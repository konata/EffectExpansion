package side.effect.free

import scala.collection.mutable
import scala.util.Try

import Predef.debug
import soot.jimple.*
import soot.{Unit as SootUnit, *}

// ── Value Domain ──────────────────────────────────────────────────────────────

sealed trait Primitive
sealed trait Reference

enum Types:
  case Ints(value: Int)         extends Types with Primitive
  case Doubles(value: Double)   extends Types with Primitive
  case Floats(value: Float)     extends Types with Primitive
  case Longs(value: Long)       extends Types with Primitive
  case Shorts(value: Short)     extends Types with Primitive
  case Bytes(value: Byte)       extends Types with Primitive
  case Booleans(value: Boolean) extends Types with Primitive
  case Chars(value: Char)       extends Types with Primitive
  case Arrays(value: mutable.ArrayBuffer[Types]) extends Types with Reference
  case Strings(value: String)                    extends Types with Reference
  case Objects(value: AnyRef)                    extends Types with Reference
  case Undefined                                 extends Types with Reference

// ── Execution State ───────────────────────────────────────────────────────────

case class Needle(procedure: SootMethod) {
  val instructions           = procedure.retrieveActiveBody().units
  var next: Option[SootUnit] = Option(instructions.getFirst)
  def jmp(to: SootUnit): Unit = next = Some(to)

  def advance: SootUnit = {
    val following = for {
      current <- next
      after   <- Option(instructions.getSuccOf(current))
    } yield after
    val instr = next.get
    next = following
    instr
  }
}

case class Scope(
    local: mutable.Map[Local, Types],
    upper: Option[Scope],
    method: SootMethod,
    args: Array[Types],
    receiver: Option[Types]
) {
  lazy val needle = Needle(method)

  // Resolves any Jimple leaf (Local or constant) to our type domain.
  // Composite expressions (BinopExpr etc.) go through evalValue instead.
  def resolve(v: Value): Option[Types] = v match {
    case l: Local          => local.get(l)
    case c: IntConstant    => Some(Types.Ints(c.value))
    case c: LongConstant   => Some(Types.Longs(c.value))
    case c: FloatConstant  => Some(Types.Floats(c.value))
    case c: DoubleConstant => Some(Types.Doubles(c.value))
    case c: StringConstant => Some(Types.Strings(c.value))
    case _: NullConstant   => Some(Types.Undefined)
    case _                 => None
  }
}

object Scope {
  given global: mutable.Map[String, Types] = mutable.Map()
}

// ── Value Evaluation ──────────────────────────────────────────────────────────

def evalValue(v: Value, scope: Scope): Option[Types] = v match {
  // arithmetic
  case e: AddExpr  => binArith(e, scope, _ + _, _ + _, _ + _, _ + _)
  case e: SubExpr  => binArith(e, scope, _ - _, _ - _, _ - _, _ - _)
  case e: MulExpr  => binArith(e, scope, _ * _, _ * _, _ * _, _ * _)
  case e: DivExpr  => binArith(e, scope, _ / _, _ / _, _ / _, _ / _)
  case e: RemExpr  => binArith(e, scope, _ % _, _ % _, _ % _, _ % _)
  // bitwise
  case e: AndExpr  => binBit(e, scope, _ & _, _ & _)
  case e: OrExpr   => binBit(e, scope, _ | _, _ | _)
  case e: XorExpr  => binBit(e, scope, _ ^ _, _ ^ _)
  // shifts
  case e: ShlExpr  => binShift(e, scope, _ << _, _ << _)
  case e: ShrExpr  => binShift(e, scope, _ >> _, _ >> _)
  case e: UshrExpr => binShift(e, scope, _ >>> _, _ >>> _)
  // comparisons → Int 0/1
  case e: EqExpr   => binOrd(e, scope, _ == _, _ == _, _ == _, _ == _)
  case e: NeExpr   => binOrd(e, scope, _ != _, _ != _, _ != _, _ != _)
  case e: LtExpr   => binOrd(e, scope, _ < _,  _ < _,  _ < _,  _ < _)
  case e: LeExpr   => binOrd(e, scope, _ <= _, _ <= _, _ <= _, _ <= _)
  case e: GtExpr   => binOrd(e, scope, _ > _,  _ > _,  _ > _,  _ > _)
  case e: GeExpr   => binOrd(e, scope, _ >= _, _ >= _, _ >= _, _ >= _)
  // long/float comparisons → Int -1/0/1
  case e: CmpExpr  =>
    for {
      l <- scope.resolve(e.getOp1); r <- scope.resolve(e.getOp2)
      v <- (l, r) match {
        case (Types.Longs(a), Types.Longs(b)) => Some(Types.Ints(a.compareTo(b)))
        case _                                => None
      }
    } yield v
  case e: CmpgExpr => floatCmpExpr(e, scope, nanResult =  1)
  case e: CmplExpr => floatCmpExpr(e, scope, nanResult = -1)
  // unary negation
  case e: NegExpr =>
    scope.resolve(e.getOp).flatMap {
      case Types.Ints(a)    => Some(Types.Ints(-a))
      case Types.Longs(a)   => Some(Types.Longs(-a))
      case Types.Floats(a)  => Some(Types.Floats(-a))
      case Types.Doubles(a) => Some(Types.Doubles(-a))
      case _                => None
    }
  // type casts
  case e: CastExpr => evalCast(e, scope)
  // array operations
  case e: ArrayRef =>
    for {
      i   <- scope.resolve(e.getIndex).collect { case Types.Ints(n) => n }
      arr <- scope.resolve(e.getBase).collect  { case Types.Arrays(a) => a }
      v   <- arr.lift(i)
    } yield v
  case e: NewArrayExpr =>
    val size = scope.resolve(e.getSize).collect { case Types.Ints(n) => n }.getOrElse(0)
    Some(Types.Arrays(mutable.ArrayBuffer.fill(size)(Types.Undefined)))
  case _: NewMultiArrayExpr =>
    Some(Types.Arrays(mutable.ArrayBuffer()))
  case e: LengthExpr =>
    scope.resolve(e.getOp).collect { case Types.Arrays(a) => Types.Ints(a.length) }
  // field reads via reflection
  case e: InstanceFieldRef => evalInstanceField(e, scope)
  case e: StaticFieldRef   => evalStaticField(e)
  // instanceof
  case e: InstanceOfExpr   => evalInstanceOf(e, scope)
  // leaf: Local or constant
  case other => scope.resolve(other)
}

// ── Numeric helpers ───────────────────────────────────────────────────────────

private def binArith(e: BinopExpr, scope: Scope,
    fi: (Int, Int) => Int, fl: (Long, Long) => Long,
    ff: (Float, Float) => Float, fd: (Double, Double) => Double): Option[Types] =
  for {
    l <- scope.resolve(e.getOp1); r <- scope.resolve(e.getOp2)
    v <- (l, r) match {
      case (Types.Ints(a),    Types.Ints(b))    => Some(Types.Ints(fi(a, b)))
      case (Types.Longs(a),   Types.Longs(b))   => Some(Types.Longs(fl(a, b)))
      case (Types.Floats(a),  Types.Floats(b))  => Some(Types.Floats(ff(a, b)))
      case (Types.Doubles(a), Types.Doubles(b)) => Some(Types.Doubles(fd(a, b)))
      case _                                    => None
    }
  } yield v

private def binBit(e: BinopExpr, scope: Scope,
    fi: (Int, Int) => Int, fl: (Long, Long) => Long): Option[Types] =
  for {
    l <- scope.resolve(e.getOp1); r <- scope.resolve(e.getOp2)
    v <- (l, r) match {
      case (Types.Ints(a),  Types.Ints(b))  => Some(Types.Ints(fi(a, b)))
      case (Types.Longs(a), Types.Longs(b)) => Some(Types.Longs(fl(a, b)))
      case _                                => None
    }
  } yield v

private def binShift(e: BinopExpr, scope: Scope,
    fi: (Int, Int) => Int, fl: (Long, Int) => Long): Option[Types] =
  for {
    l <- scope.resolve(e.getOp1); r <- scope.resolve(e.getOp2)
    v <- (l, r) match {
      case (Types.Ints(a),  Types.Ints(b)) => Some(Types.Ints(fi(a, b)))
      case (Types.Longs(a), Types.Ints(b)) => Some(Types.Longs(fl(a, b)))
      case _                               => None
    }
  } yield v

private def binOrd(e: BinopExpr, scope: Scope,
    fi: (Int, Int) => Boolean, fl: (Long, Long) => Boolean,
    ff: (Float, Float) => Boolean, fd: (Double, Double) => Boolean): Option[Types] =
  for {
    l <- scope.resolve(e.getOp1); r <- scope.resolve(e.getOp2)
    v <- (l, r) match {
      case (Types.Ints(a),    Types.Ints(b))    => Some(Types.Ints(if fi(a, b) then 1 else 0))
      case (Types.Longs(a),   Types.Longs(b))   => Some(Types.Ints(if fl(a, b) then 1 else 0))
      case (Types.Floats(a),  Types.Floats(b))  => Some(Types.Ints(if ff(a, b) then 1 else 0))
      case (Types.Doubles(a), Types.Doubles(b)) => Some(Types.Ints(if fd(a, b) then 1 else 0))
      case _                                    => None
    }
  } yield v

private def floatCmpExpr(e: BinopExpr, scope: Scope, nanResult: Int): Option[Types] =
  for {
    l <- scope.resolve(e.getOp1); r <- scope.resolve(e.getOp2)
    v <- (l, r) match {
      case (Types.Floats(a),  Types.Floats(b))  => Some(Types.Ints(floatCmp(a.toDouble, b.toDouble, nanResult)))
      case (Types.Doubles(a), Types.Doubles(b)) => Some(Types.Ints(floatCmp(a, b, nanResult)))
      case _                                    => None
    }
  } yield v

private def floatCmp(a: Double, b: Double, nan: Int): Int =
  if a > b then 1 else if a < b then -1 else if a == b then 0 else nan

// ── Cast ──────────────────────────────────────────────────────────────────────

private def evalCast(e: CastExpr, scope: Scope): Option[Types] =
  scope.resolve(e.getOp).flatMap { v =>
    (v, e.getCastType) match {
      // widening conversions
      case (Types.Ints(a),    _: LongType)   => Some(Types.Longs(a.toLong))
      case (Types.Ints(a),    _: FloatType)  => Some(Types.Floats(a.toFloat))
      case (Types.Ints(a),    _: DoubleType) => Some(Types.Doubles(a.toDouble))
      case (Types.Longs(a),   _: FloatType)  => Some(Types.Floats(a.toFloat))
      case (Types.Longs(a),   _: DoubleType) => Some(Types.Doubles(a.toDouble))
      case (Types.Floats(a),  _: DoubleType) => Some(Types.Doubles(a.toDouble))
      // narrowing conversions
      case (Types.Ints(a),    _: ByteType)   => Some(Types.Bytes(a.toByte))
      case (Types.Ints(a),    _: ShortType)  => Some(Types.Shorts(a.toShort))
      case (Types.Ints(a),    _: CharType)   => Some(Types.Chars(a.toChar))
      case (Types.Longs(a),   _: IntType)    => Some(Types.Ints(a.toInt))
      case (Types.Floats(a),  _: IntType)    => Some(Types.Ints(a.toInt))
      case (Types.Floats(a),  _: LongType)   => Some(Types.Longs(a.toLong))
      case (Types.Doubles(a), _: IntType)    => Some(Types.Ints(a.toInt))
      case (Types.Doubles(a), _: LongType)   => Some(Types.Longs(a.toLong))
      case (Types.Doubles(a), _: FloatType)  => Some(Types.Floats(a.toFloat))
      // reference cast: no-op in our value domain (we don't track declared type)
      case (v, _: RefType)                   => Some(v)
      // same-type or unhandled: identity
      case (v, _)                            => Some(v)
    }
  }

// ── Field reads via reflection ────────────────────────────────────────────────

private def evalInstanceField(e: InstanceFieldRef, scope: Scope): Option[Types] =
  scope.resolve(e.getBase).flatMap {
    case Types.Objects(obj) =>
      Try {
        val f = obj.getClass.getDeclaredField(e.getField.getName)
        f.setAccessible(true)
        javaToTypes(f.get(obj))
      }.toOption.flatten
    case _ => None
  }

private def evalStaticField(e: StaticFieldRef): Option[Types] =
  Try {
    val cls = Class.forName(e.getField.getDeclaringClass.getName)
    val f   = cls.getDeclaredField(e.getField.getName)
    f.setAccessible(true)
    javaToTypes(f.get(null))
  }.toOption.flatten

// Converts a Java runtime value into our type domain.
// Used by reflection-based field reads and future call results.
def javaToTypes(v: Any): Option[Types] = v match {
  case x: java.lang.Integer   => Some(Types.Ints(x.intValue))
  case x: java.lang.Long      => Some(Types.Longs(x.longValue))
  case x: java.lang.Float     => Some(Types.Floats(x.floatValue))
  case x: java.lang.Double    => Some(Types.Doubles(x.doubleValue))
  case x: java.lang.Boolean   => Some(Types.Booleans(x.booleanValue))
  case x: java.lang.Short     => Some(Types.Shorts(x.shortValue))
  case x: java.lang.Byte      => Some(Types.Bytes(x.byteValue))
  case x: java.lang.Character => Some(Types.Chars(x.charValue))
  case x: String              => Some(Types.Strings(x))
  case null                   => Some(Types.Undefined)
  case x: AnyRef              => Some(Types.Objects(x))
  case _                      => None
}

// ── instanceof ────────────────────────────────────────────────────────────────

private def evalInstanceOf(e: InstanceOfExpr, scope: Scope): Option[Types] =
  scope.resolve(e.getOp).map {
    case Types.Undefined    => Types.Ints(0) // null instanceof X == false
    case Types.Objects(obj) =>
      val name   = e.getCheckType.asInstanceOf[RefType].getSootClass.getName
      val result = Try(Class.forName(name).isInstance(obj)).getOrElse(false)
      Types.Ints(if result then 1 else 0)
    case _                  => Types.Ints(0)
  }
