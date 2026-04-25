package side.effect.free

import scala.collection.mutable

import Predef.debug
import soot.jimple.*
import soot.{Local, SootMethod, Value, Unit as SootUnit}

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
  case Arrays(value: mutable.Seq[Types]) extends Types with Reference
  case Strings(value: String)            extends Types with Reference
  case Objects(value: AnyRef)            extends Types with Reference
  case Undefined                         extends Types with Reference

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
  case e: AddExpr  => binArith(e, scope, _ + _, _ + _, _ + _, _ + _)
  case e: SubExpr  => binArith(e, scope, _ - _, _ - _, _ - _, _ - _)
  case e: MulExpr  => binArith(e, scope, _ * _, _ * _, _ * _, _ * _)
  case e: DivExpr  => binArith(e, scope, _ / _, _ / _, _ / _, _ / _)
  case e: RemExpr  => binArith(e, scope, _ % _, _ % _, _ % _, _ % _)
  case e: AndExpr  => binBit(e, scope, _ & _, _ & _)
  case e: OrExpr   => binBit(e, scope, _ | _, _ | _)
  case e: XorExpr  => binBit(e, scope, _ ^ _, _ ^ _)
  case e: ShlExpr  => binShift(e, scope, _ << _, _ << _)
  case e: ShrExpr  => binShift(e, scope, _ >> _, _ >> _)
  case e: UshrExpr => binShift(e, scope, _ >>> _, _ >>> _)
  case e: EqExpr   => binOrd(e, scope, _ == _, _ == _, _ == _, _ == _)
  case e: NeExpr   => binOrd(e, scope, _ != _, _ != _, _ != _, _ != _)
  case e: LtExpr   => binOrd(e, scope, _ < _,  _ < _,  _ < _,  _ < _)
  case e: LeExpr   => binOrd(e, scope, _ <= _, _ <= _, _ <= _, _ <= _)
  case e: GtExpr   => binOrd(e, scope, _ > _,  _ > _,  _ > _,  _ > _)
  case e: GeExpr   => binOrd(e, scope, _ >= _, _ >= _, _ >= _, _ >= _)
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
  case e: NegExpr  =>
    scope.resolve(e.getOp).flatMap {
      case Types.Ints(a)    => Some(Types.Ints(-a))
      case Types.Longs(a)   => Some(Types.Longs(-a))
      case Types.Floats(a)  => Some(Types.Floats(-a))
      case Types.Doubles(a) => Some(Types.Doubles(-a))
      case _                => None
    }
  case e: ArrayRef =>
    for {
      i   <- scope.resolve(e.getIndex).collect { case Types.Ints(n) => n }
      arr <- scope.resolve(e.getBase).collect  { case Types.Arrays(a) => a }
      v   <- arr.lift(i)
    } yield v
  case _: NewArrayExpr | _: NewMultiArrayExpr =>
    Some(Types.Arrays(mutable.Seq()))
  case other => scope.resolve(other)
}

// ── Helpers ───────────────────────────────────────────────────────────────────

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
