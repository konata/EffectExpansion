package side.effect.free

import scala.language.implicitConversions
import scala.collection.mutable

import Predef.{debug, raise}
import Wrappers.{SAssignStmt, SLocal}

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

  // Resolves any Jimple leaf value (Local or constant) to our type domain.
  // BinopExpr / UnopExpr are NOT leaves — use evalValue for those.
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

// ── Syntax ────────────────────────────────────────────────────────────────────

trait Syntax

sealed trait StatementSyntax extends Syntax:
  def eval(scope: Scope): Scope = ???

sealed trait ValueSyntax extends Syntax:
  def eval(scope: Scope): (Option[Types], Scope) = ???

sealed trait ScalarSyntaxes  extends ValueSyntax
sealed trait MiscSyntax      extends ValueSyntax
sealed trait ConstantsSyntax extends ValueSyntax
sealed trait InvokeSyntax    extends ValueSyntax

// ── Statement Syntax ──────────────────────────────────────────────────────────

object StatementSyntax {

  class BreakPoint(val expr: BreakpointStmt)     extends StatementSyntax
  class Invoke(val expr: InvokeExpr)             extends StatementSyntax
  class Identity(val expr: IdentityStmt)         extends StatementSyntax
  class EnterMonitor(val expr: EnterMonitorStmt) extends StatementSyntax
  class ExitMonitor(val expr: ExitMonitorStmt)   extends StatementSyntax
  class Goto(val expr: GotoStmt)                 extends StatementSyntax
  class If(val expr: IfStmt)                     extends StatementSyntax
  class LookUpSwitch(val expr: LookupSwitchStmt) extends StatementSyntax
  class TableSwitch(val expr: TableSwitchStmt)   extends StatementSyntax
  class Nop(val expr: NopStmt)                   extends StatementSyntax
  class Return(val expr: ReturnStmt)             extends StatementSyntax
  class ReturnVoid(val expr: ReturnVoidStmt)     extends StatementSyntax
  class Throw(val expr: ThrowStmt)               extends StatementSyntax

  class Assign(val expr: AssignStmt) extends StatementSyntax {
    override def eval(scope: Scope) = {
      val SAssignStmt(left @ SLocal(_, _), right) = expr: @unchecked
      evalValue(right, scope).foreach(scope.local(left) = _)
      scope
    }
  }

  given Conversion[BreakpointStmt, BreakPoint]       = BreakPoint(_)
  given Conversion[InvokeExpr, Invoke]               = Invoke(_)
  given Conversion[AssignStmt, Assign]               = Assign(_)
  given Conversion[IdentityStmt, Identity]           = Identity(_)
  given Conversion[EnterMonitorStmt, EnterMonitor]   = EnterMonitor(_)
  given Conversion[ExitMonitorStmt, ExitMonitor]     = ExitMonitor(_)
  given Conversion[GotoStmt, Goto]                   = Goto(_)
  given Conversion[IfStmt, If]                       = If(_)
  given Conversion[LookupSwitchStmt, LookUpSwitch]   = LookUpSwitch(_)
  given Conversion[TableSwitchStmt, TableSwitch]     = TableSwitch(_)
  given Conversion[NopStmt, Nop]                     = Nop(_)
  given Conversion[ReturnStmt, Return]               = Return(_)
  given Conversion[ReturnVoidStmt, ReturnVoid]       = ReturnVoid(_)
  given Conversion[ThrowStmt, Throw]                 = Throw(_)
}

// ── Misc Syntax ───────────────────────────────────────────────────────────────

object MiscSyntax {

  class ArrayReference(val expr: ArrayRef) extends MiscSyntax {
    override def eval(scope: Scope) = {
      val ArrayReference(base @ SLocal(_, _), index, _) = expr: @unchecked
      val immediate = for {
        i     <- scope.resolve(index).collect { case Types.Ints(n) => n }
        arr   <- scope.resolve(base).collect { case Types.Arrays(a) => a }
        value <- arr.lift(i)
      } yield value
      debug("ArrayReference", s"$base($index) == $immediate")
      immediate -> scope
    }
  }

  object ArrayReference {
    def unapply(arg: ArrayRef) = Some(arg.getBase, arg.getIndex, arg.getType)
  }

  class NewArrayExpression(val expr: NewArrayExpr) extends MiscSyntax {
    override def eval(scope: Scope) = {
      debug("NewArrayExpression", s"type:${expr.getType} size:${expr.getSize}")
      Some(Types.Arrays(mutable.Seq())) -> scope
    }
  }

  class NewMultiArrayExpression(val expr: NewMultiArrayExpr) extends MiscSyntax {
    override def eval(scope: Scope) = {
      debug("NewMultiArrayExpression", s"type:${expr.getType} sizes:${expr.getSizes}")
      Some(Types.Arrays(mutable.Seq())) -> scope
    }
  }

  class NewExpression(val expr: NewExpr)                       extends MiscSyntax
  class ArrayLengthExpression(val expr: LengthExpr)            extends MiscSyntax
  class InstanceFieldReference(val expr: InstanceFieldRef)     extends MiscSyntax
  class LocalReference(val expr: Local)                        extends MiscSyntax
  class ParameterReference(val expr: ParameterRef)             extends MiscSyntax
  class CaughtExceptionReference(val expr: CaughtExceptionRef) extends MiscSyntax
  class ThisReference(val expr: ThisRef)                       extends MiscSyntax
  class StaticFieldReference(val expr: StaticFieldRef)         extends MiscSyntax
  class InstanceOfExpression(val expr: InstanceOfExpr)         extends MiscSyntax

  given Conversion[ArrayRef, ArrayReference]                     = ArrayReference(_)
  given Conversion[NewArrayExpr, NewArrayExpression]             = NewArrayExpression(_)
  given Conversion[NewMultiArrayExpr, NewMultiArrayExpression]   = NewMultiArrayExpression(_)
  given Conversion[NewExpr, NewExpression]                       = NewExpression(_)
  given Conversion[LengthExpr, ArrayLengthExpression]            = ArrayLengthExpression(_)
  given Conversion[InstanceFieldRef, InstanceFieldReference]     = InstanceFieldReference(_)
  given Conversion[Local, LocalReference]                        = LocalReference(_)
  given Conversion[ParameterRef, ParameterReference]             = ParameterReference(_)
  given Conversion[CaughtExceptionRef, CaughtExceptionReference] = CaughtExceptionReference(_)
  given Conversion[ThisRef, ThisReference]                       = ThisReference(_)
  given Conversion[StaticFieldRef, StaticFieldReference]         = StaticFieldReference(_)
  given Conversion[InstanceOfExpr, InstanceOfExpression]         = InstanceOfExpression(_)
}

// ── Constants Syntax ──────────────────────────────────────────────────────────

object ConstantsSyntax {
  class ApplyDoubles(val expr: DoubleConstant)     extends ConstantsSyntax
  class ApplyLongs(val expr: LongConstant)         extends ConstantsSyntax
  class ApplyInts(val expr: IntConstant)           extends ConstantsSyntax
  class ApplyFloats(val expr: FloatConstant)       extends ConstantsSyntax
  class ApplyNulls(val expr: NullConstant)         extends ConstantsSyntax
  class ApplyStrings(val expr: StringConstant)     extends ConstantsSyntax
  class ApplyClasses(val expr: ClassConstant)      extends ConstantsSyntax
  class ApplyMethodHandles(val expr: MethodHandle) extends ConstantsSyntax

  given Conversion[DoubleConstant, ApplyDoubles]     = ApplyDoubles(_)
  given Conversion[LongConstant, ApplyLongs]         = ApplyLongs(_)
  given Conversion[IntConstant, ApplyInts]           = ApplyInts(_)
  given Conversion[FloatConstant, ApplyFloats]       = ApplyFloats(_)
  given Conversion[NullConstant, ApplyNulls]         = ApplyNulls(_)
  given Conversion[StringConstant, ApplyStrings]     = ApplyStrings(_)
  given Conversion[ClassConstant, ApplyClasses]      = ApplyClasses(_)
  given Conversion[MethodHandle, ApplyMethodHandles] = ApplyMethodHandles(_)
}

// ── Invoke Syntax ─────────────────────────────────────────────────────────────

object InvokeSyntax {
  class InterfaceInvoke(val expr: InterfaceInvokeExpr) extends InvokeSyntax
  class StaticInvoke(val expr: StaticInvokeExpr)       extends InvokeSyntax
  class SpecialInvoke(val expr: SpecialInvokeExpr)     extends InvokeSyntax
  class VirtualInvoke(val expr: VirtualInvokeExpr)     extends InvokeSyntax
  class InstanceInvoke(val expr: InstanceInvokeExpr)   extends InvokeSyntax
  class DynamicInvoke(val expr: DynamicInvokeExpr)     extends InvokeSyntax

  given Conversion[InterfaceInvokeExpr, InterfaceInvoke] = InterfaceInvoke(_)
  given Conversion[StaticInvokeExpr, StaticInvoke]       = StaticInvoke(_)
  given Conversion[SpecialInvokeExpr, SpecialInvoke]     = SpecialInvoke(_)
  given Conversion[VirtualInvokeExpr, VirtualInvoke]     = VirtualInvoke(_)
  given Conversion[InstanceInvokeExpr, InstanceInvoke]   = InstanceInvoke(_)
  given Conversion[DynamicInvokeExpr, DynamicInvoke]     = DynamicInvoke(_)
}

// ── Scalar Syntaxes ───────────────────────────────────────────────────────────

object ScalarSyntaxes {

  object Bin {
    def unapply(arg: BinopExpr): Option[(Value, Value)] = Some(arg.getOp1, arg.getOp2)
  }

  // ── helpers ────────────────────────────────────────────────────────────────

  private def arith(l: Types, r: Types,
      fi: (Int, Int) => Int, fl: (Long, Long) => Long,
      ff: (Float, Float) => Float, fd: (Double, Double) => Double): Option[Types] =
    (l, r) match {
      case (Types.Ints(a),    Types.Ints(b))    => Some(Types.Ints(fi(a, b)))
      case (Types.Longs(a),   Types.Longs(b))   => Some(Types.Longs(fl(a, b)))
      case (Types.Floats(a),  Types.Floats(b))  => Some(Types.Floats(ff(a, b)))
      case (Types.Doubles(a), Types.Doubles(b)) => Some(Types.Doubles(fd(a, b)))
      case _                                    => None
    }

  // integer-only: And / Or / Xor
  private def bitwise(l: Types, r: Types,
      fi: (Int, Int) => Int, fl: (Long, Long) => Long): Option[Types] =
    (l, r) match {
      case (Types.Ints(a),  Types.Ints(b))  => Some(Types.Ints(fi(a, b)))
      case (Types.Longs(a), Types.Longs(b)) => Some(Types.Longs(fl(a, b)))
      case _                                => None
    }

  // shift: right operand is always Int in the JVM spec
  private def shift(l: Types, r: Types,
      fi: (Int, Int) => Int, fl: (Long, Int) => Long): Option[Types] =
    (l, r) match {
      case (Types.Ints(a),  Types.Ints(b)) => Some(Types.Ints(fi(a, b)))
      case (Types.Longs(a), Types.Ints(b)) => Some(Types.Longs(fl(a, b)))
      case _                               => None
    }

  // Eq / Ne / Lt / Le / Gt / Ge → returns Int 0 or 1
  private def ordering(l: Types, r: Types,
      fi: (Int, Int) => Boolean, fl: (Long, Long) => Boolean,
      ff: (Float, Float) => Boolean, fd: (Double, Double) => Boolean): Option[Types] =
    (l, r) match {
      case (Types.Ints(a),    Types.Ints(b))    => Some(Types.Ints(if fi(a, b) then 1 else 0))
      case (Types.Longs(a),   Types.Longs(b))   => Some(Types.Ints(if fl(a, b) then 1 else 0))
      case (Types.Floats(a),  Types.Floats(b))  => Some(Types.Ints(if ff(a, b) then 1 else 0))
      case (Types.Doubles(a), Types.Doubles(b)) => Some(Types.Ints(if fd(a, b) then 1 else 0))
      case _                                    => None
    }

  // ── classes ────────────────────────────────────────────────────────────────

  class Add(val e: AddExpr) extends ScalarSyntaxes {
    override def eval(scope: Scope) =
      (for { l <- scope.resolve(e.getOp1); r <- scope.resolve(e.getOp2); v <- arith(l, r, _ + _, _ + _, _ + _, _ + _) } yield v) -> scope
  }

  class Sub(val e: SubExpr) extends ScalarSyntaxes {
    override def eval(scope: Scope) =
      (for { l <- scope.resolve(e.getOp1); r <- scope.resolve(e.getOp2); v <- arith(l, r, _ - _, _ - _, _ - _, _ - _) } yield v) -> scope
  }

  class Mul(val e: MulExpr) extends ScalarSyntaxes {
    override def eval(scope: Scope) =
      (for { l <- scope.resolve(e.getOp1); r <- scope.resolve(e.getOp2); v <- arith(l, r, _ * _, _ * _, _ * _, _ * _) } yield v) -> scope
  }

  class Div(val e: DivExpr) extends ScalarSyntaxes {
    override def eval(scope: Scope) =
      (for { l <- scope.resolve(e.getOp1); r <- scope.resolve(e.getOp2); v <- arith(l, r, _ / _, _ / _, _ / _, _ / _) } yield v) -> scope
  }

  class Rem(val e: RemExpr) extends ScalarSyntaxes {
    override def eval(scope: Scope) =
      (for { l <- scope.resolve(e.getOp1); r <- scope.resolve(e.getOp2); v <- arith(l, r, _ % _, _ % _, _ % _, _ % _) } yield v) -> scope
  }

  class And(val e: AndExpr) extends ScalarSyntaxes {
    override def eval(scope: Scope) =
      (for { l <- scope.resolve(e.getOp1); r <- scope.resolve(e.getOp2); v <- bitwise(l, r, _ & _, _ & _) } yield v) -> scope
  }

  class Or(val e: OrExpr) extends ScalarSyntaxes {
    override def eval(scope: Scope) =
      (for { l <- scope.resolve(e.getOp1); r <- scope.resolve(e.getOp2); v <- bitwise(l, r, _ | _, _ | _) } yield v) -> scope
  }

  class Xor(val e: XorExpr) extends ScalarSyntaxes {
    override def eval(scope: Scope) =
      (for { l <- scope.resolve(e.getOp1); r <- scope.resolve(e.getOp2); v <- bitwise(l, r, _ ^ _, _ ^ _) } yield v) -> scope
  }

  class Shl(val e: ShlExpr) extends ScalarSyntaxes {
    override def eval(scope: Scope) =
      (for { l <- scope.resolve(e.getOp1); r <- scope.resolve(e.getOp2); v <- shift(l, r, _ << _, _ << _) } yield v) -> scope
  }

  class Shr(val e: ShrExpr) extends ScalarSyntaxes {
    override def eval(scope: Scope) =
      (for { l <- scope.resolve(e.getOp1); r <- scope.resolve(e.getOp2); v <- shift(l, r, _ >> _, _ >> _) } yield v) -> scope
  }

  class Ushr(val e: UshrExpr) extends ScalarSyntaxes {
    override def eval(scope: Scope) =
      (for { l <- scope.resolve(e.getOp1); r <- scope.resolve(e.getOp2); v <- shift(l, r, _ >>> _, _ >>> _) } yield v) -> scope
  }

  class Eq(val e: EqExpr) extends ScalarSyntaxes {
    override def eval(scope: Scope) =
      (for { l <- scope.resolve(e.getOp1); r <- scope.resolve(e.getOp2); v <- ordering(l, r, _ == _, _ == _, _ == _, _ == _) } yield v) -> scope
  }

  class Ne(val e: NeExpr) extends ScalarSyntaxes {
    override def eval(scope: Scope) =
      (for { l <- scope.resolve(e.getOp1); r <- scope.resolve(e.getOp2); v <- ordering(l, r, _ != _, _ != _, _ != _, _ != _) } yield v) -> scope
  }

  class Lt(val e: LtExpr) extends ScalarSyntaxes {
    override def eval(scope: Scope) =
      (for { l <- scope.resolve(e.getOp1); r <- scope.resolve(e.getOp2); v <- ordering(l, r, _ < _, _ < _, _ < _, _ < _) } yield v) -> scope
  }

  class Le(val e: LeExpr) extends ScalarSyntaxes {
    override def eval(scope: Scope) =
      (for { l <- scope.resolve(e.getOp1); r <- scope.resolve(e.getOp2); v <- ordering(l, r, _ <= _, _ <= _, _ <= _, _ <= _) } yield v) -> scope
  }

  class Gt(val e: GtExpr) extends ScalarSyntaxes {
    override def eval(scope: Scope) =
      (for { l <- scope.resolve(e.getOp1); r <- scope.resolve(e.getOp2); v <- ordering(l, r, _ > _, _ > _, _ > _, _ > _) } yield v) -> scope
  }

  class Ge(val e: GeExpr) extends ScalarSyntaxes {
    override def eval(scope: Scope) =
      (for { l <- scope.resolve(e.getOp1); r <- scope.resolve(e.getOp2); v <- ordering(l, r, _ >= _, _ >= _, _ >= _, _ >= _) } yield v) -> scope
  }

  // long comparison: returns -1 / 0 / 1
  class Cmp(val e: CmpExpr) extends ScalarSyntaxes {
    override def eval(scope: Scope) = {
      val result = for {
        l <- scope.resolve(e.getOp1); r <- scope.resolve(e.getOp2)
      } yield (l, r) match {
        case (Types.Longs(a), Types.Longs(b)) => Some(Types.Ints(a.compareTo(b)))
        case _                                => None
      }
      result.flatten -> scope
    }
  }

  // float/double comparison: NaN → +1
  class Cmpg(val e: CmpgExpr) extends ScalarSyntaxes {
    override def eval(scope: Scope) = {
      val result = for {
        l <- scope.resolve(e.getOp1); r <- scope.resolve(e.getOp2)
      } yield (l, r) match {
        case (Types.Floats(a),  Types.Floats(b))  => Some(Types.Ints(floatCmp(a, b, nanResult = 1)))
        case (Types.Doubles(a), Types.Doubles(b)) => Some(Types.Ints(doubleCmp(a, b, nanResult = 1)))
        case _                                    => None
      }
      result.flatten -> scope
    }
  }

  // float/double comparison: NaN → -1
  class Cmpl(val e: CmplExpr) extends ScalarSyntaxes {
    override def eval(scope: Scope) = {
      val result = for {
        l <- scope.resolve(e.getOp1); r <- scope.resolve(e.getOp2)
      } yield (l, r) match {
        case (Types.Floats(a),  Types.Floats(b))  => Some(Types.Ints(floatCmp(a, b, nanResult = -1)))
        case (Types.Doubles(a), Types.Doubles(b)) => Some(Types.Ints(doubleCmp(a, b, nanResult = -1)))
        case _                                    => None
      }
      result.flatten -> scope
    }
  }

  class Neg(val e: NegExpr) extends ScalarSyntaxes {
    override def eval(scope: Scope) = {
      val result = scope.resolve(e.getOp).map {
        case Types.Ints(a)    => Types.Ints(-a)
        case Types.Longs(a)   => Types.Longs(-a)
        case Types.Floats(a)  => Types.Floats(-a)
        case Types.Doubles(a) => Types.Doubles(-a)
        case other            => other
      }
      result -> scope
    }
  }

  private def floatCmp(a: Float, b: Float, nanResult: Int): Int =
    if a > b then 1 else if a < b then -1 else if a == b then 0 else nanResult

  private def doubleCmp(a: Double, b: Double, nanResult: Int): Int =
    if a > b then 1 else if a < b then -1 else if a == b then 0 else nanResult

  given Conversion[AddExpr, Add]    = Add(_)
  given Conversion[SubExpr, Sub]    = Sub(_)
  given Conversion[MulExpr, Mul]    = Mul(_)
  given Conversion[DivExpr, Div]    = Div(_)
  given Conversion[RemExpr, Rem]    = Rem(_)
  given Conversion[AndExpr, And]    = And(_)
  given Conversion[OrExpr, Or]      = Or(_)
  given Conversion[XorExpr, Xor]    = Xor(_)
  given Conversion[ShlExpr, Shl]    = Shl(_)
  given Conversion[ShrExpr, Shr]    = Shr(_)
  given Conversion[UshrExpr, Ushr]  = Ushr(_)
  given Conversion[EqExpr, Eq]      = Eq(_)
  given Conversion[NeExpr, Ne]      = Ne(_)
  given Conversion[LtExpr, Lt]      = Lt(_)
  given Conversion[LeExpr, Le]      = Le(_)
  given Conversion[GtExpr, Gt]      = Gt(_)
  given Conversion[GeExpr, Ge]      = Ge(_)
  given Conversion[CmpExpr, Cmp]    = Cmp(_)
  given Conversion[CmpgExpr, Cmpg]  = Cmpg(_)
  given Conversion[CmplExpr, Cmpl]  = Cmpl(_)
  given Conversion[NegExpr, Neg]    = Neg(_)
}

// ── Value dispatch ────────────────────────────────────────────────────────────
// pattern match on Soot IR types → no implicit conversion needed here

def evalValue(v: Value, scope: Scope): Option[Types] = v match {
  case e: AddExpr  => ScalarSyntaxes.Add(e).eval(scope)._1
  case e: SubExpr  => ScalarSyntaxes.Sub(e).eval(scope)._1
  case e: MulExpr  => ScalarSyntaxes.Mul(e).eval(scope)._1
  case e: DivExpr  => ScalarSyntaxes.Div(e).eval(scope)._1
  case e: RemExpr  => ScalarSyntaxes.Rem(e).eval(scope)._1
  case e: AndExpr  => ScalarSyntaxes.And(e).eval(scope)._1
  case e: OrExpr   => ScalarSyntaxes.Or(e).eval(scope)._1
  case e: XorExpr  => ScalarSyntaxes.Xor(e).eval(scope)._1
  case e: ShlExpr  => ScalarSyntaxes.Shl(e).eval(scope)._1
  case e: ShrExpr  => ScalarSyntaxes.Shr(e).eval(scope)._1
  case e: UshrExpr => ScalarSyntaxes.Ushr(e).eval(scope)._1
  case e: EqExpr   => ScalarSyntaxes.Eq(e).eval(scope)._1
  case e: NeExpr   => ScalarSyntaxes.Ne(e).eval(scope)._1
  case e: LtExpr   => ScalarSyntaxes.Lt(e).eval(scope)._1
  case e: LeExpr   => ScalarSyntaxes.Le(e).eval(scope)._1
  case e: GtExpr   => ScalarSyntaxes.Gt(e).eval(scope)._1
  case e: GeExpr   => ScalarSyntaxes.Ge(e).eval(scope)._1
  case e: CmpExpr  => ScalarSyntaxes.Cmp(e).eval(scope)._1
  case e: CmpgExpr => ScalarSyntaxes.Cmpg(e).eval(scope)._1
  case e: CmplExpr => ScalarSyntaxes.Cmpl(e).eval(scope)._1
  case e: NegExpr  => ScalarSyntaxes.Neg(e).eval(scope)._1
  case e: ArrayRef => MiscSyntax.ArrayReference(e).eval(scope)._1
  case other       => scope.resolve(other)
}
