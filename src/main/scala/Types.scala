package side.effect.free

import scala.language.implicitConversions
import scala.collection.mutable
import scala.util.control.Exception.catching

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
  val needle = Needle(method)
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
      val (resolved, _) = right match {
        case value: ValueSyntax => value.eval(scope)
        case _                  => raise("Assign.eval", s"invalid value type: $right")
      }
      resolved.foreach(scope.local(left) = _)
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
        i <- index match {
          case v @ SLocal(_, _) => catching(classOf[Throwable]) opt scope.local(v).asInstanceOf[Types.Ints].value
          case v: IntConstant   => Some(v.value)
        }
        value <- catching(classOf[Throwable]) opt scope.local(base).asInstanceOf[Types.Arrays].value(i)
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

  class Add(val add: AddExpr)    extends ScalarSyntaxes
  class Sub(val sub: SubExpr)    extends ScalarSyntaxes
  class Mul(val mul: MulExpr)    extends ScalarSyntaxes
  class Div(val div: DivExpr)    extends ScalarSyntaxes
  class And(val and: AndExpr)    extends ScalarSyntaxes
  class Cmp(val cmp: CmpExpr)    extends ScalarSyntaxes
  class Cmpg(val cmpg: CmpgExpr) extends ScalarSyntaxes
  class Eq(val eq: EqExpr)       extends ScalarSyntaxes
  class Ge(val ge: GeExpr)       extends ScalarSyntaxes
  class Gt(val gt: GtExpr)       extends ScalarSyntaxes
  class Lt(val lt: LtExpr)       extends ScalarSyntaxes
  class Le(val le: LeExpr)       extends ScalarSyntaxes
  class Ne(val ne: NeExpr)       extends ScalarSyntaxes
  class Rem(val rem: RemExpr)    extends ScalarSyntaxes
  class Shl(val shl: ShlExpr)    extends ScalarSyntaxes
  class Shr(val shr: ShrExpr)    extends ScalarSyntaxes
  class Ushr(val ushr: UshrExpr) extends ScalarSyntaxes
  class Xor(val xor: XorExpr)    extends ScalarSyntaxes
  class Neg(val neg: NegExpr)    extends ScalarSyntaxes

  given Conversion[AddExpr, Add]    = Add(_)
  given Conversion[SubExpr, Sub]    = Sub(_)
  given Conversion[MulExpr, Mul]    = Mul(_)
  given Conversion[DivExpr, Div]    = Div(_)
  given Conversion[AndExpr, And]    = And(_)
  given Conversion[CmpExpr, Cmp]    = Cmp(_)
  given Conversion[CmpgExpr, Cmpg]  = Cmpg(_)
  given Conversion[EqExpr, Eq]      = Eq(_)
  given Conversion[GeExpr, Ge]      = Ge(_)
  given Conversion[GtExpr, Gt]      = Gt(_)
  given Conversion[LtExpr, Lt]      = Lt(_)
  given Conversion[LeExpr, Le]      = Le(_)
  given Conversion[NeExpr, Ne]      = Ne(_)
  given Conversion[RemExpr, Rem]    = Rem(_)
  given Conversion[ShlExpr, Shl]    = Shl(_)
  given Conversion[ShrExpr, Shr]    = Shr(_)
  given Conversion[UshrExpr, Ushr]  = Ushr(_)
  given Conversion[XorExpr, Xor]    = Xor(_)
  given Conversion[NegExpr, Neg]    = Neg(_)
}
