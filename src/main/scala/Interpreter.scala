package side.effect.free

import Predef.*

import soot.jimple.*
import soot.Local
import soot.options.Options
import soot.{SootMethod, Unit as SootUnit}

import scala.collection.mutable

object Interpreter {

  def bootstrap(options: Options, entry: SootMethod, args: Array[Types], receiver: Option[Types]): Unit = {
    debug("bootstrap", s"starting vm: $options")
    interpret(entry, args, receiver)
  }

  def interpret(entry: SootMethod, args: Array[Types], receiver: Option[Types]): Unit = {
    val scope  = Scope(mutable.Map(), None, entry, args, receiver)
    val needle = scope.needle
    debug("interpret", s"method: $entry")
    while (needle.next.isDefined) {
      val instr = needle.advance
      debug("interpret", s"step: $instr")
      step(instr, scope)
    }
  }

  private def step(instr: SootUnit, scope: Scope): Scope = instr match {
    case s: AssignStmt =>
      s.getLeftOp match {
        case lhs: ArrayRef =>
          for {
            i   <- scope.resolve(lhs.getIndex).collect { case Types.Ints(n) => n }
            arr <- scope.resolve(lhs.getBase).collect  { case Types.Arrays(a) => a }
            v   <- evalValue(s.getRightOp, scope)
          } arr(i) = v
        case lhs: Local =>
          evalValue(s.getRightOp, scope).foreach(scope.local(lhs) = _)
        case lhs =>
          debug("step", s"unhandled assign lhs: $lhs")
      }
      scope
    case s: IdentityStmt =>
      val lhs = s.getLeftOp.asInstanceOf[Local]
      s.getRightOp match {
        case _: ThisRef      => scope.receiver.foreach(scope.local(lhs) = _)
        case r: ParameterRef => if r.getIndex < scope.args.length then scope.local(lhs) = scope.args(r.getIndex)
        case _               => ()
      }
      scope
    case s: GotoStmt =>
      scope.needle.jmp(s.getTarget)
      scope
    case s: IfStmt =>
      evalValue(s.getCondition, scope) match {
        case Some(Types.Ints(n)) if n != 0 => scope.needle.jmp(s.getTarget)
        case _                             => ()
      }
      scope
    case _: NopStmt        => scope
    case _: ReturnVoidStmt => scope
    case s =>
      debug("step", s"unimplemented: $s")
      scope
  }
}
