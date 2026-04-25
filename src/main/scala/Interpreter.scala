package side.effect.free

import Predef.*
import Wrappers.{SAssignStmt, SLocal}

import soot.jimple.*
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
      val SAssignStmt(left @ SLocal(_, _), right) = s: @unchecked
      evalValue(right, scope).foreach(scope.local(left) = _)
      scope
    case _: NopStmt        => scope
    case _: ReturnVoidStmt => scope
    case s =>
      debug("step", s"unimplemented: $s")
      scope
  }
}
