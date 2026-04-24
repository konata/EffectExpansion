package side.effect.free

import Predef.*
import Wrappers.RichChain

import soot.options.Options
import soot.{SootMethod, Unit as SootUnit}

import scala.collection.mutable

object Interpreter {

  def bootstrap(options: Options, entry: SootMethod, args: Array[Types], receiver: Option[Types]): Unit = {
    debug("bootstrap", s"starting vm: $options")
    interpret(entry, args, receiver)
  }

  def interpret(entry: SootMethod, args: Array[Types], receiver: Option[Types]): Unit = {
    val zygote   = Scope(mutable.Map(), None, entry, args, receiver)
    val prologue = zygote.needle
    debug("interpret", s"starting vm: $prologue")
    while (prologue.next.isDefined) {
      val instruction = prologue.advance
      debug("interpret", s"running instruction: $instruction")
      interpret(instruction, zygote)
    }
  }

  def interpret(instruction: SootUnit, scope: Scope): Unit =
    instruction match {
      case statement: StatementSyntax => statement.eval(scope)
      case _                          => raise("interpret", s"invalid unit: $instruction")
    }
}
