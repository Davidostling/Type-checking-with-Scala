package simpret.errors

import scala.util.parsing.input.Position


trait InterpreterError
case class InputError(msg: String) extends InterpreterError
case class LexerError(loc: Location, msg: String) extends InterpreterError
case class ParserError(loc: Location, msg: String) extends InterpreterError
case class PrintingError(msg: String) extends InterpreterError
case class TypecheckingError(loc: Location, msg: String) extends InterpreterError
case class EvaluationError(loc: Location, msg: String) extends InterpreterError


case class Location(line: Int, column: Int) {
  override def toString = s"$line:$column"
}

object Location {
  def fromPos(pos: Position) = Location(pos.line, pos.column)
}
