package simpret

import simpret.errors._
import simpret.lexer._
import simpret.parser._
import simpret.typechecker._
import simpret.interpreter._


// Potentially helpful links:
//
//https://www.jetbrains.com/help/idea/sbt.html
//https://blog.jetbrains.com/scala/2017/03/23/scala-plugin-for-intellij-idea-2017-1-cleaner-ui-sbt-shell-repl-worksheet-akka-support-and-more/
//https://www.jetbrains.com/help/idea/run-debug-and-test-scala.html
//http://uclmr.github.io/stat-nlp-book-scala/05_tutorial/01_intro_to_scala_part1.html


// ~run src/input.sint
object Main {
  def main(args: Array[String]) = {
    if (args.length < 1) {
      println("usage:   java simpret.jar {filename} [options]")
      println("example: java simpret.jar src/input.sint")
    } else {
      val filename = args(0) // e.g., "src/input.sint"

      apply(filename) match {
        case Left(InputError(msg)) => println("INPUT ERROR: " + msg)
        case Left(LexerError(loc, msg)) => println(s"LEXER ERROR at ($loc): " + msg)
        case Left(ParserError(loc, msg)) => println(s"PARSER ERROR at ($loc): " + msg)
        case Left(PrintingError(msg)) => println("PRINTER ERROR: " + msg)
        case Left(TypecheckingError(loc, msg)) => println(s"TYPECHECKER ERROR at ($loc): " + msg)
        case Left(EvaluationError(loc, msg)) => println(s"EVALUATION ERROR at ($loc): " + msg)
        case Left(_) => println("!! unknown error type !!")
        case Right(x) => {
          x match {
            case _ if Interpreter.isvalue(x) => {
              println("Result: " + ASTPrinter.convToStr(x))
              println("==================")
            }
            case _ => {
              println("Evaluation stuck!")
              println("Stuck at")
              println("==================")
              println(ASTPrinter.convToStr(x))
              println("==================")
            }
          }
        }
      }
    }
  }

  def apply(filename: String): Either[InterpreterError, AST] = {
    for {
      input <- FileLoader(filename).right
      tokens <- Lexer(input).right
      ast <- Parser(tokens).right
      _ <- ASTPrinter(ast).right
      _ <- Typechecker(ast).right
      res <- Interpreter(ast).right
    } yield res
  }
}
