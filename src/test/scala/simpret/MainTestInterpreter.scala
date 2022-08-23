package simpret


import simpret.lexer._
import simpret.parser._
import simpret.errors._
import simpret.interpreter._
import simpret.typechecker._
import org.scalatest.funsuite.AnyFunSuite
import java.io.File


class MainTestInterpreter extends AnyFunSuite {

  def test_eval(filename: String, expected_result: Either[InterpreterError, AST]): Unit = {
    assert(runcase(filename) === expected_result)
  }

  def test_eval_text(filename: String, expected_sint: String): Unit = {
    val expected_result = parse(expected_sint) match {
      case Left(err) => throw new Exception("parsing of test case failed")
      case result => result
    }
    assert(runcase(filename) === expected_result)
  }

  def test_var_capture(filename: String, expected_var_id: String, expected_expr: AST): Unit = {
    try {
      runcase(filename)
      assert(false)
    } catch {
      case ex : VariableCapturedEvaluationException =>
        val var_id = ex.var_id
        val x = ex.subst_s
        assert(expected_var_id === var_id)
        assert(expected_expr === x)
    }
  }

  def getListOfFiles(dir: String, extensions: List[String]): List[File] = {
      new File(dir).listFiles.filter(_.isFile).toList.filter { file =>
          extensions.exists(file.getName.endsWith(_))
      }
  }

  def parse(input: String): Either[InterpreterError, AST] = {
    for {
      tokens <- Lexer(input).right
      ast <- Parser(tokens).right
    } yield ast
  }


  def loadAst(filename: String): Either[InterpreterError, AST] = {
    for {
      input <- FileLoader(filename).right
      tokens <- Lexer(input).right
      ast <- Parser(tokens).right
    } yield ast
  }

  def singleAutoTest(in: File) = {
    var inFilename = in.getAbsolutePath()
    var stepFilename = inFilename + ".step"

    (loadAst(inFilename), loadAst(stepFilename)) match {
      case (Right(inAst), Right(stepAst)) => {
        Typechecker(inAst) match {
          case Left(error) => assert(false, error)
          case _ => None
        }

        Typechecker(stepAst) match {
          case Left(error) => assert(false, error)
          case _ => None
        }

        assert(Interpreter.step(inAst) === Some(stepAst))
      }
      case (Left(error), _) => assert(false, error)
      case (_, Left(error)) => assert(false, error)
    }
  }

  def singleAutoTypeTest(in: File): Unit = {
    var inFilename = in.getAbsolutePath()
    loadAst(inFilename) match {
      case Right(ast) => assert(Typechecker(ast).isLeft, ", but it should not be typable")
      case Left(error) => assert(false, error)
    }
  }

  def fixAutoTestNoTypeCheck(in:File) = fixAutoTest(in, false)

  def fixAutoTest(in:File, typeCheck:Boolean = true) = {
    var inFilename = in.getAbsolutePath()
    var stepFilename = inFilename + ".fix"

    (loadAst(inFilename), loadAst(stepFilename)) match {
      case (Right(inAst), Right(stepAst)) => {
        Typechecker(inAst) match {
          case Left(error) => assert(!typeCheck, error)
          case _ => None
        }

        Typechecker(stepAst) match {
          case Left(error) => assert(!typeCheck, error)
          case _ => None
        }

        assert(Interpreter.eval(inAst) === Interpreter.eval(stepAst))
      }
      case (Left(error), _) => assert(false, error)
      case (_, Left(error)) => assert(false, error)
    }
  }

  def runstep(filename: String): Either[InterpreterError, Option[AST]] = {
    for {
      ast <- loadAst(filename).right
    } yield Interpreter.step(ast)
  }

  def runcase(filename: String): Either[InterpreterError, AST] = {
    for {
      ast <- loadAst(filename).right
      _ <- Typechecker(ast).right
    } yield Interpreter.eval(ast)
  }

}
