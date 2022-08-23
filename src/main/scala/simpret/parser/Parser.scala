package simpret.parser

import simpret.errors._
import simpret.lexer._
import scala.util.parsing.combinator._
import scala.util.parsing.input._


// Background information:
//
// https://enear.github.io/2016/03/31/parser-combinators/
// https://github.com/enear/parser-combinators-tutorial
// https://github.com/scala/scala-parser-combinators
//
// https://stackoverflow.com/questions/11533547/operator-precedence-with-scala-parser-combinators
// http://bitwalker.org/posts/2013-08-10-learn-by-example-scala-parser-combinators/
// http://www.scala-lang.org/api/2.12.3/scala-parser-combinators/scala/util/parsing/combinator/RegexParsers.html
// http://nielssp.dk/2015/07/creating-a-scanner-using-parser-combinators-in-scala/
// http://www.scala-lang.org/files/archive/api/2.7.7/scala/util/parsing/input/


class RecordFieldException(val message: String, val x: AST,
                           private val cause: Throwable = None.orNull)
  extends Exception(message, cause)

class RecordFieldTypeException(val message: String, val x: ASTTY,
                           private val cause: Throwable = None.orNull)
  extends Exception(message, cause)

class TokenReader(tokens: Seq[Token]) extends Reader[Token] {
  override def first: Token = tokens.head
  override def atEnd: Boolean = tokens.isEmpty
  override def pos: Position = if (atEnd) NoPosition else first.pos
  override def rest: Reader[Token] = new TokenReader(tokens.tail)
}

object Parser extends Parsers {
  override type Elem = Token

  /*
  // a whole program
  prog = stmt
  stmt = expr

  // expressions with prefix token
  expr = IF ~ expr ~ THEN ~ expr ~ ELSE ~ expr |
    LAM ~ x ~ COL ~ type_exp ~ DOT ~ expr |
    LET ~ x ~ EQ ~ expr ~ IN ~ expr |
    LETREC ~ x ~ COL ~ type_exp ~ EQ ~ expr ~ IN ~ expr |
    ISNIL ~ expr | HEAD ~ expr | TAIL ~ expr |
    term0

  // infix "less than"
  term0 = term1 ~ (opt(LT ~ term1))

  // infix plus
  term1 = term2 ~ (rep(plus_term))
  plus_term2 = PLUS ~ term2

  // infix application
  term2 = (fix_app | term3) ~ (rep(app_term3))
  fix_app = fix ~ term3
  app_term3 = term3

  // infix cons
  term3 = term4 ~ (rep(cons_term4))
  cons_term4 = CONS ~ term4

  // minus
  term4 = rep(MINUS) ~ term5

  // infix projection
  label = x
  term5 = atom ~ (rep(tuple_record_proj))
  tuple_record_proj = DOT ~ (intlit | label)

  // atoms
  atom = var | boollit | intlit | par_and_tuple | record | list

  // parentheses, tuples, lists
  par_and_tuple = PARL ~ stmt ~ (rep(comma_stmt)) ~ PARR
  list = SQBL ~ ((opt(stmt ~ (rep(comma_stmt)) ~ VBAR)) ~ type_exp) ~ SQBR
  comma_stmt = COM ~ stmt

  // records
  record = CURL ~ record_item ~ (rep(comma_record_item)) ~ CURR
  record_item = label ~ EQ ~ stmt
  comma_record_item = COM ~ record_item

  ------

  type_exp = type_atom ~ rep(arrow_type_atom)
  arrow_type_atom = ARROW ~ type_atom

  type_atom = BOOL | INT | par_and_tuple_type | record_type | list_type

  par_and_tuple_type = PARL ~ type_exp ~ (rep(comma_type_exp)) ~ PARR
  comma_type_exp = COM ~ type_exp

  list_type = SQBL ~ type_exp ~ SQBR

  record_type = CURL ~ record_item_type ~ (rep(comma_record_item_type)) ~ CURR
  record_item_type = label ~ COL ~ type_exp
  comma_record_item_type = COM ~ record_item_type

  ------

  Print parentheses, when:
  CondExp/LamExp/LetExp/LetRecExp/IsNilExp/HeadExp/TailExp -> no parentheses needed
  LtExp ->  "all before" and LtExp
  PlusExp -> "all before"
         -> and when PlusExp appears on the right side
  AppExp/FixAppExp -> "all before"
         -> and when AppExp/FixAppExp appears on the right side
  ConsExp -> "all before"
         -> and when ConsExp appears on the left side
         -> and for ConsExp, contraction to comma separated list
  UMinExp -> "all before"
  ProjTupleExp/ProjRecordExp -> "all before"

  ArrowTy -> when ArrowTy appears on the left side

  */

  /* helper function */
  def collect_parser[T_IN, T_OUT](start_token: Token, sub_parser: Parser[T_IN], collect_fun: T_IN=>T_OUT): Parser[T_OUT] = {
    start_token ~ sub_parser ^^ { case _ ~ in => collect_fun(in) }
  }

  def unary_op[T](start_token: Token, sub_parser: Parser[T], pack_fun: T=>T): Parser[T] = {
    start_token ~ sub_parser ^^ { case _ ~ x => pack_fun(x) }
  }

  /* a whole program */
  def prog: Parser[AST] = {
    phrase(stmt)
  }
  def stmt = expr

  /* expressions */
  def expr: Parser[AST] = positioned {
    def cond: Parser[AST] = {
      TOKIF ~ expr ~ TOKTHEN ~ expr ~ TOKELSE ~ expr ^^ {
        case _ ~ c ~ _ ~ e1 ~ _ ~ e2 => CondExp(c, e1, e2)
      }
    }

    def lamabs: Parser[AST] = {
      TOKLAM ~ ident ~ TOKCOL ~ type_exp ~ TOKDOT ~ expr ^^ {
        case _ ~ Variable(id) ~ _ ~ ty ~ _ ~ e => LamExp(id, ty, e)
        case _ ~ _ ~ _ ~ ty ~ _ ~ e => LamExp("_", ty, e) // to make the match exhaustive
      }
    }

    def let: Parser[AST] = {
      TOKLET ~ ident ~ TOKEQ ~ expr ~ TOKIN ~ expr ^^ {
        case _ ~ Variable(id) ~ _ ~ e1 ~ _ ~ e2 => LetExp(id, e1, e2)
        case _ ~ _ ~ _ ~ e1 ~ _ ~ e2 => LetExp("_", e1, e2) // to make the match exhaustive
      }
    }

    def letrec: Parser[AST] = {
      TOKLETREC ~ ident ~ TOKCOL ~ type_exp ~ TOKEQ ~ expr ~ TOKIN ~ expr ^^ {
        case _ ~ Variable(id) ~ _ ~ ty ~ _ ~ e1 ~ _ ~ e2 => LetExp(id, FixAppExp(LamExp(id, ty, e1)), e2)
        case _ ~ _ ~ _ ~ ty ~ _ ~ e1 ~ _ ~ e2 => LetExp("_", FixAppExp(LamExp("_", ty, e1)), e2) // to make the match exhaustive
      }
    }

    def isnil = unary_op(TOKISNIL, expr, e => IsNilExp(e))
    def head = unary_op(TOKHEAD, expr, e => HeadExp(e))
    def tail = unary_op(TOKTAIL, expr, e => TailExp(e))

    cond |
      lamabs | let | letrec |
      isnil | head | tail |
      term0
  }

  /* terms */
  def term0: Parser[AST] = {
    term1 ~ opt(TOKLT ~ term1) ^^ {
      case t ~ None => t
      case t1 ~ Some(_ ~ t2) => LtExp(t1, t2)
    }
    }

  def term1: Parser[AST] = {
    def plus_term2 = collect_parser(TOKPLUS, term2, (e:AST) => (x:AST) => PlusExp(x,e))
    term2 ~ rep(plus_term2) ^^ { case t1 ~ t2 => (t1 /: t2) { (acc,f) => f(acc) } }
  }

  def term2: Parser[AST] = {
    // application is left associative
    def app_term3: Parser[AST => AST] = {
      term3 ^^ { case e => AppExp(_, e) }
    }

    def fix_app = collect_parser(TOKFIX, term3, (e:AST) => FixAppExp(e))
    (fix_app | term3) ~ rep(app_term3) ^^ { case t1 ~ t2 => (t1 /: t2) { (acc,f) => f(acc) } }
  }

  def term3: Parser[AST] = {
    def cons_term4 = collect_parser(TOKCONS, term4, (e:AST) => e)
    term4 ~ rep(cons_term4) ^^ {
      case t1 ~ t2 =>
        val es = (t1 :: t2).reverse
        val er = es.head
        val eFuns = es.tail.map(e => (y: AST) => ConsExp(e, y))

        (er /: eFuns) { (acc, f) => f(acc) }
    }
  }

  def term4: Parser[AST] = {
    rep(TOKMINUS) ~ term5 ^^ { case ml ~ t => (t /: ml) { (acc, _) => UMinExp(acc) } }
  }

  def term5: Parser[AST] = {
    def tuple_record_proj: Parser[AST=>AST] = {
      def index: Parser[AST=>AST] = {
        accept("index number", { case _ @ TOKINT(v) => ProjTupleExp(_, v) })
      }
      def label: Parser[AST=>AST] = {
        accept("projection label", { case _ @ TOKID(name) => ProjRecordExp(_, name) })
      }

      TOKDOT ~ (index | label) ^^ { case _ ~ ef => ef}
    }

    atom ~ rep(tuple_record_proj) ^^ { case t1 ~ t2 => (t1 /: t2) { (acc,f) => f(acc) } }
  }


  /* atoms */
  def atom: Parser[AST] = positioned {
    ident | boollit | intlit | par_and_tuple | record | list
  }

  def ident: Parser[AST] = {
    accept("identifier", { case _ @ TOKID(name) => Variable(name) })
  }

  def boollit: Parser[AST] = {
    accept("boolean literal", { case _ @ TOKBOOL(v) => BoolLit(v) })
  }

  def intlit: Parser[AST] = {
    accept("integer literal", { case _ @ TOKINT(v) => IntLit(v) })
  }

  def par_and_tuple: Parser[AST] = {
    TOKPARL ~ stmt ~ rep(comma_stmt) ~ TOKPARR ^^ {
      case _ ~ e ~ List() ~ _ => e
      case _ ~ e ~ es ~ _ => TupleExp(e::es)
    }
  }

  def list: Parser[AST] = {
    TOKSQBL ~ opt(stmt ~ rep(comma_stmt) ~ TOKVBAR) ~ type_exp ~ TOKSQBR ^^ {
      case _ ~ None ~ ty ~ _ => NilExp(ty)
      case _ ~ Some(e ~ es ~ _) ~ ty ~ _ => ((e::es) :\ (NilExp(ty):AST)) { ConsExp.apply }
    }
  }
  def comma_stmt = collect_parser(TOKCOM, stmt, (e:AST) => e)

  def record: Parser[AST] = {
    def label: Parser[String] = {
      accept("record label", { case _ @ TOKID(name) => name })
    }
    def record_item: Parser[(String, AST)] = {
      label ~ TOKEQ ~ stmt ^^ { case name ~ _ ~ e => (name, e) }
    }

    def comma_record_item = collect_parser(TOKCOM, record_item, (x:(String, AST)) => x)
    TOKCURL ~ record_item ~ rep(comma_record_item) ~ TOKCURR ^^ {
      case _ ~ it1 ~ its ~ _ =>
        RecordExp(((Map.empty:Map[String,AST]) /: (it1::its)) {
          case (m, (name,e)) =>
            if (m.keySet.contains(name)) {
              throw new RecordFieldException("record field \"" + name + "\" occurs twice", e)
            }
            m + (name -> e)
        })
    }
  }



  /* types */
  def type_exp: Parser[ASTTY] = positioned {
    // the arrow type operator is is right associative
    def arrow_type_atom = collect_parser(TOKTYARROW, type_atom, (x:ASTTY) => x)
    type_atom ~ rep(arrow_type_atom) ^^ { case t1 ~ t2 =>
      val tys = (t1::t2).reverse
      val tyr = tys.head
      val tyFuns = tys.tail.map(ty => (y:ASTTY) => ArrowTy(ty, y))

      (tyr /: tyFuns) { (acc,f) => f(acc) }
    }
  }

  def type_atom: Parser[ASTTY] = {
    def typebool: Parser[ASTTY] =
      TOKTYBOOL ^^ { case _ => BoolTy }

    def typeint: Parser[ASTTY] =
      TOKTYINT ^^ { case _ => IntTy }

    def comma_type_exp = collect_parser(TOKCOM, type_exp, (x:ASTTY) => x)
    def par_and_tuple_type: Parser[ASTTY] = {
      TOKPARL ~ type_exp ~ rep(comma_type_exp) ~ TOKPARR ^^ {
        case _ ~ ty ~ List() ~ _ => ty
        case _ ~ ty ~ tys ~ _ => TupleTy(ty::tys)
      }
    }

    def list_type: Parser[ASTTY] = {
      TOKSQBL ~ type_exp ~ TOKSQBR ^^ { case _ ~ ty ~ _ => ListTy(ty) }
    }

    def record_type: Parser[ASTTY] = {
      def label: Parser[String] = {
        accept("record label", { case _ @ TOKID(name) => name })
      }
      def record_item_type: Parser[(String, ASTTY)] = {
        label ~ TOKCOL ~ type_exp ^^ { case name ~ _ ~ ty => (name, ty) }
      }

      def comma_record_item_type = collect_parser(TOKCOM, record_item_type, (x:(String, ASTTY)) => x)
      TOKCURL ~ record_item_type ~ rep(comma_record_item_type) ~ TOKCURR ^^ {
        case _ ~ it1 ~ its ~ _ =>
          RecordTy(((Map.empty:Map[String,ASTTY]) /: (it1::its)) {
            case (m, (name,ty)) =>
              if (m.keySet.contains(name)) {
                throw new RecordFieldTypeException("record field \"" + name + "\" occurs twice", ty)
              }
              m + (name -> ty)
          })
      }
    }

    typebool | typeint | par_and_tuple_type | record_type | list_type
  }

  /* function to apply the parser */
  def apply(tokens: Seq[Token]): Either[ParserError, AST] = {
    val reader = new TokenReader(tokens)

    try {
    prog(reader) match {
      case Success(result, _) => Right(result)
      case failure : NoSuccess => Left(ParserError(Location.fromPos(failure.next.pos), failure.msg))
      }
    } catch {
      case ex: RecordFieldException =>
        val msg = ex.message
        val xe = ex.x
        val msg2 = msg + " -> \r\n" + ASTPrinter.convToStr(xe)
        Left(ParserError(Location.fromPos(xe.pos), msg2))
      case ex: RecordFieldTypeException =>
        val msg = ex.message
        val xe = ex.x
        val msg2 = msg + " -> \r\n" + ASTPrinter.convToTyStr(xe)
        Left(ParserError(Location.fromPos(xe.pos), msg2))
    }
  }
}
