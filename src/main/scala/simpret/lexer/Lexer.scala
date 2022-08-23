package simpret.lexer

import simpret.errors._
import scala.util.parsing.combinator._

// https://www.tutorialspoint.com/scala/scala_regular_expressions.htm


object Lexer extends RegexParsers {
  override def skipWhitespace = false

  /* comment and whitespace handling */
  def skip: Parser[Unit] = rep(whiteSpace | comment) ^^^ ()
  def skip1: Parser[Unit] = rep1(whiteSpace | comment) ^^^ ()
  def comment: Parser[Unit] = singleComment | multiComment
  def singleComment: Parser[Unit] = "//" ~ rep(not("\n") ~ ".".r) ^^^ ()
  def multiComment: Parser[Unit] = "/*" ~ rep(not("*/") ~ "(?s).".r) ~ "*/" ^^^ ()

  /* identifiers */
  def ident: Parser[TOKID] = positioned {
    "[a-zA-Z_][a-zA-Z0-9_]*".r     ^^ { TOKID(_) }
  }

  /* literals */
  def literals: Parser[Token] =
    positioned (boolt | boolf | intlit)
  def boolt       = "true"         ^^ (_ => TOKBOOL(true) )
  def boolf       = "false"        ^^ (_ => TOKBOOL(false) )

  def intlit: Parser[TOKINT] = positioned {
    "0|([1-9][0-9]*)".r      ^^ { str => TOKINT(Integer.parseInt(str)) }
  }

  /* keywords */
  def keywords: Parser[Token] =
    positioned ((condif | condthen | condelse |
      letrec | let |
      tyint | in |
      fix |
      isnil | head | tail |
      tybool)
      <~ not(ident | literals))  // a keyword can only be followed immediately by a symbol,
                                 // otherwise skip.
                                 // e.g., "int" in "int->int"
                                 // but "int" in "inte" is NOT a keyword

  def condif      = "if"           ^^ (_ => TOKIF)
  def condthen    = "then"         ^^ (_ => TOKTHEN)
  def condelse    = "else"         ^^ (_ => TOKELSE)

  def let         = "let"          ^^ (_ => TOKLET)
  def letrec      = "letrec"       ^^ (_ => TOKLETREC)
  def in          = "in"           ^^ (_ => TOKIN)
  def tyint       = "int"          ^^ (_ => TOKTYINT)
  def fix         = "fix"          ^^ (_ => TOKFIX)

  def isnil       = "isnil"        ^^ (_ => TOKISNIL)
  def head        = "hd"           ^^ (_ => TOKHEAD)
  def tail        = "tl"           ^^ (_ => TOKTAIL)

  def tybool      = "bool"         ^^ (_ => TOKTYBOOL)

  /* symbols */
  def symbols: Parser[Token] =
    positioned (plus | lt | minus_tyarr |
      parl | parr |
      lam | dot | col_cons |
      eq | comma | curl | curr |
      sqbl | sqbr | vbar)

  def plus        = "+"            ^^ (_ => TOKPLUS)
  def lt          = "<"            ^^ (_ => TOKLT)
  def minus_tyarr = "-" ~ opt(">") ^^ {
    case _ ~ None    => TOKMINUS        // "-"
    case _ ~ Some(_) => TOKTYARROW      // "->"
  }

  def parl        = "("            ^^ (_ => TOKPARL)
  def parr        = ")"            ^^ (_ => TOKPARR)

  def lam         = "\\"           ^^ (_ => TOKLAM)
  def dot         = "."            ^^ (_ => TOKDOT)
  def col_cons    = ":" ~ opt(":") ^^ {
    case _ ~ None    => TOKCOL          // ":"
    case _ ~ Some(_) => TOKCONS         // "::"
  }

  def eq          = "="            ^^ (_ => TOKEQ)
  def comma       = ","            ^^ (_ => TOKCOM)
  def curl        = "{"            ^^ (_ => TOKCURL)
  def curr        = "}"            ^^ (_ => TOKCURR)

  def sqbl        = "["            ^^ (_ => TOKSQBL)
  def sqbr        = "]"            ^^ (_ => TOKSQBR)
  def vbar        = "|"            ^^ (_ => TOKVBAR)

  /* token stream */
  def tokens: Parser[List[Token]] = skip ~> rep1(token <~ skip) <~ eof

  def eof: Parser[String] = "\\z".r | failure("unexpected character")
  def token: Parser[Token] =
    positioned(literals | symbols | keywords | ident)

  def apply(input: String): Either[LexerError, List[Token]] = {
    parseAll(tokens, input) match {
      case Success(result, _) => Right(result)
      case failure : NoSuccess => Left(LexerError(Location.fromPos(failure.next.pos), failure.msg))
    }
  }
}
