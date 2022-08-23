package simpret.lexer

import scala.util.parsing.input.Positional


sealed trait Token extends Positional


/* ------------- expression literals ---------------- */
case class TOKID(str: String) extends Token       // identifiers
case class TOKBOOL(i: Boolean) extends Token      // "true" or "false"
case class TOKINT(i: Int) extends Token           // (non-negative) int literals


/* ---------- mainly expression symbols ------------- */
case object TOKIF extends Token        // "if"
case object TOKTHEN extends Token      // "then"
case object TOKELSE extends Token      // "else"

case object TOKPLUS extends Token      // "+"  binary infix
case object TOKLT extends Token        // "<" binary infix
case object TOKMINUS extends Token     // "-"  unary

case object TOKPARL extends Token      // "("
case object TOKPARR extends Token      // ")"

case object TOKLAM extends Token       // "\" lambda
case object TOKCOL extends Token       // ":"
case object TOKDOT extends Token       // "."
case object TOKLET extends Token       // "let"
case object TOKIN extends Token        // "in"

case object TOKFIX extends Token       // "fix" fix point
case object TOKLETREC extends Token    // "letrec"

case object TOKEQ extends Token        // "="
case object TOKCOM extends Token       // ","
case object TOKCURL extends Token      // "{"
case object TOKCURR extends Token      // "}"

case object TOKSQBL extends Token      // "["
case object TOKSQBR extends Token      // "]"
case object TOKVBAR extends Token      // "|"
case object TOKCONS extends Token      // "::"
case object TOKISNIL extends Token     // "isnil"
case object TOKHEAD extends Token      // "hd"
case object TOKTAIL extends Token      // "tl"


/* ------------------ type symbols ------------------ */
case object TOKTYBOOL extends Token    // "bool"
case object TOKTYINT extends Token     // "int"
case object TOKTYARROW extends Token   // "->"