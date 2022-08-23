package simpret.parser


import scala.util.parsing.input.Positional


trait AST extends Positional

case class Variable(id: String) extends AST
case class BoolLit(b: Boolean) extends AST
case class IntLit(i: Int) extends AST

case class CondExp(c: AST, e1: AST, e2: AST) extends AST
case class PlusExp(e1: AST, e2: AST) extends AST
case class LtExp(e1: AST, e2: AST) extends AST
case class UMinExp(e: AST) extends AST // unary minus

case class LamExp(id: String, ty: ASTTY, e: AST) extends AST
case class AppExp(e1: AST, e2: AST) extends AST
case class LetExp(id: String, e1: AST, e2: AST) extends AST
case class FixAppExp(e: AST) extends AST

case class TupleExp(el: List[AST]) extends AST
case class ProjTupleExp(e: AST, i: Int) extends AST
case class RecordExp(em: Map[String, AST]) extends AST
case class ProjRecordExp(e: AST, l: String) extends AST

case class NilExp(ty: ASTTY) extends AST
case class ConsExp(eh: AST, et: AST) extends AST
case class IsNilExp(e: AST) extends AST
case class HeadExp(e: AST) extends AST
case class TailExp(e: AST) extends AST





trait ASTTY extends Positional

case object BoolTy extends ASTTY
case object IntTy extends ASTTY

case class ArrowTy(ty1: ASTTY, ty2: ASTTY) extends ASTTY

case class TupleTy(tyl: List[ASTTY]) extends ASTTY
case class RecordTy(tym: Map[String, ASTTY]) extends ASTTY
case class ListTy(ty: ASTTY) extends ASTTY

