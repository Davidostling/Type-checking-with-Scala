package simpret.interpreter

import simpret.parser._
import simpret.errors._


abstract case class EvaluationException(val message: String, val x: AST,
                                        private val cause: Throwable = None.orNull)
  extends Exception(message, cause)

final class VariableCapturedEvaluationException(val var_id: String, val subst_s: AST,
                                                private val cause: Throwable = None.orNull)
  extends EvaluationException("variable (" + var_id + ") has been captured during substitution", subst_s, cause)

object Interpreter {
  def errVarCap(var_id: String, x: AST) = throw new VariableCapturedEvaluationException(var_id, x)

  /* function for defining which AST elements are values */
  def isvalue(x: AST): Boolean = x match {
    case BoolLit(_) => true
    case IntLit(_) => true
    case LamExp(_,_,_) => true
    case NilExp(_) => true
    case ConsExp(eh, et) => isvalue(eh) & isvalue(et)
    case TupleExp(el) => el.forall(isvalue)
    case RecordExp(em) => em.values.forall(isvalue)
    case _ => false
  }


  def step(x: AST): Option[AST] = {
    x match {
        
      //APPEXP
      //E-App1
      case AppExp(x, y) if !isvalue(x)=> Some(AppExp(step(x).get, y))
      //E-App2  
      case AppExp(x, y) if !isvalue(y)=> Some(AppExp(x, step(y).get))
      //E-App-Abs
      case AppExp(LamExp(st, ast, as), y) => Some(substitute(st, y, as))

      //FIXAPPEXP
      //E-fix
      case FixAppExp(x) if !isvalue(x) =>
        Some(FixAppExp(step(x).get))
      //E-fixbeta
      case FixAppExp(LamExp(x, ty, tt)) if isvalue(LamExp(x, ty, tt)) => 
        Some(substitute(x, FixAppExp(LamExp(x, ty, tt)), tt))

      //UMINEXP
      //E-minusval
      case UMinExp(IntLit(x)) => Some(IntLit(-x))
      //E-minus
      case UMinExp(x) if !isvalue(x) => Some(UMinExp(step(x).get))

      //LTEXP
      //E-lessthan
      case LtExp(IntLit(x), IntLit(y)) => Some(BoolLit(x < y))
      //E-lessthanleft
      case LtExp(x, y) if !isvalue(x) => Some(LtExp(step(x).get, y))
      //E-lessthanright
      case LtExp(x, y) if !isvalue(y) => Some(LtExp(x, step(y).get))

      //PLUSEXP
      // if we have 2 Int with + between we can evaluate by performing addition
      case PlusExp(IntLit(x), IntLit(y)) =>
        Some(IntLit(x + y))
      //E-addLeft if x can evaluate to x´in one step we can evaluate x +y -> x´+y
      case PlusExp(x, y) if !isvalue(x) =>
        Some(PlusExp(step(x).get, y)) //x prime
      //case when one of terms are not constant yet
      //E-addRight if the first are already constant and not the second we can evaluate
      case PlusExp(IntLit(x),y)  => step(y).map(PlusExp(IntLit(x), _))

      //CONDEXP

      //E-IfTrue
      case CondExp(BoolLit(true), y, z) =>
        Some(y)
      //E-IfFalse
      case CondExp(BoolLit(false), y, z) =>
        Some(z)
      //E-if
      case CondExp(x, y, z) if !isvalue(x) =>
        Some(CondExp(step(x).get, y, z))

      //LETEXP
      //E-let
      case LetExp(x, y, z) if !isvalue(y) =>
        Some(LetExp(x, step(y).get, z))
      //E-letV
      case LetExp(x, y, z) =>
        Some(substitute(x, y, z))

      //CONSEXP
      //E-cons1
      case ConsExp(x, y) if !isvalue(x) => Some(ConsExp(step(x).get, y))
      //E-cons2
      case ConsExp(x, y) if !isvalue(y) => Some(ConsExp(x, step(y).get))
      
      //HEADEXP
      //E-HeadCons
      case HeadExp(ConsExp(eh, et)) if isvalue(ConsExp(eh, et))  => Some(eh)
      //E-Head
      case HeadExp(e) => step(e).map(HeadExp(_))

      //TAILEXP
      //E-TailCons
      case TailExp(ConsExp(eh, et)) if isvalue(ConsExp(eh, et))  => Some(et)
      //E-Tail
      case TailExp(e) => step(e).map(TailExp(_))

      //NILEXP
      case NilExp(_) => None

      //ISNILEXP
      //E-IsNilNil
      case IsNilExp(NilExp(ty)) => Some(BoolLit(true))
      //E-IsNilCons
      case IsNilExp(ConsExp(eh, et)) => Some(BoolLit(false))
      //IsNil
      case IsNilExp(e) => step(e).map(HeadExp(_))

      //TUPLEEXP
      case TupleExp(l) if !isvalue(x) => 
        subStepList(l) match {
          case Some(l1) => Some(TupleExp(l1))
          case None => None
        }

      //PROJTUPLEEXP
      case ProjTupleExp(TupleExp(l), i) =>
        if (isvalue(l(i - 1)))  Some(l(i - 1))
        else step(TupleExp(l))
      case ProjTupleExp(e, i) =>
        step(e).map(ProjTupleExp(_, i))


      //RECORDEXP
      case RecordExp(m) if !isvalue(x) =>
        subStepMap(m.keys.toList, m) match {
          case Some(m1) => Some(RecordExp(m1))
          case None => None
        }

      //PROJRECORDEXP
      case ProjRecordExp(RecordExp(m),i) =>
        if (isvalue(m(i)))  Some(m(i))
        else step(RecordExp(m))
      case ProjRecordExp(e, i) =>
        step(e).map(ProjRecordExp(_,i))

      //NONE
      case _ => None
    }
  }

  def subStepList(l: List[AST]):Option[List[AST]] = l match {
    case List() => Some(List())
    case (a::as) =>
      if(isvalue(a)) {
        subStepList(as) match {
          case Some(as1) => Some(a::as1)
          case None => None
        }
      } else {
        step(a) match {
          case Some(c) => Some(as.patch(l.size, List(c), 1).reverse)
          case None => None
        }
      }
  }

  def subStepMap[A](keys: List[A], m: Map[A,AST]):Option[Map[A,AST]] = keys match {
    case List() => Some(m)
    case k::ks =>
      if (isvalue(m(k))) {
        subStepMap(ks, m)
      } else {
        step(m(k)) match {
          case Some(c) => Some(m+(k -> c))
          case None => None
        }
      }
  }
  
  val rename : String = "string"
  def substitute(x: String, s: AST, t: AST): AST = t match {
    
    case LamExp(t1, ty, e)  =>
      if (t1==x) t // if y (s) = x in lambda condition; we dont do anything as we do not want to replace the bound occurences - we skip it
      else if ((t1!=x)&&(!freevariables(s).contains(t1))) LamExp(t1, ty, substitute(x,s,e)) //if y!=x and y (s) is not a free variable; avoid capturing --> recursive substitution
      /*
      ex  [x->s](lambday . t1) = lambday . [x->s]t1
      if y = x we need to first rename the variable y to something else, so we rename the bounder y
      and the occurense that are bind by the bounder then continue with the substituten
      */
      else LamExp(rename, ty, substitute(x, s, reduce(e,t1,rename))) //ensures that the parameter y is ALWAYS unique enabling the capture avoiding substitution; y!=x, y is a freevariable
    //if y would be in freevariables(s) then we would have a free variable of s which would get bound by y, this means that if y is not a freevariable(s) it will avoid capturing

    case Variable(t1) =>
      if (t1==x)  s // if y (s) = x
      else   t // if y (s) != x, we skip it; do nothing

    //Execute all Exp functions
    case AppExp(e1, e2) =>
      AppExp(substitute(x, s, e1), substitute(x, s, e2))

    case PlusExp(e1, e2) =>
      PlusExp(substitute(x, s, e1), substitute(x, s, e2))

    case CondExp(c, e1, e2) =>
      CondExp(substitute(x, s, c), substitute(x, s, e1), substitute(x, s, e2))

    case UMinExp(e) =>
      UMinExp(substitute(x, s, e))

    case LtExp(e1, e2) =>
      LtExp(substitute(x, s, e1), substitute(x, s, e2))

    case LetExp(id, e1, e2) =>
      if(id == x) {
        LetExp(id, substitute(x, s, e1), e2)
      } else {
        LetExp(id, substitute(x, s, e1), substitute(x, s, e2))
      }

    case NilExp(ty) =>
      t

    case ConsExp(eh, et) =>
      ConsExp(substitute(x, s, eh), substitute(x, s, et))
      
    case IsNilExp(e) =>
      IsNilExp(substitute(x, s, e))

    case HeadExp(e) =>
      HeadExp(substitute(x, s, e))

    case TailExp(e) =>
      TailExp(substitute(x, s, e))

    case FixAppExp(e) =>
      FixAppExp(substitute(x, s, e))

    case TupleExp(el) =>
      TupleExp(el.map(substitute(x, s, _)))

    case ProjTupleExp(e, i) =>
      ProjTupleExp(substitute(x, s, e), i)
      
    case RecordExp(em) =>
      RecordExp(em.transform((key, value) => substitute(x, s, value))) 

    case ProjRecordExp(e, l) =>
      ProjRecordExp(substitute(x, s, e), l)

    case _ => t //None

  }


  def reduce(t: AST, s: String, x: String): AST = t match {
    //we consistently rename the binder (t1) and the occurrences (e) that are bound by the corresponding binder, this enables the substitution to always be defined for lambda abstractions
    //we use this function to ensure the uniqueness of the variable y
    case Variable(t1)  =>
      if (t1==s) Variable(x)
      else t

    //Execute all Exp functions
    case AppExp(e1, e2) =>
      AppExp(reduce(e1, s, x), reduce(e2, s, x))
    case PlusExp(e1, e2) =>
      PlusExp(reduce(e1, s, x), reduce(e2, s, x))
    case CondExp(c, e1, e2) =>
      CondExp(reduce(c, s, x), reduce(e1, s, x), reduce(e2, s, x))
    case LtExp(e1, e2) =>
      LtExp(reduce(e1, s, x), reduce(e2, s, x))
    case UMinExp(e) =>
      UMinExp(reduce(e, s, x))
    case ConsExp(eh, et) =>
      LtExp(reduce(eh, s, x), reduce(et, s, x))
    case HeadExp(e) =>
      HeadExp(reduce(e, s, x))
    case TailExp(e) =>
      TailExp(reduce(e, s, x))
    case NilExp(ty) =>
      t
    case IsNilExp(e) =>
      IsNilExp(reduce(e, s, x))
    case RecordExp(em) =>
      RecordExp(em.transform((key, value) => reduce(value, s, x)))
    case FixAppExp(e) =>
      FixAppExp(reduce(e, s, x))
    case TupleExp(el) =>
      TupleExp(el.map(reduce(_, s, x)))
    case LamExp(t1, ty, e)  =>
      if (t1==s)t
      else LamExp(t1, ty, reduce(e, s, x))
  }

  def freevariables (x: AST) : List[String] =
    x match {
      case Variable(id) =>
        List(id)

      case CondExp(c, e1, e2) =>
        val f1 = freevariables(c)
        val f2 = freevariables(e1)
        val f3 = freevariables(e2)
        f1 ++ f2 ++ f3

      case PlusExp(e1, e2) =>
        val f1 = freevariables(e1)
        val f2 = freevariables(e2)
        f1 ++ f2

      case AppExp(e1, e2) =>
        val f1= freevariables(e1)
        val f2 = freevariables(e2)
        f1 ++ f2

      case LamExp(id, ty, t) =>
        val f1 = freevariables(t)
        f1.filterNot( _ == id )

      case LetExp(id, e1, e2) =>
        val f1= freevariables(e1)
        val f2 = freevariables(e2)
        f1 ++ f2

      case UMinExp(e) =>
        freevariables(e)

      case LtExp(e1, e2) =>
        val f1 = freevariables(e1)
        val f2 = freevariables(e2)
        f1++f2

      case FixAppExp(e) =>
        freevariables(e)

      case HeadExp(e) =>
        freevariables(e)

      case TailExp(e) =>
        freevariables(e)

      case  ConsExp(eh, et) =>
        val f1 = freevariables(eh)
        val f2 = freevariables(et)
        f1++f2

      case NilExp(ty) =>
        List()

      case IsNilExp(e) =>
        freevariables(e)

      case ProjTupleExp(e, i) =>
        freevariables(e)

      case ProjRecordExp(e, l) =>
        freevariables(e)

      case TupleExp(el) =>
        el.flatMap(freevariables)

      case RecordExp(em) =>
        em.values.toList.flatMap(freevariables)

      case _ => List()

    }



  /* evaluation function to iterate the steps of evaluation */
  def eval(x: AST): AST = step(x) match {
    case None => x
    case Some(x1) => eval(x1)
  }

  /* function to apply the interpreter */
  def apply(x: AST): Either[EvaluationError, AST] = {
    try {
      Right(eval(x))
    } catch {
      case EvaluationException (msg, xe, _) =>
        val msg2 = msg + " -> \r\n" + ASTPrinter.convToStr(xe)
        Left(EvaluationError(Location.fromPos(xe.pos), msg2))
    }
  }
}
