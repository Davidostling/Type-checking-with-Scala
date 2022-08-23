package simpret.typechecker

import simpret.parser._
import simpret.errors._

object Typechecker {
  // error handling helper functions
  def errUnknownAST(x: AST) = throw new UnknownASTTypecheckerException(x)
  def errExpectedType(ty_str: String, x: AST) = throw new NotExpectedTypeTypecheckerException(ty_str, x)
  def errVarUnbound(x: AST) = throw new VarUnboundTypecheckerException(x)
  def errAppArgument(ty_param: ASTTY, ty_arg: ASTTY, x: AST) = throw new ApplicationArgumentTypecheckerException(ty_param, ty_arg, x)
  def errBranch(ty1: ASTTY, ty2: ASTTY, x: AST) = throw new BranchMismatchTypecheckerException(ty1, ty2, x)
  def errArrowNotSame(ty_param: ASTTY, ty_res: ASTTY, x: AST) = throw new ArrowNotSameTypecheckerException(ty_param, ty_res, x)
  def errCons(eh_ty: ASTTY, et_lty: ASTTY, x: AST) = throw new ConsMismatchTypecheckerException(eh_ty, et_lty, x)
  def errProjTooSmall(x: AST) = throw new ProjectionTooSmallTypecheckerException(x)
  def errProjTooBig(length: Int, x: AST) = throw new ProjectionTooBigTypecheckerException(length, x)
  def errProjNotField(l: String, x: AST) = throw new ProjectionNotAFieldTypecheckerException(l, x)

  // the recursive typechecking relation
  def check(x: AST, env: Map[String, ASTTY] = Map.empty):ASTTY = {
    x match{
      case BoolLit(_) => BoolTy
      case IntLit(_) => IntTy

      case Variable(c) =>
        if(!env.contains(c)) errVarUnbound(x)
        else env(c)
      
      //PLUSEXP
      case PlusExp(e1, e2) =>
        if (check(e1, env)==IntTy && check(e2, env)== IntTy ) IntTy
        else errExpectedType("IntTy", x)

      //UMINEXP
      case UMinExp(e) =>
        if(check(e, env)==IntTy)  IntTy
        else errExpectedType("IntTy", x)

      //LTEXP
      case LtExp(e1, e2) =>
        if (check(e1, env) == IntTy && check(e2, env)== IntTy) BoolTy
        else errExpectedType("IntTy", x)
        
      //CONDEXP
      case CondExp(c, e1, e2) =>
        check(c, env) match {
          case BoolTy =>
            (check(e1, env), check(e2, env)) match {
              case (ty2, ty3) =>
                if(ty2==ty3) {
                  ty2
                } else {
                  errBranch(ty2, ty3, x)
                }
            }
          case _ => errExpectedType("BoolTy", x)
        }

      //LAMEXP
      case LamExp(id, ty1, ty2) => ArrowTy(ty1, check(ty2, env + ((id ,ty1))))

      //APPEXP
      case AppExp(e1, e2) =>
        val tt1 = check(e1, env)
        val tt2 = check(e2, env)
        tt1 match {
          case ArrowTy(ty1, ty2) if (ty1== tt2) => ty2
          case ArrowTy(ty1, ty2) => errAppArgument (ty1, ty2, x)
          case _ => errExpectedType("ArrowTy" ,x)
        }

      //LETEXP
      case LetExp(id, e1, e2) => check(e2, env + ((id , check(e1, env))))

      //FIXAPPEXP
      case FixAppExp(e) =>
        check(e, env) match {
          case ArrowTy(ty1,ty2) =>
            if (ty1==ty2){
              ty1
            }
            else {
              errArrowNotSame(ty1, ty2, x)
            }
          case _ =>
            errExpectedType("ArrowTy", x)
        }

      //NILEXP
      case NilExp(ty) =>
        ListTy(ty)

      //CONSEXP
      case ConsExp(eh, et) =>
        val eh1 = check(eh, env)
        val et1 = check(et, env)
        (eh1, et1) match {
          case (t1,ListTy(t2)) =>
            if(t1!=t2) errCons(t1, t2, x)
            else ListTy(t2)
          case (t1, t2) => errCons(t1, t2, x)
        }

      //ISNILEXP
      case IsNilExp(e) =>
        val e1 = check(e, env)
         e1 match {
          case ListTy(_) => BoolTy
          case _ => errExpectedType("errExpectedType", x)
        }

      //HEADEXP
      case HeadExp(e) =>
        val e1 = check(e, env)
        e1  match {
          case ListTy(ty) => ty
          case _ => errExpectedType("errExpectedType", x)
        }

      //TAILEXP
      case TailExp(e) =>
        val e1 = check(e, env)
        e1 match {
          case ListTy(ty) => ListTy(ty)
          case _ => errExpectedType("errExpectedType", x)
        }

      //TUPLEEXP
      case TupleExp(el) =>TupleTy(el.map(check(_, env)))

      //PROJTUPLEEXP
      case ProjTupleExp(e, i) =>
        val ep1 = check(e, env)
        ep1 match {
          case TupleTy(tyl) if (0 > i-1) => errProjTooSmall(x)
          case TupleTy(tyl) if (tyl.size > i - 1) => tyl(i - 1)
          case TupleTy(tyl) => errProjTooBig(i, x)
          case _ => errExpectedType("TupleTy", e)
        }

      //RECORDEXP
      case RecordExp(m) =>
        RecordTy(m.map({case (key, value) => key-> 
        check(value, env)}))

      //PROJRECORDEXP
      case ProjRecordExp(e, l) =>
      val el1 = check(e, env)
        el1 match{
          case RecordTy(tymmap) if (!tymmap.contains(l)) => errProjNotField(l, x)
          case RecordTy(tymmap) if (tymmap.contains(l)) => tymmap(l)
          case _ => errExpectedType("RecordTy", x)
        }
    }
  }

  /* function to apply the interpreter */
  def apply(x: AST): Either[TypecheckingError, Unit] = {
    try {
      check(x)
      Right(())
    } catch {
      case ex: TypecheckerException =>
        val msg = ex.message
        val x = ex.x
        val msg2 = msg + " -> \r\n" + ASTPrinter.convToStr(x)
        Left(TypecheckingError(Location.fromPos(x.pos), msg2))
    }
  }
}
