package simpret.parser

import simpret.errors.PrintingError


object ASTPrinter {
  // helper predicates to determine whether parentheses are needed
  def needNoPar(e: AST) = false
  def needParTerm0(e: AST) = {
    e match {
      case CondExp(_,_,_) => true
      case LamExp(_,_,_) => true
      case IsNilExp(_) => true
      case HeadExp(_) => true
      case TailExp(_) => true
      case LtExp(_,_) => true
      case _ => needNoPar(e)
    }
  }
  def needParTerm1(e: AST) = {
    e match {
      case _ => needParTerm0(e)
    }
  }
  def needParTerm1Plus(e: AST) = {
    e match {
      case PlusExp(_, _) => true
      case _ => needParTerm1(e)
    }
  }
  def needParTerm2(e: AST) = {
    e match {
      case _ => needParTerm1Plus(e)
    }
  }
  def needParTerm2App(e: AST) = {
    e match {
      case AppExp(_, _) => true
      case FixAppExp(_) => true
      case _ => needParTerm2(e)
    }
  }
  def needParTerm3(e: AST) = {
    e match {
      case _ => needParTerm2App(e)
    }
  }
  def needParTerm3Cons(e: AST) = {
    e match {
      case ConsExp(_, _) => true
      case _ => needParTerm3(e)
    }
  }
  def needParTerm4(e: AST) = {
    e match {
      case _ => needParTerm3Cons(e)
    }
  }
  def needParTerm5(e: AST) = {
    e match {
      case UMinExp(_) => true
      case _ => needParTerm4(e)
    }
  }
  def needParType(e: ASTTY) = {
    e match {
      case _ => false
    }
  }
  def needParTypeArrow(e: ASTTY) = {
    e match {
      case ArrowTy(_, _) => true
      case _ => needParType(e)
    }
  }

  /* helper function to print "with needed parentheses" */
  def convToStrWNP[A](needFunc: A=>Boolean, convFun:(A,Int)=>String, e: A, skipCnt: Int) = {
    val needPar = needFunc(e)
    val skipCnt_new = skipCnt + (if (needPar) 1 else 0)

    val str1 = if (needPar) "(" else ""
    val str2 = convFun(e, skipCnt_new)
    val str3 = if (needPar) ")" else ""
    str1 + str2 + str3
  }

  def coll_to_str[A] (c : Iterable[A], it_to_str: A => String) =
    it_to_str(c.head) + c.tail.foldLeft("")((str: String, it: A) => str + ", " + it_to_str(it))

  /* convert an ASTTY to a String for pretty printing */
  def convToTyStr(x:ASTTY, skipCnt: Int = 0):String = {

    x match {
      case BoolTy => "BOOL"
      case IntTy => "INT"
      case ArrowTy(ty1, ty2) =>
        val str1 = convToStrWNP(needParTypeArrow, convToTyStr, ty1, skipCnt)
        val strm = "->"
        val str2 = convToStrWNP(needParType, convToTyStr, ty2, skipCnt)
        str1 + strm + str2
      case TupleTy(tyl) =>
        def it_to_str(ty: ASTTY) = convToTyStr(ty, skipCnt)
        "(" + coll_to_str(tyl, it_to_str) + ")"
      case RecordTy(tym) =>
        def it_to_str(it: (String, ASTTY)) = it match {
          case (label, ty) => label + ":" + convToTyStr(ty, skipCnt)
        }
        "{" + coll_to_str(tym, it_to_str) + "}"
      case ListTy(ty) =>
        "[" + convToTyStr(ty, skipCnt) + "]"
    }
  }

  /* convert an AST to a String for pretty printing */
  def convToStr(x:AST, skipCnt: Int = 0):String = {
    val spaceStr = " "
    val indentSize = 2
    val indentStr = spaceStr * indentSize
    val newLine = "\r\n" + (spaceStr * skipCnt)

    def unary_to_str(needParFun: AST => Boolean,opname: String, e: AST) = {
      val strm = opname + " "
      val str1 = convToStrWNP(needParFun, convToStr, e, skipCnt + strm.length())
      strm + str1
    }

    x match {
      case Variable(id) =>
        id
      case BoolLit(b) =>
        if (b) "true" else "false"
      case IntLit(i) =>
        i.toString()

      case NilExp(ty: ASTTY) => "[" + convToTyStr(ty) + "]"
      case TupleExp(el: List[AST]) =>
        def it_to_str(e: AST) = convToStr(e, skipCnt)
        "(" + coll_to_str(el, it_to_str) + ")"
      case RecordExp(em: Map[String,AST]) =>
        def it_to_str(it: (String, AST)) = it match {
          case (label, e) => label + "=" + convToStr(e, skipCnt)
        }
        "{" + coll_to_str(em, it_to_str) + "}"

      case AppExp(e1, e2) =>
        val str1 = convToStrWNP(needParTerm2, convToStr, e1, skipCnt)
        val strm = " "
        val str2 = convToStrWNP(needParTerm2App, convToStr, e2, skipCnt + str1.length() + strm.length())
        str1 + strm + str2

      case LtExp(e1, e2) =>
        val str1 = convToStrWNP(needParTerm0, convToStr, e1, skipCnt)
        val strm = " < "
        val str2 = convToStrWNP(needParTerm0, convToStr, e2, skipCnt + str1.length() + strm.length())
        str1 + strm + str2

      case PlusExp(e1, e2) =>
        val str1 = convToStrWNP(needParTerm1, convToStr, e1, skipCnt)
        val strm = " + "
        val str2 = convToStrWNP(needParTerm1Plus, convToStr, e2, skipCnt + str1.length() + strm.length())
        str1 + strm + str2

      case UMinExp(e) =>
        val str1 = "-"
        val str2 = convToStrWNP(needParTerm4, convToStr, e, skipCnt + str1.length)
        str1 + str2

      case CondExp(c, e1, e2) =>
        val strm1 = "if "
        val str1 = convToStrWNP(needNoPar, convToStr, c, skipCnt + strm1.length())
        val strm2 = " then" + newLine + indentStr
        val str2 = convToStrWNP(needNoPar, convToStr, e1, skipCnt + indentStr.length())
        val strm3 = newLine + "else" + newLine + indentStr
        val str3 = convToStrWNP(needNoPar, convToStr, e2, skipCnt + indentStr.length())
        strm1 + str1 + strm2 + str2 + strm3 + str3

      case LamExp(id, ty, e) =>
        val str1 = "\\" + id + ":" + convToTyStr(ty) + ". "
        val str2 = convToStrWNP(needNoPar, convToStr, e, skipCnt + str1.length())
        str1 + str2

      case LetExp(id, e1, e2) =>
        val str0 = "let " + id + " = "
        val str1 = convToStrWNP(needNoPar, convToStr, e1, skipCnt + str0.length())
        val str2 = " in" + newLine
        val str3 = convToStrWNP(needNoPar, convToStr, e2, skipCnt)
        str0 + str1 + str2 + str3

      case IsNilExp(e) => unary_to_str(needNoPar, "isnil", e)
      case HeadExp(e) => unary_to_str(needNoPar, "hd", e)
      case TailExp(e) => unary_to_str(needNoPar, "tl", e)

      case FixAppExp(e) => convToStr(AppExp(Variable("fix"), e), skipCnt)

      case ProjTupleExp(e: AST, i: Int) =>
        val str1 = convToStrWNP(needParTerm5, convToStr, e, skipCnt)
        val strm = "."
        val str2 = i.toString()
        str1 + strm + str2

      case ProjRecordExp(e: AST, l: String) =>
        val str1 = convToStrWNP(needParTerm5, convToStr, e, skipCnt)
        val strm = "."
        val str2 = l
        str1 + strm + str2

      // contracts cons to list print as far as possible
      // (needParTerm2ConsLeft, needParTerm2Cons)
      case ConsExp(eh: AST, et: AST) =>
        def toConsList(acc: List[AST], e: AST): Option[(List[AST], ASTTY)] = e match {
          case NilExp(ty) => Some((acc, ty))
          case ConsExp(eh1: AST, et1: AST) => toConsList(eh1::acc, et1)
          case _ => None
        }
        toConsList(List(), x) match {
          case None =>
            val str1 = convToStrWNP(needParTerm3Cons, convToStr, eh, skipCnt)
            val strm = "::"
            val str2 = convToStrWNP(needParTerm3, convToStr, et, skipCnt)
            str1 + strm + str2
          case Some((el, ty)) =>
            def it_to_str(e: AST) = convToStr(e, skipCnt)
            "[" + coll_to_str(el.reverse, it_to_str) + " | " + convToTyStr(ty) + " ]"
        }

      case _ =>
        throw new Exception("Cannot print AST element: " + x)
    }
  }

  /* function to apply the AST printer */
  def apply(x: AST): Either[PrintingError, Unit] = {
    try {
      println("==========================================================")
      println("AST")
      println("==========================================================")
      println(convToStr(x))
      println("==========================================================")
      Right(())
    } catch {
      case ex: Exception => Left(PrintingError(ex.getMessage()))
    }
  }
}
