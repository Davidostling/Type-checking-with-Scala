package simpret.typechecker

import simpret.parser._


abstract class TypecheckerException(val message: String, val x: AST,
                                    private val cause: Throwable = None.orNull)
  extends Exception(message, cause)

final class UnknownASTTypecheckerException(val xe: AST,
                                           private val cause: Throwable = None.orNull)
  extends TypecheckerException("Unknown AST node class", xe, cause)

final class NotExpectedTypeTypecheckerException(val ty_str: String, val xe: AST,
                                                private val cause: Throwable = None.orNull)
  extends TypecheckerException(ty_str + " expected", xe, cause)

final class VarUnboundTypecheckerException(val xe: AST,
                                            private val cause: Throwable = None.orNull)
  extends TypecheckerException("Variable unbound", xe, cause)

final class ApplicationArgumentTypecheckerException(val ty_param: ASTTY, val ty_arg: ASTTY, val xe: AST,
                                                    private val cause: Throwable = None.orNull)
  extends TypecheckerException("Argument type (" + ASTPrinter.convToTyStr(ty_arg) +
    ") in application does not match parameter type (" + ASTPrinter.convToTyStr(ty_param) + ")", xe, cause)

final class BranchMismatchTypecheckerException(val ty1: ASTTY, val ty2: ASTTY, val xe: AST,
                                               private val cause: Throwable = None.orNull)
  extends TypecheckerException("Types of the branches do not match ("
    + ASTPrinter.convToTyStr(ty1) + " and " + ASTPrinter.convToTyStr(ty2) + ")", xe, cause)

final class ArrowNotSameTypecheckerException(val ty_param: ASTTY, val ty_res: ASTTY, val xe: AST,
                                             private val cause: Throwable = None.orNull)
  extends TypecheckerException("ARROW TYPE expected, where parameter type ("
    + ASTPrinter.convToTyStr(ty_param) + ") and result type (" + ASTPrinter.convToTyStr(ty_res) + ") match", xe, cause)

final class ConsMismatchTypecheckerException(val eh_ty: ASTTY, val et_lty: ASTTY, val xe: AST,
                                             private val cause: Throwable = None.orNull)
  extends TypecheckerException("Type of head ("+ ASTPrinter.convToTyStr(eh_ty) +
    ") does not match list type of tail ("+ ASTPrinter.convToTyStr(et_lty) +") in cons", xe, cause)

final class ProjectionTooSmallTypecheckerException(val xe: AST,
                                            private val cause: Throwable = None.orNull)
  extends TypecheckerException("The projection index is too small, it has to be at least 1", xe, cause)

final class ProjectionTooBigTypecheckerException(val length: Int, val xe: AST,
                                 private val cause: Throwable = None.orNull)
  extends TypecheckerException("The projection index is too big, it has to be between 1 and the tuple size ("+ length +")", xe, cause)

final class ProjectionNotAFieldTypecheckerException(val l: String, val xe: AST,
                                 private val cause: Throwable = None.orNull)
  extends TypecheckerException("The label " + l + " is not a field of the record", xe, cause)

