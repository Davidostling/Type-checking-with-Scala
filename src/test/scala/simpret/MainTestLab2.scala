package simpret

import simpret.errors._
import simpret.parser._


class MainTestLab2 extends MainTestInterpreter {
  val filesStep = getListOfFiles("src/test/sint/lab2/steptests", List("sint")).sorted
  val filesFix = getListOfFiles("src/test/sint/lab2/fixpointtests", List("sint")).sorted
  val nottypable = getListOfFiles("src/test/sint/lab2/nottypable", List("sint")).sorted
  val notypecheck = getListOfFiles("src/test/sint/lab2/notypecheck", List("sint")).sorted

  filesStep.foreach { file =>
    test("step test " + file.getName()) {
      singleAutoTest(file)
    }
  }

  filesFix.foreach { file =>
    test("fixpoint test " + file.getName()) {
      fixAutoTest(file)
    }
  }

  nottypable.foreach { file =>
    test("typing test " + file.getName()) {
      singleAutoTypeTest(file)
    }
  }

  notypecheck.foreach { file =>
    test("fixpoint test w.o. type check " + file.getName()) {
      fixAutoTestNoTypeCheck(file)
    }
  }



  /*
  // this is how you add a test case
  test("TestCaseLab3 3 ABC") {
    // here you add the sub testcases
  }

  // this is how you add another test case
  test("TestCaseLab3 4 XYZ") {
    // here you add the corresponding sub testcases
  }
  */
}
