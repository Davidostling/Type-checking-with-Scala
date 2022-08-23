## Scala laboration

A lambda calculus laboration me and a lab partner completed at KTH using typechecking with Scala.
The instructions for the lab are provided in the lab-instructinons.pdf file. 

### How to run the code with the provided test cases.

1. Clone the repository.
2. Install JDK (version **8** or above).
3. Install sbt, following the instructions on https://www.scala-sbt.org/1.x/docs/Setup.html.
   It is recommended to use sbt version **1.6.0** or above.
4. In the root directory of the project:
   - Use `sbt compile` to compile the main project.
     sbt will fetch the required Scala version (currently 3.1.1) automatically.
   - Use `sbt "run test.sint"` to run your interpreter on an existing file `test.sint`.
   - Use `sbt test` to run the unit tests.
   - Use `sbt clean` to clean up all generated files.
   - Alternatively, you can use `sbt` to enter the interactive shell
     and run commands `compile`, `run test.sint`, `test`, and `clean` from there.
