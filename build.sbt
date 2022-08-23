name := "simpret"

version := "0.1"

scalaVersion := "3.1.1"


libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "2.1.1"



// https://www.scala-sbt.org/1.x/docs/Triggered-Execution.html
// https://www.scala-sbt.org/1.0/docs/Howto-Triggered.html
watchSources += baseDirectory.value / "src" / "input.sint"
//watchSources += baseDirectory.value / "src" / "test" / "sint" / "lab3"



// https://docs.scala-lang.org/getting-started-sbt-track/testing-scala-with-sbt-on-the-command-line.html
libraryDependencies += "org.scalatest" %% "scalatest" % "3.2.11" % Test
