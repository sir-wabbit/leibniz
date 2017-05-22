val testLibraries = List(
  "org.scalacheck" %% "scalacheck" % "1.13.5" % "test",
  "org.typelevel" %% "discipline" % "0.7.3" % "test",
  "org.scalatest" %% "scalatest" % "3.0.3" % "test")

val catsLibraries = List(
  "org.typelevel" %% "algebra" % "0.7.0",
  "org.typelevel" %% "cats" % "0.9.0")

val simulacrumLibrary = List(
  "com.github.mpilquist" %% "simulacrum" % "0.10.0")

lazy val commonSettings = List(
  addCompilerPlugin("org.spire-math" %% "kind-projector" % "0.9.3"),
  addCompilerPlugin("org.scalamacros" % "paradise" % "2.1.0" cross CrossVersion.full),
  organization := "com.alexknvl",
  version := "0.3.1",
  scalaVersion := "2.12.1",
  licenses += ("MIT", url("http://opensource.org/licenses/MIT")),
  scalacOptions ++= List(
    "-deprecation", "-unchecked", "-feature",
    "-encoding", "UTF-8",
    "-language:existentials",
    "-language:higherKinds",
    "-language:implicitConversions",
    "-Ypartial-unification",
    "-Yno-adapted-args", "-Ywarn-dead-code",
    "-Ywarn-numeric-widen", "-Xfuture"),
  resolvers ++= List(
    Resolver.sonatypeRepo("snapshots"),
    Resolver.sonatypeRepo("releases")),
  libraryDependencies ++= testLibraries,
  wartremoverWarnings ++= Warts.all
)

lazy val root = (project in file("."))
  .settings(name := "leibniz")
  .settings(commonSettings: _*)
  .settings(libraryDependencies ++= catsLibraries)
