addCompilerPlugin("org.scalamacros" %% "paradise" % "2.1.0" cross CrossVersion.full)

val testLibraries = List(
  "org.scalacheck" %% "scalacheck" % "1.13.5" % "test",
  "org.typelevel" %% "discipline" % "0.8" % "test",
  "org.scalatest" %% "scalatest" % "3.0.4" % "test")

val catsLibraries = List(
  "org.typelevel" %% "cats-core" % "1.0.0-MF")

lazy val commonSettings = List(
  addCompilerPlugin("org.spire-math" %% "kind-projector" % "0.9.4"),
  organization      := "com.alexknvl",
  version           := "0.11.0-SNAPSHOT",
  scalaVersion      := "2.12.1",
  scalaOrganization := "org.typelevel",
  licenses += ("MIT", url("http://opensource.org/licenses/MIT")),
  scalacOptions ++= List(
    "-deprecation", "-unchecked", "-feature",
    "-encoding", "UTF-8",
    "-language:existentials",
    "-language:higherKinds",
    "-language:implicitConversions",
    "-language:experimental.macros",
    "-Yliteral-types",
    "-Ypartial-unification",
    "-Yno-adapted-args", "-Ywarn-dead-code",
    "-Ywarn-numeric-widen", "-Xfuture"),
  resolvers ++= List(
    Resolver.sonatypeRepo("snapshots"),
    Resolver.sonatypeRepo("releases")),
  libraryDependencies ++= testLibraries,
  wartremoverWarnings ++= Warts.all
)

val macroCompatVersion = "1.1.1"
val macroParadiseVersion = "2.1.0"

lazy val root = (project in file("."))
  .settings(name := "leibniz")
  .settings(commonSettings: _*)
  .settings(libraryDependencies ++= catsLibraries)
  .settings(libraryDependencies ++= Seq(
    scalaOrganization.value % "scala-compiler" % scalaVersion.value,
    "org.typelevel" %% "macro-compat" % macroCompatVersion))
