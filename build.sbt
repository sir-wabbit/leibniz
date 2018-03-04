addCompilerPlugin("org.scalamacros" % "paradise_2.12.4" % "2.1.0")

autoCompilerPlugins := true

addCompilerPlugin("com.lihaoyi" %% "acyclic" % "0.1.7")

val testLibraries = List(
  "org.scalacheck" %% "scalacheck" % "1.13.5" % "test",
  "org.typelevel" %% "discipline" % "0.8" % "test",
  "org.scalatest" %% "scalatest" % "3.0.4" % "test")

val catsLibraries = List(
  "org.typelevel" %% "cats-core" % "1.0.0-MF")

lazy val commonSettings = List(
  addCompilerPlugin("org.spire-math" %% "kind-projector" % "0.9.4"),
  organization      := "com.alexknvl",
  version           := "0.13.0-SNAPSHOT",
  scalaVersion      := "2.12.4-bin-typelevel-4",
  scalaOrganization := "org.typelevel",
  licenses += ("MIT", url("http://opensource.org/licenses/MIT")),
  scalacOptions ++= List(
    "-deprecation",
    "-encoding", "UTF-8",
    "-explaintypes",
    "-Yrangepos",
    "-feature",
    "-Xfuture",
    "-Yliteral-types",
    "-Ypartial-unification",
    "-language:existentials",
    "-language:higherKinds",
    "-language:implicitConversions",
    "-language:experimental.macros",
    "-unchecked",
    "-Yno-adapted-args",
    "-opt-warnings",
    "-Xlint:_,-type-parameter-shadow",
    "-Xsource:2.13",
    "-Ywarn-dead-code",
    "-Ywarn-extra-implicit",
    "-Ywarn-inaccessible",
    "-Ywarn-infer-any",
    "-Ywarn-nullary-override",
    "-Ywarn-nullary-unit",
    "-Ywarn-numeric-widen",
    "-Ywarn-unused:_,-imports",
    "-Ywarn-value-discard",
    "-opt:l:inline",
    "-opt-inline-from:<source>"),
  resolvers ++= List(
    Resolver.sonatypeRepo("snapshots"),
    Resolver.sonatypeRepo("releases")),
  libraryDependencies ++= testLibraries
//  wartremoverErrors ++= List(Wart.AsInstanceOf)
)

val macroCompatVersion = "1.1.1"
val macroParadiseVersion = "2.1.0"

lazy val leibnizMacros = (project in file("./macros/"))
  .settings(name := "leibniz-macros")
  .settings(commonSettings: _*)
  .settings(libraryDependencies ++= Seq(
    scalaOrganization.value % "scala-compiler" % scalaVersion.value,
    "org.typelevel" %% "macro-compat" % macroCompatVersion))

lazy val root = (project in file("."))
  .settings(name := "leibniz")
  .settings(commonSettings: _*)
//  .settings(libraryDependencies ++= catsLibraries)
  .settings(libraryDependencies ++= Seq(
    scalaOrganization.value % "scala-compiler" % scalaVersion.value,
    "org.typelevel" %% "macro-compat" % macroCompatVersion))
  .dependsOn(leibnizMacros)
