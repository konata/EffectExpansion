ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "3.3.4"

lazy val root = (project in file("."))
  .settings(
    name := "EffectExpansion",
    idePackagePrefix := Some("side.effect.free")
  )

libraryDependencies += "org.soot-oss"    %  "soot"          % "4.2.1"
libraryDependencies += "org.slf4j"       %  "slf4j-simple"  % "2.0.9"
libraryDependencies += "org.scala-graph" %% "graph-core"    % "2.0.1"
libraryDependencies += "org.scala-graph" %% "graph-dot"     % "2.0.0"
libraryDependencies += "org.scalatest"   %% "scalatest"     % "3.2.17" % Test
libraryDependencies += "org.json4s"      %% "json4s-native" % "4.0.6"

javacOptions ++= Seq(
  "-source", "1.8",
  "-target", "1.8"
)
