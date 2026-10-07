import isabelle.*

 
object ExportNativeMetadata {
  def main(args: Array[String]): Unit = {
    require(args.length >= 2, "output directory and session names required")
    val store = Store(Options.init())
    for (session <- args.drop(1)) {
      Export.export_files(store, session, Path.explode(args(0)) + Path.basic(session),
        export_patterns = List("*:lctr-metadata/facts.json"))
      println(session)
    }
  }
}
