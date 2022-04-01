/*  Author:     Makarius

Prepare session root directory for Isabelle/DOF.
*/

package isabelle_dof

import isabelle._


object DOF_Mkroot
{
  /** mkroot **/

  def mkroot(
    session_name: String = "",
    session_dir: Path = Path.current,
    session_parent: String = "",
    init_repos: Boolean = false,
    title: String = "",
    author: String = "",
    progress: Progress = new Progress): Unit =
  {
    Mkroot.mkroot(session_name = session_name, session_dir = session_dir,
      session_parent = session_parent, init_repos = init_repos,
      title = title, author = author, progress = progress)
  }



  /** Isabelle tool wrapper **/

  val isabelle_tool = Isabelle_Tool("dof_mkroot", "prepare session root directory for Isabelle/DOF",
    Scala_Project.here, args =>
  {
    var author = ""
    var init_repos = false
    var title = ""
    var session_name = ""

    val getopts = Getopts("""
Usage: isabelle dof_mkroot [OPTIONS] [DIRECTORY]

  Options are:
    -A LATEX     provide author in LaTeX notation (default: user name)
    -I           init Mercurial repository and add generated files
    -T LATEX     provide title in LaTeX notation (default: session name)
    -n NAME      alternative session name (default: directory base name)

  Prepare session root directory (default: current directory).
""",
      "A:" -> (arg => author = arg),
      "I" -> (arg => init_repos = true),
      "T:" -> (arg => title = arg),
      "n:" -> (arg => session_name = arg))

    val more_args = getopts(args)

    val session_dir =
      more_args match {
        case Nil => Path.current
        case List(dir) => Path.explode(dir)
        case _ => getopts.usage()
      }

    mkroot(session_name = session_name, session_dir = session_dir, init_repos = init_repos,
      author = author, title = title, progress = new Console_Progress)
  })
}
