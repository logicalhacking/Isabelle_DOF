/*
 * Copyright (c) 
 *               2021-2022 The University of Exeter. 
 *               2021-2022 The University of Paris-Saclay. 
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
 * BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */


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
    template: String = "",
    ontologies: List[String] = List(),
    progress: Progress = new Progress): Unit =
  {
    Isabelle_System.make_directory(session_dir)

    val name = proper_string(session_name) getOrElse session_dir.absolute_file.getName
    val parent = proper_string(session_parent) getOrElse Isabelle_System.getenv("ISABELLE_LOGIC")

    val root_path = session_dir + Sessions.ROOT
    if (root_path.file.exists) error("Cannot overwrite existing " + root_path)

    val document_path = session_dir + Path.explode("document")
    if (document_path.file.exists) error("Cannot overwrite existing " + document_path)

    progress.echo("\nPreparing session " + quote(name) + " in " + session_dir)


    /* ROOT */

    progress.echo("  creating " + root_path)

    File.write(root_path,
      "session " + Mkroot.root_name(name) + " = " + Mkroot.root_name(parent) + """ +
  options [document = pdf, document_output = "output", document_build = dof, dof_ontologies = """" 
       + ontologies.mkString(" ") + """", dof_template = """ + Mkroot.root_name(template) 
       + """, document_comment_latex=true] 
(*theories [document = false]
    A
    B*)
  theories
    """ + Mkroot.root_name(name) + """    
  document_files
    "preamble.tex"
""")

    val thy = session_dir + Path.explode(name+".thy")
    progress.echo("  creating " + thy)
    File.write(thy,
      "theory\n  " + name + "\nimports\n  " + ontologies.mkString("\n  ") +  """
begin
  
end
""")



    val preamble_tex = session_dir + Path.explode("document/preamble.tex")
    progress.echo("  creating " + preamble_tex)
    Isabelle_System.make_directory(preamble_tex.dir)
    File.write(preamble_tex,"""%% This is a placeholder for user-specific configuration and packages.""")

    /* Mercurial repository */

    if (init_repos) {
      progress.echo("  \nInitializing Mercurial repository " + session_dir)

      val hg = Mercurial.init_repository(session_dir)

      val hg_ignore = session_dir + Path.explode(".hgignore")
      File.write(hg_ignore,
"""syntax: glob

*~
*.marks
*.orig
*.rej
.DS_Store
.swp

syntax: regexp

^output/
""")

      hg.add(List(root_path, preamble_tex, hg_ignore))
    }


    /* notes */

    {
      val print_dir = session_dir.implode
      progress.echo("""
Now use the following command line to build the session:

  isabelle build -D """ +
        (if (Bash.string(print_dir) == print_dir) print_dir else quote(print_dir)) + "\n")
    }
  }


  /** Isabelle tool wrapper **/

  val isabelle_tool = Isabelle_Tool("dof_mkroot", "prepare session root directory for Isabelle/DOF",
    Scala_Project.here, args =>
  {
    var init_repos = false
    var help = false
    var session_name = ""
    var session_parent = "Isabelle_DOF"
    var ontologies:List[String] = List()
    var template = session_parent + ".scrartcl"
    val default_ontologies = List(session_parent+".scholarly_paper")

    val getopts = Getopts("""
Usage: isabelle dof_mkroot [OPTIONS] [DIRECTORY]

  Options are:
    -I           init Mercurial repository and add generated files
    -n NAME      alternative session name (default: directory base name)
    -o ONTOLOGY  ontology (default: scholarly_paper)
    -t TEMPLATE  tempalte (default: scrartcl)

  Prepare session root directory (default: current directory).
""",
      "I" ->  (arg => init_repos = true),
      "n:" -> (arg => session_name = arg),
      "o:"  -> (arg => ontologies = ontologies :+ arg),
      "t:"  -> (arg => template = arg),
      "h"  -> (arg => help = true)
    )

    val more_args = getopts(args)

    ontologies = if (ontologies.isEmpty) default_ontologies else ontologies
  
    if (help) {getopts.usage()} else {()}
    val session_dir =
      more_args match {
        case Nil => Path.current
        case List(dir) => Path.explode(dir)
        case _ => getopts.usage()
      }

    mkroot(session_parent=session_parent, session_name = session_name, session_dir = session_dir, init_repos = init_repos,
      ontologies = ontologies, template = template, progress = new Console_Progress)
  })
}
