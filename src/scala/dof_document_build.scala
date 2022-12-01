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

package isabelle.dof

import isabelle._


object DOF_Document_Build
{
  class Engine extends Document_Build.Bash_Engine("dof")
  {
    // override def use_build_script: Boolean = true

    override def prepare_directory(
      context: Document_Build.Context,
      dir: Path,
      doc: Document_Build.Document_Variant): Document_Build.Directory =
    {
      val options = DOF.options(context.options)
      val latex_output = new Latex_Output(options)
      val directory = context.prepare_directory(dir, doc, latex_output)

      // produced by alternative presentation hook (workaround for missing Toplevel.present_theory)
      for {
        name <- context.document_theories.iterator
        entry <- context.session_context.get(name.theory, Export.DOCUMENT_LATEX + "_dof")
      } {
        val path = Path.basic(Document_Build.tex_name(name))
        val xml = YXML.parse_body(entry.text)
        File.content(path, xml).output(latex_output(_, file_pos = path.implode_symbolic))
          .write(directory.doc_dir)
      }
      val isabelle_dof_dir = context.session_context.sessions_structure(DOF.session).dir

      // copy Isabelle/DOF LaTeX templates
      val template_dir = isabelle_dof_dir + Path.explode("document-templates")
      // TODO: error handling in case 1) template does not exist or 2) root.tex does already exist
      val template = Long_Name.base_name(options.string("dof_template"))
      Isabelle_System.copy_file(
        template_dir + Path.explode("root-" + template + ".tex"),
        directory.doc_dir + Path.explode("root.tex"))

      // copy Isabelle/DOF LaTeX styles
      List(Path.explode("DOF/latex"), Path.explode("ontologies"))
        .flatMap(dir =>
          File.find_files((isabelle_dof_dir + dir).file,
            file => file.getName.endsWith(".sty"), include_dirs = true))
        .foreach(sty => Isabelle_System.copy_file(sty, directory.doc_dir.file))

      // create ontology.sty
      val ontologies = DOF.explode_ontologies(options.string("dof_ontologies"))
      File.write(directory.doc_dir + Path.explode("ontologies.tex"),
        ontologies.map(name => "\\usepackage{DOF-" + Long_Name.base_name(name) + "}\n").mkString)

      // create dof-config.sty
      File.write(directory.doc_dir + Path.explode("dof-config.sty"), """
\newcommand{\isabelleurl}{""" + DOF.isabelle_url + """}
\newcommand{\dofurl}{""" + DOF.url + """}
\newcommand{\dof@isabelleversion}{""" + DOF.isabelle_version + """}
\newcommand{\isabellefullversion}{""" + DOF.isabelle_version + """\xspace}
\newcommand{\dof@version}{""" + DOF.version + """}
\newcommand{\dof@artifacturl}{""" + DOF.artifact_dir + """}
\newcommand{\doflatestversion}{""" + DOF.latest_version + """}
\newcommand{\isadoflatestdoi}{""" + DOF.latest_doi + """}
\newcommand{\isadofgenericdoi}{""" + DOF.generic_doi + """}
\newcommand{\isabellelatestversion}{""" + DOF.latest_isabelle + """}
""")
      directory
    }
  }

  class Latex_Output(options: Options) extends Latex.Output(options)
  {
    override def latex_environment(
      name: String,
      body: Latex.Text,
      optional_argument: String = ""): Latex.Text =
    {
      XML.enclose(
        "\n\\begin{" + name + "}" + optional_argument + "\n",
        "\n\\end{" + name + "}", body)
    }
  }
}
