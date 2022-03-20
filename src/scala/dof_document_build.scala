/*  Author:     Makarius

Build theory document (PDF) from session database.
*/

package isabelle_dof

import isabelle._


object DOF_Document_Build
{
  class Engine extends Document_Build.Bash_Engine("dof")
  {
    override def use_build_script: Boolean = true

    override def prepare_directory(
      context: Document_Build.Context,
      dir: Path,
      doc: Document_Build.Document_Variant): Document_Build.Directory =
    {
      val latex_output = new Latex_Output(context.options)
      val directory = context.prepare_directory(dir, doc, latex_output)

      // produced by alternative presentation hook (workaround for missing Toplevel.present_theory)
      for (name <- context.document_theories) {
        val path = Path.basic(Document_Build.tex_name(name))
        val xml =
          YXML.parse_body(context.get_export(name.theory, Export.DOCUMENT_LATEX + "_dof").text)
        if (xml.nonEmpty) {
          File.Content(path, xml).output(latex_output(_, file_pos = path.implode_symbolic))
            .write(directory.doc_dir)
        }
      }

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
