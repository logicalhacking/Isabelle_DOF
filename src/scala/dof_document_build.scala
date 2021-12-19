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
      context.prepare_directory(dir, doc, new Latex_Output(context.options))
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
