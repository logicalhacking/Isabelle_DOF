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
  }
}
