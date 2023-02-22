(*<*)
theory "document_setup"
  imports
  "Isabelle_DOF.technical_report"
  "Isabelle_DOF-Ontologies.CENELEC_50128"
begin

use_template "scrreprt-modern"
use_ontology "Isabelle_DOF.technical_report" and "Isabelle_DOF-Ontologies.CENELEC_50128"

(*>*)

title*[title::title]         \<open>Isabelle/DOF\<close>
subtitle*[subtitle::subtitle]\<open>Ontologies\<close>

(*<*)
end
(*>*)
