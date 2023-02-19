(*<*)
theory "document_setup"
  imports
    "Isabelle_DOF.technical_report"
begin

use_template "scrreprt-modern"
use_ontology "technical_report"
(*>*)

title*[title::title]         \<open>Isabelle/DOF\<close>
subtitle*[subtitle::subtitle]\<open>Ontologies\<close>

(*<*)
end
(*>*)
