(*<*)
theory "Isabelle_DOF-Unit-Tests_document"
  imports
    "Isabelle_DOF.technical_report"
    "Isabelle_DOF-Ontologies.CENELEC_50128"
  
begin

use_template "scrreprt-modern"
use_ontology "technical_report" and "Isabelle_DOF-Ontologies.CENELEC_50128"

title*[title::title]         \<open>The Isabelle/DOF Implementation\<close>
subtitle*[subtitle::subtitle]\<open>The Unit-Test Suite\<close>


(*>*)
(* BUG: Invariant checking should not go across sessions boundaries.

title*[title::title]         \<open>Isabelle/DOF\<close>
subtitle*[subtitle::subtitle]\<open>Unit Tests\<close>
*)
(*<*)
end
(*>*)
