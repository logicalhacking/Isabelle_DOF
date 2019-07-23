(*<*)
theory "00_Frontmatter"
  imports "Isabelle_DOF.technical_report"
begin

open_monitor*[this::report] 

(*>*)

title*[title::title]\<open>Isabelle/DOF\<close> 
subtitle*[subtitle::subtitle]\<open>User and Implementation Manual\<close> 
text*[adb:: author,
      email="\<open>a.brucker@exeter.ac.uk\<close>",
      orcid="\<open>0000-0002-6355-1200\<close>",
      http_site="\<open>https://www.brucker.ch/\<close>",
      affiliation="\<open>University of Exeter, Exeter, UK\<close>"]\<open>Achim D. Brucker\<close>
text*[bu::author,
      email       = "\<open>wolff@lri.fr\<close>",
      affiliation = "\<open>Université Paris-Saclay, LRI, Paris, France\<close>"]\<open>Burkhart Wolff\<close>
 

text*[abs::abstract,
      keywordlist="[''Ontology'',''Ontological Modeling'',''Isabelle/DOF'']"]\<open>
While Isabelle is mostly known as part of Isabelle/HOL (an interactive 
theorem prover), it actually provides a framework for developing a wide
spectrum of applications. A particular strength
of the Isabelle framework is the combination of text editing, formal verification,
and code generation. 

Up to now, Isabelle's document preparation system lacks a mechanism
for ensuring the structure of different document types (as, e.g.,
required in certification processes) in general and, in particular,
a \<^emph>\<open>systematic\<close> mechanism for linking informal and formal parts of a document. 

In this paper, we present \isadof, a novel Document Ontology Framework 
on top of Isabelle. \isadof allows for conventional typesetting
\<^emph>\<open>as well\<close> as formal development. We show how to model document
 ontologies inside \isadof, how to use the resulting meta-information 
for enforcing a certain document structure, and discuss ontology-specific IDE support. 
\<close>


(*<*) 
end
(*>*) 
  