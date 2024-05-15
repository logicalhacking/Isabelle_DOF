theory
  "template-scrreprt-modern"
imports
  "Isabelle_DOF-Ontologies.document_templates"
   Isabelle_DOF.technical_report
begin

list_templates
use_template "scrreprt-modern"
list_ontologies
use_ontology "technical_report"

title* [tit::title]\<open>Formal Verification of Security Protocols\<close>
author*[alice, email       = "\<open>alice@example.com\<close>",
               http_site   = "\<open>https://example.com/alice\<close>",
               affiliation = "\<open>Wonderland University\<close>"]\<open>Alice\<close>  
author*[bob,   email       = "\<open>bob@example.com\<close>",
               http_site   = "\<open>https://example.com/bob\<close>",
               affiliation = "\<open>Wonderland University\<close>"]\<open>Bob\<close>  

end
