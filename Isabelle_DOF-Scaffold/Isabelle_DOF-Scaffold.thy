theory
  "Isabelle_DOF-Scaffold"
imports
   Isabelle_DOF.scholarly_paper
begin

list_templates
use_template "scrartcl"
list_ontologies
use_ontology "scholarly_paper"

title* [tit::title]\<open>Formal Verification of Security Protocols\<close>
author*[alice, email       = "\<open>alice@example.com\<close>",
               http_site   = "\<open>https://example.com/alice\<close>",
               affiliation = "\<open>Wonderland University\<close>"]\<open>Alice\<close>  
author*[bob,   email       = "\<open>bob@example.com\<close>",
               http_site   = "\<open>https://example.com/bob\<close>",
               affiliation = "\<open>Wonderland University\<close>"]\<open>Bob\<close>  

end
