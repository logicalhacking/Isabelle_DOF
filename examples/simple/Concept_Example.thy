theory Concept_Example
  imports "../../ontologies/Conceptual"
begin

open_monitor*[struct::M]  

section*[a::A, x = "''alpha''"] \<open> AAA \<close>


text*[c1::C, x = "''beta''"] \<open> C \<close>
text*[d ::D, x = "''gamma''"] \<open> D \<close>
text*[c2 ::C, x = "''delta''"] \<open> C \<close>

section*[f::F]  \<open> D \<close>
  
close_monitor*[struct]

  
end 
  