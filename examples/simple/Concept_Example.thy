theory Concept_Example
  imports "../../ontologies/Conceptual"
begin

open_monitor*[struct::M]  

section*[a::A, x = "''alpha''"] \<open> Lorem ipsum dolor sit amet, ... \<close>

text*[c1::C, x = "''beta''"] 
\<open> ... suspendisse non arcu malesuada mollis, nibh morbi, ...  \<close>


text*[d::D, a1 = "X3"] 
\<open> ... phasellus amet id massa nunc, pede suscipit repellendus, ... @{docitem_ref \<open>c1\<close>} @{thm "refl"}\<close>


update_instance*[d::D, a1 := X2]

text{* ... in ut tortor ... @{docitem_ref \<open>a\<close>} ... @{A \<open>a\<close>}*}  
  
(* text{* ... in ut tortor ... @{docitem_ref \<open>a\<close>} ... @{C \<open>a\<close>}*}  *)
  
text*[c2::C, x = "''delta''"] 
\<open> ... in ut tortor eleifend augue pretium consectetuer.  \<close>

section*[f::F] \<open> Lectus accumsan velit ultrices, ... }\<close>
  
theorem some_proof : "P" sorry
    
update_instance*[f,r:="[@{thm ''some_proof''}]"]

text{* ..., mauris amet, id elit aliquam aptent id,  ... *}
  
update_instance*[f,b:="{(@{docitem  ''a''}::A,@{docitem  ''c1''}::C), 
                        (@{docitem  ''a''},@{docitem  ''c1''})}"] 
  
close_monitor*[struct]

  
end 
  