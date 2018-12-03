chapter\<open>Setting and modifying attributes of doc-items\<close>

theory Concept_Example
  imports "../../ontologies/Conceptual" (* we use the generic "Conceptual" ontology *)
begin

text\<open>@{theory Conceptual} provides a monitor @{typ M} enforcing a particular document structure.
     Here, we say: From now on, this structural rules are respected wrt. all doc\_classes M is
     enabled for.\<close>
open_monitor*[struct::M]  

section*[a::A, x = "3"] \<open> Lorem ipsum dolor sit amet, ... \<close>

text*[c1::C, x = "''beta''"] \<open> ... suspendisse non arcu malesuada mollis, nibh morbi, ...  \<close>

text*[d::D, a1 = "X3"] \<open> ... phasellus amet id massa nunc, pede suscipit repellendus, 
                         ... @{docitem \<open>c1\<close>} @{thm "refl"}\<close>


update_instance*[d::D, a1 := X2]

text\<open> ... in ut tortor ... @{docitem \<open>a\<close>} ... @{A \<open>a\<close>}\<close>  
    
text*[c2::C, x = "''delta''"]  \<open> ... in ut tortor eleifend augue pretium consectetuer.  \<close>

section*[f::F] \<open> Lectus accumsan velit ultrices, ... }\<close>
  
theorem some_proof : "P" sorry

text\<open>This is an example where we add a theorem into a kind of "result-list" of the doc-item f.\<close>
update_instance*[f::F,r:="[@{thm ''Concept_Example.some_proof''}]"]

text\<open> ..., mauris amet, id elit aliquam aptent id,  ... @{docitem \<open>a\<close>} \<close>

text\<open>Here we add and maintain a link that is actually modeled as m-to-n relation ...\<close>
update_instance*[f::F,b:="{(@{docitem  ''a''}::A,@{docitem  ''c1''}::C), 
                           (@{docitem  ''a''},   @{docitem  ''c2''})}"] 
  
close_monitor*[struct]

text\<open>And the trace of the monitor is:\<close>
ML\<open>@{trace_attribute struct}\<close>

print_doc_classes
print_doc_items

ML\<open>

\<close>

setup\<open>DOF_core.update_class_invariant "Conceptual.A" (fn thy => (writeln "ZZZ"; true))\<close>

section*[b::A, x = "5"] \<open> Lorem ipsum dolor sit amet, ... \<close>


end 
  