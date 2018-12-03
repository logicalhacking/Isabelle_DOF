chapter\<open>Setting and modifying attributes of doc-items\<close>

theory Concept_ExampleInvariant
  imports "../../ontologies/Conceptual" (* we use the generic "Conceptual" ontology *)
begin

print_doc_classes
print_doc_items

ML\<open>fun check_A_invariant oid ctxt = 
      let val term =  AttributeAccess.calc_attr_access ctxt "x" oid @{here}
          val (@{typ "int"},x_value) = HOLogic.dest_number term
      in  if x_value > 5 then error("class A invariant violation") else true end
\<close>

text\<open>Watch out: The current programming interface to document class invariants is pretty low-level:
\<^item> No inheritance principle
\<^item> No high-level notation in HOL
\<^item> Typing on ML level is assumed to be correct.
The implementor of an ontology must know what he does ...
\<close>
setup\<open>DOF_core.update_class_invariant "Conceptual.A" (fn oid => 
                                                       fn ctxt => 
                                                        (writeln ("sample echo : "^oid); true))\<close>

section*[b::A, x = "5"] \<open> Lorem ipsum dolor sit amet, ... \<close>

setup\<open>DOF_core.update_class_invariant "Conceptual.A" check_A_invariant\<close>

(* test : should fail :
section*[c::A, x = "6"] \<open> Lorem ipsum dolor sit amet, ... \<close>
*)

(* to test : updates *)

(* to do: trace example *)

end 
  