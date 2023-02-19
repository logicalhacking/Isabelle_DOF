(*************************************************************************
 * Copyright (C) 
 *               2019      The University of Exeter 
 *               2018-2019 The University of Paris-Saclay
 *               2018      The University of Sheffield
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

chapter\<open>Setting and modifying attributes of doc-items\<close>

theory 
  Concept_Example_Low_Level_Invariant
imports 
  "Isabelle_DOF-Ontologies.Conceptual" (* we use the generic "Conceptual" ontology *)
begin

section\<open>Example: Standard Class Invariant\<close>

text\<open>Status:\<close>
print_doc_classes
print_doc_items


text\<open>Watch out: The current programming interface to document class invariants is pretty low-level:
\<^item> No inheritance principle
\<^item> No high-level notation in HOL
\<^item> Typing on ML level is assumed to be correct.
The implementor of an ontology must know what he does ...
\<close>

text\<open>Setting a sample invariant, which simply produces some side-effect:\<close>
setup\<open>
fn thy =>
let val ctxt = Proof_Context.init_global thy
    val binding = DOF_core.binding_from_onto_class_pos "A" thy
in DOF_core.add_ml_invariant binding (fn oid =>
                                         fn {is_monitor = b} =>
                                            fn ctxt => 
                                               (writeln ("sample echo : "^oid); true)) thy end
\<close>

subsection*[b::A, x = "5"] \<open> Lorem ipsum dolor sit amet, ... \<close>


text\<open>Setting a sample invariant, referring to attribute value "x":\<close>
ML\<open>
fn thy =>
let fun check_A_invariant oid {is_monitor:bool} ctxt =
      let val term =  ISA_core.compute_attr_access ctxt "x" oid NONE @{here} 
          val (@{typ "int"},x_value) = HOLogic.dest_number term
    in  if x_value > 5 then error("class A invariant violation") else true end
    val binding = DOF_core.binding_from_onto_class_pos "A" thy
in DOF_core.add_ml_invariant binding check_A_invariant thy end
\<close>


subsection*[d::A, x = "4"] \<open> Lorem ipsum dolor sit amet, ... \<close>

(* test : update should not fail, invariant still valid *)
update_instance*[d::A, x += "1"]

(* test : with the next step it should fail : 
update_instance*[d::A, x += "1"]
*)

section\<open>Example: Monitor Class Invariant\<close>

text\<open>Of particular interest are class invariants attached to monitor classes: since the
latter manage a trace-attribute, a class invariant on them can assure a global form of consistency. 
It is possible to express:
\<^item> that attributes of a document element must satisfy particular conditions depending on the
  prior document elements --- as long they have been observed in a monitor.
\<^item> non-regular properties on a trace not expressible in a regular expression 
  (like balanced ness of opening and closing text elements)
\<^item> etc.
\<close>

text\<open>A simple global trace-invariant is expressed in the following: it requires
that instances of class C occur more often as those of class D; note that this is meant
to take sub-classing into account:
\<close>

ML\<open>
fn thy =>
let fun check_M_invariant oid {is_monitor} ctxt =
      let val term =  ISA_core.compute_attr_access ctxt "trace" oid NONE @{here} 
          fun conv (\<^Const>\<open>Pair \<^typ>\<open>doc_class rexp\<close> \<^typ>\<open>string\<close>\<close>
                      $ (\<^Const>\<open>Atom \<^typ>\<open>doc_class\<close>\<close> $ (\<^Const>\<open>mk\<close> $ s)) $ S) =
            let val s' =  DOF_core.get_onto_class_name_global' (HOLogic.dest_string s) thy
            in (s', HOLogic.dest_string S) end
          val string_pair_list = map conv (HOLogic.dest_list term) 
          val cid_list = map fst string_pair_list
          val ctxt' = Proof_Context.init_global(Context.theory_of ctxt)
          fun is_C x = DOF_core.is_subclass ctxt' x "Conceptual.C"
          fun is_D x = DOF_core.is_subclass ctxt' x "Conceptual.D"
          val n = length (filter is_C cid_list)
          val m = length (filter is_D cid_list)
      in  if m > n then error("class M invariant violation") else true end
    val binding = DOF_core.binding_from_onto_class_pos "M" thy
in DOF_core.add_ml_invariant binding check_M_invariant thy end
\<close>


section\<open>Example: Monitor Class Invariant\<close>

open_monitor*[struct::M]

subsection*[a::A, x = "3"]       \<open> Lorem ipsum dolor sit amet, ... \<close>

text*[c1::C, x = "''beta''"]     \<open> ... suspendisse non arcu malesuada mollis, nibh morbi, ...  \<close>

text*[d1::E, a1 = "X3"]          \<open> ... phasellus amet id massa nunc, pede suscipit repellendus, ... \<close>
    
text*[c2:: C, x = "''delta''"]   \<open> ... in ut tortor eleifend augue pretium consectetuer...  \<close>

subsection*[f::E]                \<open> Lectus accumsan velit ultrices, ... }\<close>

(*
section*[f2::E]                  \<open> Lectus accumsan velit ultrices, ... }\<close>
*)

ML\<open>val ctxt = @{context}
   val term = ISA_core.compute_attr_access 
                  (Context.Proof ctxt) "trace" "struct" NONE @{here} ;
   fun conv (Const(@{const_name "Pair"},_) $ Const(s,_) $ S) = (s, HOLogic.dest_string S)
   fun conv' (\<^Const>\<open>Pair \<^typ>\<open>doc_class rexp\<close> \<^typ>\<open>string\<close>\<close>
                      $ (\<^Const>\<open>Atom \<^typ>\<open>doc_class\<close>\<close> $ (\<^Const>\<open>mk\<close> $ s)) $ S) =
     let val s' =  DOF_core.get_onto_class_name_global' (HOLogic.dest_string s)
                                                                    (Proof_Context.theory_of ctxt)
     in (s', HOLogic.dest_string S) end
   val string_pair_list = map conv' (HOLogic.dest_list term)
  \<close>


close_monitor*[struct]


end 
  