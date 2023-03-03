(*************************************************************************
 * Copyright (C) 
 *               2019-2023 The University of Exeter 
 *               2018-2023 The University of Paris-Saclay
 *               2018      The University of Sheffield
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

chapter\<open>Creating and Referencing Ontological Instances\<close>

theory 
  Concept_OntoReferencing
  imports 
  "Isabelle_DOF-Unit-Tests_document"
  "Isabelle_DOF-Ontologies.Conceptual" 
  "TestKit"
begin

section\<open>Test Purpose.\<close>
text\<open> Creation of ontological instances along the \<^theory>\<open>Isabelle_DOF-Ontologies.Conceptual\<close> 
Ontology. Emphasis is put on type-safe (ontologically consistent) referencing of text, code and
proof elements. Some tests cover also the critical cases concerning name spaces of oid's. \<close>

section\<open>Setting up a monitor.\<close>
text\<open>\<^theory>\<open>Isabelle_DOF-Ontologies.Conceptual\<close> provides a monitor \<^typ>\<open>M\<close>  enforcing a 
     particular document structure. Here, we say: From now on, this structural rules are 
     respected wrt. all \<^theory_text>\<open>doc_classes M\<close> is enabled for.\<close>

open_monitor*[struct::M]  

section\<open>Defining Text Elements and Referring to them... \<close>

text\<open> This uses elements of two ontologies, notably 
      \<^theory>\<open>Isabelle_DOF-Ontologies.Conceptual\<close> and \<^theory>\<open>Isabelle_DOF.Isa_COL\<close>.\<close>

(*<*)
title*[abbb::title, short_title="Some\<open>ooups.\<close>"]\<open>Lorem ipsum dolor sit amet ...\<close>
subtitle*[abbbb::subtitle, abbrev = "Some\<open>ooups-oups.\<close>"]\<open>Lorem ipsum dolor sit amet ...\<close>
chapter*[abbbbbb::A, x = "3"]   \<open> Lorem ipsum dolor sit amet ... \<close>
section*[a::A, x = "3"]         \<open> Lorem ipsum dolor sit amet, ... \<close>
subsection*[ab::A, x = "3"]     \<open> Lorem ipsum dolor sit amet, ... 
                                  As mentioned in the @{title \<open>abbb\<close>}... \<close> \<comment> \<open>old-style and ...\<close>
subsubsection*[abb::A, x = "3"] \<open> Lorem ipsum dolor sit amet, ... 
                                  As mentioned in the \<^title>\<open>abbb\<close>\<close>    \<comment> \<open>new-style references to
                                                                          ontological instances 
                                                                          assigned to text 
                                                                          elements ...\<close>
(*>*)



text\<open>Meta-Objects are typed, and references have to respect this : \<close>
(*<*)
text-assert-error[ac]\<open> \<^title>\<open>a\<close> \<close>    \<open>reference ontologically inconsistent\<close>
text-assert-error[ad]\<open> \<^title>\<open>abbbb\<close> \<close>\<open>reference ontologically inconsistent\<close> 
                       \<comment> \<open>erroneous reference: please consider class hierarchy!\<close>
(*>*)

text\<open>References to Meta-Objects can be forward-declared:\<close>

text-assert-error[ae1]\<open>@{C \<open>c1\<close>}\<close>\<open>Undefined instance:\<close>

declare_reference*[c1::C]     \<comment> \<open>forward declaration\<close>

text\<open>@{C \<open>c1\<close>} \<close>              \<comment> \<open>THIS IS A  BUG !!! OVERLY SIMPLISTIC BEHAVIOUR. THIS SHOULD FAIL! \<close>

text\<open>@{C (unchecked) \<open>c1\<close>} \<close>  \<comment> \<open>THIS SHOULD BE THE CORRECT BEHAVIOUR! \<close>


text*[c1::C, x = "''beta''"] \<open> ... suspendisse non arcu malesuada mollis, nibh morbi, ...  \<close>

text-assert-error[c1::C, x = "''gamma''"] 
                             \<open> ... suspendisse non arcu malesuada mollis, nibh morbi, ...  \<close>
                             \<open>Duplicate instance declaration\<close>

text*[d::D, a1 = "X3"] \<open> ... phasellus amet id massa nunc, pede suscipit repellendus, 
                         ... @{C "c1"} or @{C \<open>c1\<close>} or \<^C>\<open>c1\<close>
                             similar to @{thm "refl"} and \<^thm>"refl"\<close>  \<comment> \<open>ontological and built-in
                                                                          references\<close>

text\<open>Not only text-elements are "ontology-aware", proofs and code can this be too !\<close>

ML*[ddddd2::C]\<open>fun fac x = if x = 0 then 1 else x * (fac(x-1))\<close> (* TODO : BUG *)

lemma*[ddddd3::E] asd: "True" by simp

definition*[dddddd3::E] facu :: "nat \<Rightarrow> nat" where "facu xxxx = undefined"

(* BUG 
text\<open>As shown in @{E \<open>ddddd3\<close>}\<close>
text\<open>As shown in @{C \<open>ddddd2\<close>}\<close>
*)


text\<open>Ontological information ("class instances") is mutable: \<close>

update_instance*[d::D, a1 := X2]

text\<open> ... in ut tortor ... @{docitem \<open>a\<close>} ... @{A \<open>a\<close>} ... \<close> \<comment> \<open>untyped or typed referencing \<close>

(* THIS IS A BUG : this should work rather than fail. \<And>\<And>! *)
text-assert-error[ae::text_element]\<open>the function @{C "ddddd2"} \<close>\<open>referred text-element is macro!\<close>

text*[c2::C, x = "\<open>delta\<close>"]  \<open> ... in ut tortor eleifend augue pretium consectetuer.  \<close>

text\<open>Note that both the notations @{term "''beta''"} and @{term "\<open>beta\<close>"} are possible;
the former is a more ancient format only supporting pure ascii, while the latter also supports
fancy unicode such as: @{term "\<open>\<beta>\<^sub>i''\<close>"} \<close>

text*[f::F] \<open> Lectus accumsan velit ultrices, ... \<close>
  
theorem some_proof : "True" by simp

text\<open>This is an example where we add a theorem into a kind of "result-list" of the doc-item f.\<close>
update_instance*[f::F,r:="[@{thm ''Concept_OntoReferencing.some_proof''}]"]

text\<open> ..., mauris amet, id elit aliquam aptent id,  ... @{docitem \<open>a\<close>} \<close>

text\<open>Here we add and maintain a link that is actually modeled as m-to-n relation ...\<close>
update_instance*[f::F,b:="{(@{docitem  \<open>a\<close>}::A,@{docitem  \<open>c1\<close>}::C), 
                           (@{docitem  \<open>a\<close>},   @{docitem  \<open>c2\<close>})}"] 

close_monitor*[struct]

text\<open>And the trace of the monitor is:\<close>
ML\<open>val trace = @{trace_attribute struct}\<close>
ML\<open>@{assert} (trace = [("Conceptual.A", "abbbbbb"), ("Conceptual.A", "a"), ("Conceptual.A", "ab"), 
    ("Conceptual.A", "abb"), ("Conceptual.C", "c1"), ("Conceptual.C", "c1"), ("Conceptual.D", "d"), 
    ("Conceptual.C", "ddddd2"),("Conceptual.E", "ddddd3"), ("Conceptual.C", "c2"), ("Conceptual.F", "f")]) \<close>
(* BUG : SHOULD BE:
ML\<open>@{assert} (trace = [("Conceptual.A", "abbbbbb"), ("Conceptual.A", "a"), ("Conceptual.A", "ab"), ("Conceptual.A", "abb"),
    ("Conceptual.C", "c1"), ("Conceptual.D", "d"), ("Conceptual.C", "ddddd2"),
    ("Conceptual.E", "ddddd3"), ("Conceptual.C", "c2"), ("Conceptual.F", "f")]) \<close>

   FAILURE DUE TO DUPLICATE DEFINITION BUG 
*)

text\<open>Note that the monitor \<^typ>\<open>M\<close> of the ontology \<^theory>\<open>Isabelle_DOF-Ontologies.Conceptual\<close> does
     not observe the common entities of \<^theory>\<open>Isabelle_DOF.Isa_COL\<close>, but just those defined in the 
     accept- clause of \<^typ>\<open>M\<close>.\<close>

text\<open>One final check of the status DOF core: observe that no new classes have been defined,
     just a couple of new document elements have been introduced.\<close>

print_doc_classes
print_doc_items



end 
  
