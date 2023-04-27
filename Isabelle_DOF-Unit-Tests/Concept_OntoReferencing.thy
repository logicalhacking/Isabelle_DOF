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

theory   Concept_OntoReferencing
  imports   "TestKit"
            "Isabelle_DOF_Unit_Tests_document"
            "Isabelle_DOF-Ontologies.Conceptual" 
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
title*[ag::title, short_title="Some\<open>ooups.\<close>"]\<open>Lorem ipsum dolor sit amet ...\<close>
subtitle*[af::subtitle, abbrev = "Some\<open>ooups-oups.\<close>"]\<open>Lorem ipsum dolor sit amet ...\<close>
chapter*[a0::A, x = "3"]   \<open> Lorem ipsum dolor sit amet ... \<close>
section*[a::A, x = "3"]         \<open> Lorem ipsum dolor sit amet, ... \<close>
subsection*[ab::A, x = "3"]     \<open> Lorem ipsum dolor sit amet, ... 
                                  As mentioned in the @{title \<open>ag\<close>}... \<close> \<comment> \<open>old-style and ...\<close>
subsubsection*[ac::A, x = "3"]  \<open> Lorem ipsum dolor sit amet, ... 
                                  As mentioned in the \<^title>\<open>ag\<close>\<close>    \<comment> \<open>new-style references to
                                                                          ontological instances 
                                                                          assigned to text 
                                                                          elements ...\<close>
(*>*)


text\<open>Meta-Objects are typed, and references have to respect this : \<close>
(*<*)
text-assert-error[ad]\<open> \<^title>\<open>a\<close> \<close>    \<open>reference ontologically inconsistent\<close>
text-assert-error[ae]\<open> \<^title>\<open>af\<close> \<close>\<open>reference ontologically inconsistent\<close> 
                       \<comment> \<open>erroneous reference: please consider class hierarchy!\<close>
(*>*)

text\<open>References to Meta-Objects can be forward-declared:\<close>

text-assert-error[ae1]\<open>@{C \<open>c1\<close>}\<close>\<open>Undefined instance:\<close>

declare_reference*[c1::C]     \<comment> \<open>forward declaration\<close>

text-assert-error\<open>@{C \<open>c1\<close>} \<close>\<open>Instance declared but not defined, try option unchecked\<close>

text\<open>@{C (unchecked) \<open>c1\<close>} \<close>

text*[a1::A, level="Some 0", x = 3]\<open>... phasellus amet id massa nunc, ...\<close>
text*[c1::C, x = "''beta''"] \<open> ... suspendisse non arcu malesuada mollis, nibh morbi, ...  \<close>

text-assert-error[c1::C, x = "''gamma''"] 
                             \<open> ... suspendisse non arcu malesuada mollis, nibh morbi, ...  \<close>
                             \<open>Duplicate instance declaration\<close>

\<comment> \<open>Referencing from a text context:\<close>
text*[d::D, a1 = "X3"] \<open> ... phasellus amet id massa nunc, pede suscipit repellendus, 
                         ... @{C "c1"} or @{C \<open>c1\<close>} or \<^C>\<open>c1\<close>
                             similar to @{thm "refl"} and \<^thm>"refl"\<close>  \<comment> \<open>ontological and built-in
                                                                          references\<close>

text\<open>Not only text-elements are "ontology-aware", proofs and code can this be too !\<close>

\<comment> \<open>Referencing from and to a ML-code context:\<close>

ML*[c4::C, z = "Some @{A \<open>a1\<close>}"]\<open>
fun fac x = if x  = 0  then 1 else x * (fac(x-1))
val v = \<^value_>\<open>A.x (the (z @{C \<open>c4\<close>}))\<close> |> HOLogic.dest_number |> snd |> fac
\<close>

definition*[a2::A, x=5, level="Some 1"] xx' where "xx' \<equiv> A.x @{A \<open>a1\<close>}" if "A.x @{A \<open>a1\<close>} = 5"

lemma*[e5::E] testtest : "xx + A.x @{A \<open>a1\<close>} = yy + A.x @{A \<open>a1\<close>} \<Longrightarrow> xx = yy" by simp

doc_class cc_assumption_test =
a :: int
text*[cc_assumption_test_ref::cc_assumption_test]\<open>\<close>

definition tag_l :: "'a \<Rightarrow> 'b \<Rightarrow> 'b" where "tag_l \<equiv> \<lambda>x y. y"

lemma* tagged : "tag_l @{cc-assumption-test \<open>cc_assumption_test_ref\<close>} AA \<Longrightarrow> AA"
  by (simp add: tag_l_def)

find_theorems name:tagged "(_::cc_assumption_test \<Rightarrow> _ \<Rightarrow> _) _ _ \<Longrightarrow>_"

declare_reference-assert-error[c1::C]\<open>Duplicate instance declaration\<close>     \<comment> \<open>forward declaration\<close>

declare_reference*[e6::E] 

text\<open>This is the answer to the "OutOfOrder Presentation Problem": @{E (unchecked) \<open>e6\<close>} \<close>

definition*[e6::E] facu :: "nat \<Rightarrow> nat" where "facu arg = undefined"

text\<open>As shown in @{E \<open>e5\<close>} following from  @{E \<open>e6\<close>}\<close> 

text\<open>As shown in @{C \<open>c4\<close>}\<close>



text\<open>Ontological information ("class instances") is mutable: \<close>

update_instance*[d::D, a1 := X2]

text\<open> ... in ut tortor ... @{docitem \<open>a\<close>} ... @{A \<open>a\<close>} ... \<close> \<comment> \<open>untyped or typed referencing \<close>

text-assert-error[ae::text_element]\<open>the function @{C [display] "c4"} \<close>\<open>referred text-element is no macro!\<close>

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

section\<open>Closing the Monitor and testing the Results.\<close>

close_monitor*[struct]

text\<open>And the trace of the monitor is:\<close>
ML\<open>val trace = @{trace_attribute struct}\<close>
ML\<open>@{assert} (trace = 
   [("Conceptual.A", "a0"), ("Conceptual.A", "a"), ("Conceptual.A", "ab"),
    ("Conceptual.A", "ac"), ("Conceptual.A", "a1"),
    ("Conceptual.C", "c1"), ("Conceptual.D", "d"), ("Conceptual.C", "c4"),
    ("Conceptual.A", "a2"), ("Conceptual.E", "e5"), 
    ("Conceptual.E", "e6"), ("Conceptual.C", "c2"), ("Conceptual.F", "f")]) \<close>


text\<open>Note that the monitor \<^typ>\<open>M\<close> of the ontology \<^theory>\<open>Isabelle_DOF-Ontologies.Conceptual\<close> does
     not observe the common entities of \<^theory>\<open>Isabelle_DOF.Isa_COL\<close>, but just those defined in the 
     accept- clause of \<^typ>\<open>M\<close>.\<close>

text\<open>One final check of the status DOF core: observe that no new classes have been defined,
     just a couple of new document elements have been introduced.\<close>

print_doc_classes
print_doc_items



end 
  
