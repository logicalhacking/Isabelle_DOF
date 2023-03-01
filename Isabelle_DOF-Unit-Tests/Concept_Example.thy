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
  Concept_Example
  imports 
  "Isabelle_DOF-Unit-Tests_document"
  "Isabelle_DOF-Ontologies.Conceptual" 
  "TestKit"
begin

section\<open>Setting up a monitor.\<close>
text\<open>\<^theory>\<open>Isabelle_DOF-Ontologies.Conceptual\<close> provides a monitor \<^typ>\<open>M\<close>  enforcing a 
     particular document structure. Here, we say: From now on, this structural rules are 
     respected wrt. all \<^theory_text>\<open>doc_classes M\<close> is enabled for.\<close>

open_monitor*[struct::M]  

section\<open>Defining Text Elements and Referring to them... \<close>

text\<open>This uses elements of two ontologies, notably 
      \<^theory>\<open>Isabelle_DOF-Ontologies.Conceptual\<close> and \<^theory>\<open>Isabelle_DOF.Isa_COL\<close>.\<close>

title*[abbb::title, short_title="Some\<open>ooups.\<close>"]\<open>Lorem ipsum dolor sit amet ...\<close>
subtitle*[abbbb::subtitle, abbrev = "Some\<open>ooups-oups.\<close>"]\<open>Lorem ipsum dolor sit amet ...\<close>
chapter*[abbbbbb::A, x = "3"]   \<open> Lorem ipsum dolor sit amet ... \<close>
section*[a::A, x = "3"]         \<open> Lorem ipsum dolor sit amet, ... \<close>
subsection*[ab::A, x = "3"]     \<open> Lorem ipsum dolor sit amet, ... 
                                  As mentioned in the @{title \<open>abbb\<close>}... \<close> \<comment> \<open>old-style and ...\<close>
subsubsection*[abb::A, x = "3"] \<open> Lorem ipsum dolor sit amet, ... 
                                  As mentioned in the \<^title>\<open>abbb\<close>\<close>    \<comment> \<open>new-style references to
                                                                          ontologically qualified
                                                                          text elements ...\<close>

text-assert-error[ac]\<open> \<^title>\<open>a\<close> \<close>\<open>reference ontologically inconsistent\<close>
text-assert-error[ad]\<open> \<^title>\<open>abbbb\<close> \<close>\<open>reference ontologically inconsistent\<close> 
                       \<comment> \<open>consider class hierarchy!\<close>

text*[c1::C, x = "''beta''"] \<open> ... suspendisse non arcu malesuada mollis, nibh morbi, ...  \<close>

text*[d::D, a1 = "X3"] \<open> ... phasellus amet id massa nunc, pede suscipit repellendus, 
                         ... @{C "c1"} or @{C \<open>c1\<close>} or \<^C>\<open>c1\<close>
                             similar to @{thm "refl"} and \<^thm>"refl"\<close>

ML*[ddddd2::E]\<open>fun fac x = if x = 0 then 1 else x * (fac(x-1))\<close>

update_instance*[d::D, a1 := X2]

text\<open> ... in ut tortor ... @{docitem \<open>a\<close>} ... @{A \<open>a\<close>} ... \<close> \<comment> \<open>untyped or typed referencing \<close>

(* THIS IS A BUG \<And>\<And>! *)
text-assert-error[ae]\<open>the function @{E "ddddd2"} \<close>\<open>referred text-element is macro!\<close>

text*[c2::C, x = "\<open>delta\<close>"]  \<open> ... in ut tortor eleifend augue pretium consectetuer.  \<close>

text\<open>Note that both the notations @{term "''beta''"} and @{term "\<open>beta\<close>"} are possible;
the former is a more ancient format only supporting pure ascii, while the latter also supports
fancy unicode such as: @{term "\<open>\<beta>\<^sub>i''\<close>"} \<close>

text*[f::F] \<open> Lectus accumsan velit ultrices, ... \<close>
  
theorem some_proof : "True" by simp

text\<open>This is an example where we add a theorem into a kind of "result-list" of the doc-item f.\<close>
update_instance*[f::F,r:="[@{thm ''Concept_Example.some_proof''}]"]

text\<open> ..., mauris amet, id elit aliquam aptent id,  ... @{docitem \<open>a\<close>} \<close>

text\<open>Here we add and maintain a link that is actually modeled as m-to-n relation ...\<close>
update_instance*[f::F,b:="{(@{docitem  \<open>a\<close>}::A,@{docitem  \<open>c1\<close>}::C), 
                           (@{docitem  \<open>a\<close>},   @{docitem  \<open>c2\<close>})}"] 

close_monitor*[struct]

text\<open>And the trace of the monitor is:\<close>
ML\<open>val trace = @{trace_attribute struct}\<close>
ML\<open>@{assert} (trace = [("Conceptual.A", "abbbbbb"), ("Conceptual.A", "a"), ("Conceptual.A", "ab"), 
                       ("Conceptual.A", "abb"),("Conceptual.C", "c1"), ("Conceptual.D", "d"), 
                       ("Conceptual.E", "ddddd2"), ("Conceptual.C", "c2"), ("Conceptual.F", "f")]) \<close>

text\<open>Note that the monitor \<^typ>\<open>M\<close> of the ontology \<^theory>\<open>Isabelle_DOF-Ontologies.Conceptual\<close> does
     not observe the common entities of \<^theory>\<open>Isabelle_DOF.Isa_COL\<close>, but just those defined in the 
     accept- clause of \<^typ>\<open>M\<close>.\<close>

text\<open>One final check of the status DOF core: observe that no new classes have been defined,
     just a couple of new document elements have been introduced.\<close>

print_doc_classes
print_doc_items



end 
  
