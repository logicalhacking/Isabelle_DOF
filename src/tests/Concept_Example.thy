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
  "../ontologies/Conceptual/Conceptual" (* we use the generic "Conceptual" ontology *)
begin

text\<open>@{theory "Isabelle_DOF-tests.Conceptual"} provides a monitor @{typ M} enforcing a particular document structure.
     Here, we say: From now on, this structural rules are respected wrt. all doc\_classes M is
     enabled for.\<close>
open_monitor*[struct::M]  

section*[a::A, x = "3"] \<open> Lorem ipsum dolor sit amet, ... \<close>

text*[c1::C, x = "''beta''"] \<open> ... suspendisse non arcu malesuada mollis, nibh morbi, ...  \<close>

text*[d::D, a1 = "X3"] \<open> ... phasellus amet id massa nunc, pede suscipit repellendus, 
                         ... @{C "c1"} @{thm "refl"} \<close>


update_instance*[d::D, a1 := X2]

text\<open> ... in ut tortor ... @{docitem \<open>a\<close>} ... @{A \<open>a\<close>}\<close>  
    
text*[c2::C, x = "\<open>delta\<close>"]  \<open> ... in ut tortor eleifend augue pretium consectetuer.  \<close>

text\<open>Note that both the notations @{term "''beta''"} and @{term "\<open>beta\<close>"} are possible;
the former is a more ancient format only supporting pure ascii, while the latter also supports
fancy unicode such as: @{term "\<open>\<beta>\<^sub>i''\<close>"} \<close>

text*[f::F] \<open> Lectus accumsan velit ultrices, ... }\<close>
  
theorem some_proof : "True" by simp

text\<open>This is an example where we add a theorem into a kind of "result-list" of the doc-item f.\<close>
update_instance*[f::F,r:="[@{thm ''Concept_Example.some_proof''}]"]

text\<open> ..., mauris amet, id elit aliquam aptent id,  ... @{docitem \<open>a\<close>} \<close>

text\<open>Here we add and maintain a link that is actually modeled as m-to-n relation ...\<close>
update_instance*[f::F,b:="{(@{docitem  \<open>a\<close>}::A,@{docitem  \<open>c1\<close>}::C), 
                           (@{docitem  \<open>a\<close>},   @{docitem  \<open>c2\<close>})}"] 

close_monitor*[struct]

text\<open>And the trace of the monitor is:\<close>
ML\<open>@{trace_attribute struct}\<close>


print_doc_classes
print_doc_items



end 
  
