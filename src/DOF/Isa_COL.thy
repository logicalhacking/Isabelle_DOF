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

chapter \<open>The Document Ontology Common Library for the Isabelle Ontology Framework\<close>

text\<open> Offering 
\<^item> ...
\<^item> 
\<^item> LaTeX support. \<close> 
  
 
theory Isa_COL   
  imports  Isa_DOF  
begin
  
   
section\<open> Library of Standard Text Ontology \<close>



datatype placement = pl_h  | (*here*) 
                     pl_t  | (*top*)
                     pl_b  | (*bottom*)
                     pl_ht | (*here ->  top*) 
                     pl_hb   (*here ->  bottom*)



doc_class figure   = 
   relative_width   :: "int" (* percent of textwidth *)    
   src              :: "string"
   placement        :: placement 
   spawn_columns    :: bool <= True 

ML\<open>(Symtab.defined (#docclass_tab(DOF_core.get_data_global @{theory}))) "side_by_side_figure"\<close>


print_doc_classes

doc_class side_by_side_figure = figure +
   anchor           :: "string"
   caption          :: "string"
   relative_width2  :: "int" (* percent of textwidth *)    
   src2             :: "string"
   anchor2          :: "string"
   caption2         :: "string"

print_doc_classes


doc_class figure_group = 
   (*  trace :: "doc_class rexp list" <= "[]" automatically generated since monitor clause *)
   caption          :: "string"
   rejects             figure_group   (* this forbids recursive figure-groups not supported
                                        by the current LaTeX style-file. *)
   accepts             "\<lbrace>figure\<rbrace>\<^sup>+"

print_doc_classes


(* dito the future table *)

(* dito the future monitor: table - block *)


text\<open> The attribute @{term "level"} in the subsequent enables doc-notation support section* etc.
we follow LaTeX terminology on levels 
\<^enum>             part          = Some -1
\<^enum>             chapter       = Some 0
\<^enum>             section       = Some 1
\<^enum>             subsection    = Some 2
\<^enum>             subsubsection = Some 3
\<^enum>             ... 

for scholarly paper: invariant level > 0 \<close>

doc_class text_element = 
   level         :: "int  option"    <=  "None" 
   referentiable :: bool <= "False"
   variants      :: "String.literal set" <= "{STR ''outline'', STR ''document''}" 

section\<open>Some attempt to model standardized links to Standard Isabelle Formal Content\<close>
(* Deprecated *)
doc_class assertions = 
    properties :: "term list"
  
doc_class "thms" =
    properties :: "thm list"

doc_class formal_item = 
    item :: "(assertions + thms)"

doc_class definitions =
    requires    :: "formal_item list"
    establishes :: "thms list"

doc_class formal_content =
    style :: "string option"
    accepts "\<lbrace>formal_item\<rbrace>\<^sup>+"

doc_class concept = 
    tag        :: "string"   <= "''''"
    properties :: "thm list" <= "[]"

section\<open>Tests\<close>
   
ML\<open>@{term "side_by_side_figure"};
@{typ "doc_class rexp"}; 
DOF_core.SPY;
\<close>


end
