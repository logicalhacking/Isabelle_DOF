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

section\<open>An example ontology for a scholarly paper\<close>

theory technical_report
   imports "../scholarly_paper/scholarly_paper"
begin

(* for reports paper: invariant: level \<ge> -1 *)

section\<open>More Global Text Elements for Reports\<close>

doc_class table_of_contents =
   bookmark_depth :: int <= 3
   depth          :: int <= 3

doc_class front_matter = 
   front_matter_style :: string    (* TODO Achim :::: *)

doc_class index =
   kind  :: "doc_class" 
   level :: "int option"

section\<open>Code Statement Elements\<close>

doc_class "code"     = technical +
   checked :: bool <=  "False"
   caption :: "string" <=  "''''"


text\<open>The @{doc_class "code"} is a general stub for free-form and type-checked code-fragments
such as:
\<^enum> SML code
\<^enum> bash code
\<^enum> isar code (although this might be an unwanted concurrence to the Isabelle standard cartouche)
\<^enum> C code.

it is intended that later refinements of this "stub" as done in \<^verbatim>\<open>Isabelle_C\<close> which come with their
own content checking and, of course, presentation styles. 
\<close>

doc_class "SML"     = code +
   checked :: bool <=  "False"

doc_class "ISAR"     = code +
   checked :: bool <=  "False"

doc_class "LATEX"     = code +
   checked :: bool <=  "False"

print_doc_class_template "SML" (* just a sample *)


doc_class report = 
   style_id :: string                <= "''LNCS''"
   version  :: "(int \<times> int \<times> int)"  <= "(0,0,0)"
   accepts "(title                 ~~ 
           \<lbrakk>subtitle\<rbrakk>              ~~
           \<lbrace>author\<rbrace>\<^sup>+               ~~ 
           \<lbrakk>front_matter\<rbrakk>          ~~
           abstract                ~~
           \<lbrakk>table_of_contents\<rbrakk>     ~~
           \<lbrace>introduction\<rbrace>\<^sup>+         ~~ 
           \<lbrace>technical || figure || side_by_side_figure\<rbrace>\<^sup>+ ~~ 
           \<lbrace>conclusion\<rbrace>\<^sup>+           ~~  
           \<lbrace>index\<rbrace>\<^sup>*  ~~  
           bibliography)"


end

(*
===================================== 
docclass: Isa_COL.thms 
    name:    "thms" 
    origin:  Isa_COL 
    attrs:   "properties" 
    invs:     
docclass: Isa_COL.figure 
    name:    "figure" 
    origin:  Isa_COL 
    attrs:   "relative_width", "src", "placement", "spawn_columns"(True) 
    invs:     
docclass: Isa_COL.chapter = Isa_COL.text_element +  
    name:    "chapter" 
    origin:  Isa_COL 
    attrs:   "level"(Some 0) 
    invs:     
docclass: Isa_COL.concept 
    name:    "concept" 
    origin:  Isa_COL 
    attrs:   "tag"([]), "properties"([]) 
    invs:     
docclass: Isa_COL.section = Isa_COL.text_element +  
    name:    "section" 
    origin:  Isa_COL 
    attrs:   "level"(Some 1) 
    invs:     
docclass: Isa_COL.assertions 
    name:    "assertions" 
    origin:  Isa_COL 
    attrs:   "properties" 
    invs:     
docclass: Isa_COL.subsection = Isa_COL.text_element +  
    name:    "subsection" 
    origin:  Isa_COL 
    attrs:   "level"(Some 2) 
    invs:     
docclass: Isa_COL.definitions 
    name:    "definitions" 
    origin:  Isa_COL 
    attrs:   "requires", "establishes" 
    invs:     
docclass: Isa_COL.formal_item 
    name:    "formal_item" 
    origin:  Isa_COL 
    attrs:   "item" 
    invs:     
docclass: Isa_COL.figure_group 
    name:    "figure_group" 
    origin:  Isa_COL 
    attrs:   "trace"([]), "caption" 
    invs:     
docclass: Isa_COL.text_element 
    name:    "text_element" 
    origin:  Isa_COL 
    attrs:   "level"(None), "referentiable"(False), "variants"({STR ''outline'', STR ''document''}) 
    invs:     
docclass: scholarly_paper.data = scholarly_paper.engineering_content +  
    name:    "data" 
    origin:  scholarly_paper 
    attrs:   "tag"([]) 
    invs:     
docclass: technical_report.SML = technical_report.code +  
    name:    "SML" 
    origin:  technical_report 
    attrs:   "checked"(False) 
    invs:     
docclass: Isa_COL.subsubsection = Isa_COL.text_element +  
    name:    "subsubsection" 
    origin:  Isa_COL 
    attrs:   "level"(Some 3) 
    invs:     
docclass: scholarly_paper.annex = scholarly_paper.text_section +  
    name:    "annex" 
    origin:  scholarly_paper 
    attrs:   "main_author"(None) 
    invs:     
docclass: scholarly_paper.lemma = scholarly_paper.math_content +  
    name:    "lemma" 
    origin:  scholarly_paper 
    attrs:   "referentiable"(True), "mcc"(lem) 
    invs:    d3::\<lambda>\<sigma>. lemma.mcc \<sigma> = lem 
docclass: scholarly_paper.title 
    name:    "title" 
    origin:  scholarly_paper 
    attrs:   "short_title"(None) 
    invs:     
docclass: technical_report.ISAR = technical_report.code +  
    name:    "ISAR" 
    origin:  technical_report 
    attrs:   "checked"(False) 
    invs:     
docclass: technical_report.code = scholarly_paper.technical +  
    name:    "code" 
    origin:  technical_report 
    attrs:   "checked"(False), "label"([]) 
    invs:     
docclass: Isa_COL.formal_content 
    name:    "formal_content" 
    origin:  Isa_COL 
    attrs:   "trace"([]), "style" 
    invs:     
docclass: scholarly_paper.author 
    name:    "author" 
    origin:  scholarly_paper 
    attrs:   "email"([]), "http_site"([]), "orcid"([]), "affiliation" 
    invs:     
docclass: technical_report.LATEX = technical_report.code +  
    name:    "LATEX" 
    origin:  technical_report 
    attrs:   "checked"(False) 
    invs:     
docclass: technical_report.index 
    name:    "index" 
    origin:  technical_report 
    attrs:   "kind", "level" 
    invs:     
docclass: scholarly_paper.article 
    name:    "article" 
    origin:  scholarly_paper 
    attrs:   "trace"([]), "style_id"(''LNCS''), "version"((0, 0, 0)) 
    invs:     
docclass: scholarly_paper.example = scholarly_paper.text_section +  
    name:    "example" 
    origin:  scholarly_paper 
    attrs:   "referentiable"(True), "status"(description), "short_name"([]) 
    invs:     
docclass: scholarly_paper.theorem = scholarly_paper.math_content +  
    name:    "theorem" 
    origin:  scholarly_paper 
    attrs:   "referentiable"(True), "mcc"(thm) 
    invs:    d2::\<lambda>\<sigma>. theorem.mcc \<sigma> = thm 
docclass: scholarly_paper.abstract 
    name:    "abstract" 
    origin:  scholarly_paper 
    attrs:   "keywordlist"([]), "principal_theorems" 
    invs:     
docclass: scholarly_paper.subtitle 
    name:    "subtitle" 
    origin:  scholarly_paper 
    attrs:   "abbrev"(None) 
    invs:     
docclass: scholarly_paper.corollary = scholarly_paper.math_content +  
    name:    "corollary" 
    origin:  scholarly_paper 
    attrs:   "referentiable"(True), "mcc"(cor) 
    invs:    d4::\<lambda>\<sigma>. corollary.mcc \<sigma> = thm 
docclass: scholarly_paper.technical = scholarly_paper.text_section +  
    name:    "technical" 
    origin:  scholarly_paper 
    attrs:   "definition_list"([]), "status"(description), "formal_results" 
    invs:    L1::\<lambda>\<sigma>. 0 < the (text_section.level \<sigma>) 
docclass: scholarly_paper.conclusion = scholarly_paper.text_section +  
    name:    "conclusion" 
    origin:  scholarly_paper 
    attrs:   "main_author"(None) 
    invs:     
docclass: scholarly_paper.definition = scholarly_paper.math_content +  
    name:    "definition" 
    origin:  scholarly_paper 
    attrs:   "referentiable"(True), "mcc"(defn) 
    invs:    d1::\<lambda>\<sigma>. definition.mcc \<sigma> = defn 
docclass: scholarly_paper.evaluation = scholarly_paper.engineering_content +  
    name:    "evaluation" 
    origin:  scholarly_paper 
    attrs:   "tag"([]) 
    invs:     
docclass: scholarly_paper.experiment = scholarly_paper.engineering_content +  
    name:    "experiment" 
    origin:  scholarly_paper 
    attrs:   "tag"([]) 
    invs:     
docclass: Isa_COL.side_by_side_figure = Isa_COL.figure +  
    name:    "side_by_side_figure" 
    origin:  Isa_COL 
    attrs:   "anchor", "caption", "relative_width2", "src2", "anchor2", "caption2" 
    invs:     
docclass: scholarly_paper.bibliography = scholarly_paper.text_section +  
    name:    "bibliography" 
    origin:  scholarly_paper 
    attrs:   "style"(Some ''LNCS'') 
    invs:     
docclass: scholarly_paper.introduction = scholarly_paper.text_section +  
    name:    "introduction" 
    origin:  scholarly_paper 
    attrs:   "comment", "claims" 
    invs:     
docclass: scholarly_paper.math_content = scholarly_paper.technical +  
    name:    "math_content" 
    origin:  scholarly_paper 
    attrs:   "referentiable"(True), "short_name"([]), "status"(semiformal), "mcc"(thm) 
    invs:    s1::\<lambda>\<sigma>. \<not> math_content.referentiable \<sigma> \<longrightarrow>
                     math_content.short_name \<sigma> = [], s2::\<lambda>\<sigma>. math_content.status \<sigma> = semiformal 
docclass: scholarly_paper.math_example = scholarly_paper.math_content +  
    name:    "math_example" 
    origin:  scholarly_paper 
    attrs:   "referentiable"(True), "mcc"(expl) 
    invs:    d5::\<lambda>\<sigma>. math_example.mcc \<sigma> = expl 
docclass: scholarly_paper.related_work = scholarly_paper.conclusion +  
    name:    "related_work" 
    origin:  scholarly_paper 
    attrs:   "main_author"(None) 
    invs:     
docclass: scholarly_paper.tech_example = scholarly_paper.technical +  
    name:    "tech_example" 
    origin:  scholarly_paper 
    attrs:   "referentiable"(True), "tag"([]) 
    invs:     
docclass: scholarly_paper.text_section = Isa_COL.text_element +  
    name:    "text_section" 
    origin:  scholarly_paper 
    attrs:   "main_author"(None), "fixme_list"([]), "level"(None) 
    invs:     
docclass: technical_report.front_matter 
    name:    "front_matter" 
    origin:  technical_report 
    attrs:   "front_matter_style" 
    invs:     
docclass: scholarly_paper.math_motivation = scholarly_paper.technical +  
    name:    "math_motivation" 
    origin:  scholarly_paper 
    attrs:   "referentiable"(False) 
    invs:     
docclass: scholarly_paper.math_semiformal = scholarly_paper.math_content +  
    name:    "math_semiformal" 
    origin:  scholarly_paper 
    attrs:   "referentiable"(True) 
    invs:     
docclass: scholarly_paper.math_explanation = scholarly_paper.technical +  
    name:    "math_explanation" 
    origin:  scholarly_paper 
    attrs:   "referentiable"(False) 
    invs:     
docclass: technical_report.table_of_contents 
    name:    "table_of_contents" 
    origin:  technical_report 
    attrs:   "bookmark_depth"(3), "depth"(3) 
    invs:     
docclass: scholarly_paper.engineering_content = scholarly_paper.technical +  
    name:    "engineering_content" 
    origin:  scholarly_paper 
    attrs:   "short_name"([]), "status" 
    invs:     
=====================================


*)
