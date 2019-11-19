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

theory Nmath_exam
 imports "../../DOF/Isa_COL"
begin
  
(*<<*)  
text\<open>In our scenario, content has four different types of addressees: 
\<^item> the @{emph \<open>setter\<close>}, i.e. the author of the exam, 
\<^item> the @{emph \<open>student\<close>}, i.e. the addressee of the exam, 
\<^item> the @{emph \<open>checker\<close>}, i.e. a person that checks the exam for
\<^item> the @{emph \<open>external\_examiner\<close>}, i.e. a person that checks the exam for
  feasibility and non-ambiguity.

Note that the latter quality assurance mechanism is used in many universities,
where for organizational reasons the execution of an exam takes place in facilities
where the author of the exam is not expected to be physically present.
\<close>  
  
  
datatype content_class =   setter   | checker   | external_examiner  |  student         

text\<open>Tasks, Answers and Solutions are grouped into the \<^emph>\<open>categories\<close> 
\<^enum> \<open>main\<close> and 
\<^enum> \<open>sub\<close>. \<close>

datatype category = main | sub
  
doc_class author =
   affiliation :: "string"
   roles       :: "content_class set"
   email       :: "string"


doc_class exam_item = 
   level        :: "int option"
   concerns     :: "content_class set"  
   visible_for  :: "content_class set"  

doc_class header = exam_item +
   date          :: string
   authors       :: "author list"
   timeAllowed   :: int (*  minutes *)


datatype prog_lang = python | C | java | Haskell | SML


doc_class marking = exam_item +
   marks        :: int

doc_class answer_element =  exam_item +
   cat           :: category
(* justification :: string
  "term"        :: "string"  *)


doc_class text_answer =  answer_element +
   "term"        :: "string" 

doc_class program_text =  answer_element +
   prog_lang    :: prog_lang
   pre_filled   :: "string"  <= "\<open>This is a text with \<alpha>, \<beta>, \<gamma>\<close>" 

doc_class formula_text =  answer_element +
   "term"        :: "string" 

doc_class checkbox = exam_item  +
   "value"       :: "bool option"

doc_class checkboxes = answer_element +
   marks         :: int
   accepts       "\<lbrace>checkbox\<rbrace>\<^sup>+"
           
doc_class radiobutton =  exam_item +
   "value"       :: "bool option"
   "term"        :: "string" 

doc_class radiobuttons =  answer_element +
   "term"        :: "string" 
   accepts       "\<lbrace>radiobutton\<rbrace>\<^sup>+ "

datatype opn = eq | equiv | refines | refined_by

doc_class equational_derivation =  answer_element +
   eq_deriv        :: "(opn option \<times> term option) list" 

(* these two could be refined substantially *)
doc_class proof_derivation =  answer_element +
   "term"        :: "term list" 

doc_class answer = exam_item +
   cat         :: category
   accepts "\<lbrace>answer_element\<rbrace>\<^sup>+ "
    

datatype task_type =  formal | informal | mixed 
  
doc_class task = exam_item +
   cat         :: category
   local_grade :: marking
   type        :: task_type
   concerns    :: "content_class set" <= "{setter,student,checker,external_examiner}" 
   mark        :: int

doc_class validation = 
   tests  :: "term list"  <="[]"
   proofs :: "thm list"   <="[]"

doc_class solution = exam_item +
   cat         :: category
   motivation  :: string
   valids      :: "validation list"
   objectives  :: string 
   concerns    :: "content_class set" <= "{setter,checker,external_examiner}" 
  


doc_class exercise = exam_item +
   concerns :: "content_class set" <= "{setter,student,checker,external_examiner}"
   accepts "\<lbrace>task ~~ answer\<rbrace>\<^sup>+ ~~ \<lbrace>solution\<rbrace>\<^sup>+"


ML\<open>fun check_exercise_inv_1 oid {is_monitor} ctxt = 
      let fun get_attr oid attr =  AttributeAccess.compute_attr_access ctxt attr oid @{here} @{here} 
          (* val term =  AttributeAccess.compute_attr_access ctxt "trace" oid @{here} @{here} *)
          fun conv (Const(@{const_name "Pair"},_) $ Const(s,_) $ S) = (s, HOLogic.dest_string S)
          val string_pair_list = map conv (HOLogic.dest_list (get_attr oid "trace" )) 
          val cid_list = map fst string_pair_list
          val ctxt' = Proof_Context.init_global(Context.theory_of ctxt)
          fun is_task x = DOF_core.is_subclass ctxt' x "Nmath_exam.task"
          fun is_answer x = DOF_core.is_subclass ctxt' x "Nmath_exam.answer"
          val task_answer_part = (filter (fn x => is_task x orelse is_answer x) cid_list)
          val _ = case get_attr (hd task_answer_part) "cat" of
                     @{term "main"} => ()
                  |  _ => error("class exercise invariant violation: must start with main category. ")
          fun check_match [] = ()
             |check_match (task_id::answer_id::S) = 
                    (if get_attr task_id "cat" = get_attr answer_id "cat" 
                     then check_match S
                     else error("class exercise invariant violation: \
                                \ task and answer category does not match. "))
          val _ = check_match task_answer_part
      in  true end
\<close>

setup\<open>DOF_core.update_class_invariant "Nmath_exam.exercise" check_exercise_inv_1\<close>

doc_class context_description = exam_item +
   label :: string

doc_class math_exam =
   global_grade :: int 
   accepts "header ~~ \<lbrace>author\<rbrace>\<^sup>+ ~~ context_description ~~ \<lbrace>exercise\<rbrace>\<^sup>+ "



text\<open> Invariants (not yet implemented):

\<^enum> the task list must start with a \<open>main\<close> category.

\<^enum> solutions must structurally match to answer blocks, i.e. coincide in
  category and corresponding answer elements

\<^enum> one-to-n relation between answer_elements and solutions

\<^enum> invariants over markings and grades : sub-task must sum up to task grades, exo
  marks to the global grade.

\<^enum> distribution constraints: subtask should have no more than 25 % of overall grade.

\<close>




(*>>*)
end
