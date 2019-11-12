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
  
  
datatype ContentClass =   setter   | checker   | externalExaminer  |  student         

  
doc_class Author =
   affiliation :: "string"
   roles       :: "ContentClass set"
   email       :: "string"


doc_class Exam_item = 
  level        :: "int option"
  concerns     :: "ContentClass set"  
  visible_for  :: "ContentClass set"  

doc_class Header = Exam_item +
  date          :: string
  authors       :: "Author list"
  timeAllowed   :: int (*  minutes *)

doc_class marking = Exam_item +
   marks        :: int

doc_class Answer_Element =  Exam_item +
  justification :: string
  "term"        :: "string" 

doc_class text_answer =  Answer_Element +
  "term"        :: "string" 

doc_class program_text =  Answer_Element +
  "term"        :: "string" 

doc_class formula_text =  Answer_Element +
  "term"        :: "string" 

doc_class checkbox =  Answer_Element +
  "term"        :: "string" 

doc_class radiobuttons =  Answer_Element +
  "term"        :: "string" 

doc_class equational_derivation =  Answer_Element +
  "term"        :: "string" 

doc_class proof_derivation =  Answer_Element +
  "term"        :: "string" 


doc_class Answer_YesNo =  Exam_item +
  step_label    :: string
  yes_no        :: bool  (* \<open>for checkboxes\<close> *)

datatype Question_Type =   
  formal | informal | mixed 
  
doc_class Task = Exam_item +
  local_grade :: marking
  type        :: Question_Type
  subitems    :: "(SubQuestion * (Answer_Formal_Step list + Answer_YesNo)list) list"
  concerns    :: "ContentClass set" <= "{setter,student,checker,externalExaminer}" 
  mark        :: int


doc_class SubTask = Task + 
  local_grade :: Level

doc_class Exercise = Exam_item +
  content  :: "(Task) list"
  concerns :: "ContentClass set" <= "{setter,student,checker,externalExaminer}"


text\<open>In many institutions, it makes sense to have a rigorous process of validation
for exam subjects : is the initial question correct ? Is a proof in the sense of the
question possible ? We model the possibility that the @{term setter} validates a 
question by a sample proof validated by Isabelle. In our scenario this sample proofs
are completely @{emph \<open>intern\<close>}, i.e. not exposed to the students but just additional
material for the internal review process of the exam.\<close>
  
doc_class Validation = 
   tests  :: "term list"  <="[]"
   proofs :: "thm list"   <="[]"
  
doc_class Solution = Exam_item +
  valids   :: "Validation list"
  concerns :: "ContentClass set" <= "{setter,checker,externalExaminer}"
  
doc_class MathExam =
  global_grade :: Mark 
  accepts "\<lbrace>Author\<rbrace>\<^sup>+  ~~  Header ~~  \<lbrace>Exercise ~~ Solution\<rbrace>\<^sup>+ "


(*
exercise - (header ~ context_description ~ task list)
*)

(*
tasks  > subtask

answer > subanswer

 
answer_element
 - text
 - program-text ? ? ? 
 - checkbox
 - radiobutton
 - equational derivation
 - proof derivation

solution > subsolution
 - text
 - program-text
 - checkbox
 - radiobutton
 - equational derivation
 - proof derivation

marking > submarking
  
grade

Invarianten:
1 : n Relation answer_element \<longrightarrow> subsolution

2 : invariants over markings and grades

3 : distribution constraints: subtask should have more than 25 % of overall grade 

*)



(*>>*)
end
