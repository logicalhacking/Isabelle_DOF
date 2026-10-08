(*************************************************************************
 * Copyright (C) 
 *               2026      The University of Exeter 
 *               2026      The University of Paris-Saclay
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

chapter \<open>An Outline of an Exercise Ontology\<close>

text\<open>  \<close> 

(*<<*)  
theory  Exercise
  imports  
  "Isabelle_DOF.scholarly_paper" 
begin

(*
define_ontology "exercise.sty" "Exercise"
*)

text\<open>The Exercise ontology is distantly oriented towards the exercise.sty offerred by the
TeXLife distribution. A documentation can be found here 
\url\<open>https://ctan.tetaneutral.net/macros/latex/contrib/exercise/exercise.pdf\<close>.\<close>      
     
doc_class "exercise" = text_section + \<comment> \<open> equivalent 'ExerciseList' in exercise.sty\<close>
      title      :: string
      difficulty :: int
      origin     :: string
      name       :: string
      counter    :: int  
      \<comment> \<open>The body of the exercise class is used to give context information or background material.\<close>

doc_class task = text_section +      \<comment> \<open> equivalent 'Exercise' in exercise.sty\<close>
      header     :: \<open>string option\<close>
      number     :: \<open>int option\<close>
      difficulty :: int
      \<comment> \<open>The body of the task class is used formulate the question.\<close>


doc_class solution = text_section +  \<comment> \<open> equivalent 'Answer' in exercise.sty\<close>
      header    :: \<open>string option\<close>
      refers_to :: \<open>string list\<close>     \<comment> \<open>references to CMs and TDs and beyond.\<close>
      \<comment> \<open>The body of the task class is used to give context information or background.\<close>


datatype category = TD | TP | CM | Exam

doc_class exercise_sheet = 
      status        :: status <= semiformal 
      authors       :: \<open>author list\<close> 
      reviewers     :: \<open>author list\<close>
      institution   :: \<open>string\<close>
      cat           :: category 
      course        :: string
      year          :: int
      month         :: int
      \<comment> \<open>The body of the task class may be used to give context information general hints.\<close>
      accepts "\<lbrace> exercise ~~ \<lbrace>task ~~ solution \<rbrace>\<^sup>+ \<rbrace>\<^sup>+"


end

