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


define_ontology "exercise.sty" "Exercise"


text\<open>\<close>

datatype category = TD | TP | CM 

doc_class exercise_sheet = 
      status        :: status <= "semiformal" 
      authors       :: "author list" 
      reviewers     :: "author list"
      institution   :: "string"
      course        :: string
      year          :: int
      month         :: int

doc_class exercise = 
      dfgd :: string
      label::string
      title::string
      difficulty::int
      origin::string
      name::string
      counter::int
      number::string 
      exam::string 
      year::string

doc_class description = sdf:: int

doc_class task = 
      dfgd :: string


doc_class solution = 
      dfgd :: string

doc_class anwer = 
      dfgd :: string



