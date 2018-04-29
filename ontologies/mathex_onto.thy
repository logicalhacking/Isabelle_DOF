theory mathex_onto
 
imports "../Isa_DOF"
begin

doc_class Author =
   affiliation :: "string"
   email :: "string"

datatype Subject =
  algebra | geometry | statistical

datatype Level =
  oneStar | twoStars | threeStars

text{* In our scenario, content has three different types of addressees: 
\<^item> the @{emph \<open>examiner\<close>}, i.e. the author of the exam, 
\<^item> the @{emph \<open>student\<close>}, i.e. the addressee of the exam, 
\<^item> the @{emph \<open>validator\<close>}, i.e. a person that checks the exam for
  feasibility and non-ambiguity.

Note that the latter quality assurance mechanism is used in many universities,
where for organizational reasons the execution of an exam takes place in facilities
where the author of the exam is not expected to be physically present.
 *}  
  
datatype ContentClass =   
  examiner | validator | student
  
datatype Grade =
  A1 | A2 | A3

doc_class Header = 
  examTitle :: string
  examGrade :: Grade
  examSubject :: Subject

doc_class Question =
  level :: Level
  mark  :: integer

doc_class Exercise= 
  content :: "(Question) list"
  mark :: integer

doc_class Solution = 
  content :: "(Question) list"
  
  
doc_class MathExam=
  content :: "(Header + Author + Exercise) list"
  where "((Author)+  ~
          Header ~ 
         (Exercise)+ )"
end