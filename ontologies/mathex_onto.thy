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

datatype Grade =
  A1 | A2 | A3

doc_class Header = 
  examTitle :: string
  examGrade :: Grade
  examSubject :: Subject

doc_class Question =
  level :: Level
  mark :: integer

doc_class Exercise= 
  content :: "(Question) list"
  mark :: integer

doc_class MathExam=
  content :: "(Header + Author + Exercise) list"
  where "((Author)+  ~
          Header ~ 
         (Exercise)+ )"
end