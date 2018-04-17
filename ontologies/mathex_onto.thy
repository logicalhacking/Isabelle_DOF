theory mathex_onto
 
imports "../Isa_DOF"
begin

doc_class Author =
   affiliation :: "string"

datatype Subject =
  algebra | geometry | statistical

datatype Level =
  oneStar | twoStars | threeStars

datatype Grade =
  A1 | A2 | A3

doc_class Header = 
  examGrade :: Grade
  examSubject :: Subject

doc_class Question =
  level :: Level
  mark :: integer

doc_class Exercise= 
  content :: "(Question) list"

doc_class MathExam=
  content :: "(Header + Author + Exercise) list"
 where "(Header ~ 
        (Author)+  ~
        (Exercise)+ )"
  
  
end