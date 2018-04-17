theory mathex_onto
 
imports "../Isa_DOF"
begin

doc_class Question =
  content :: "(string + term) list"

doc_class Response =
  content :: "(string + term) list"

datatype grades = A | B | C  
  
doc_class Exercise_part = 
  question :: Question
  response :: Response

doc_class Exercise= 
  content :: "(Exercise_part) list"

doc_class MathExam=
  content :: "(Exercise) list"

section{* Example*}  
 
term "[ @{thm ''refl''}] @ [ @{thm ''sym''}, @{thm ''trans''} ] "
  
text{*
      @{term "[ @{thm ''refl''}] @ [ @{thm ''sym''}, @{thm ''trans''} ]"}} are the theorems
of the equational logic fragment of HOL.
*}

  
  
end