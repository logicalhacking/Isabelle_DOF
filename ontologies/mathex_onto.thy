theory mathex_onto
 
imports "../Isa_DOF"
begin

doc_class Question =
  content :: "(string + term) list"

doc_class Response =
  content :: "(string + term) list"

doc_class Exercise_part = 
  question :: Question
  response :: Response

doc_class Exercise= 
  content :: "(Exercise_part) list"

end