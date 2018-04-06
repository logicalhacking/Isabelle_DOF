theory mathex_onto
 
imports "../Isa_DOF"
begin

doc_class Question =
  content :: "string list"

doc_class Response =
  content :: "string list"

doc_class Exercise = 
  question :: Question
  response :: Response


end