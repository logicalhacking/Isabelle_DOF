theory ScientificPaperOnto
  imports "../Isa_DOF"

begin

doc_class Paragraph = 
    content :: "string list" 

doc_class Abstract =
     content ::  Paragraph 

doc_class SubSection =
    id :: integer
    content :: "Paragraph list"

doc_class Section =
    id :: integer
    content :: "Paragraph list"
    itsSubSection :: "SubSection list"

doc_class Article = 
    content :: "(Abstract + Section) list"
    where
    "(Abstract.
      Section*)"
end