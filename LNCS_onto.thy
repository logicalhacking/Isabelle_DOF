theory LNCS_onto
  imports Isa_DOF
begin

doc_class title =
   short_title :: "string option" -- None
  
doc_class subtitle =
   abbrev :: "string option"      -- None

doc_class author =
   affiliation :: "string"

doc_class abstract =
   keywds :: "string list"

doc_class introduction =
   main_author :: "author option"

doc_class tech_section =
   main_author :: "author option"

doc_class conclusion =
   main_author :: "author option"

doc_class bibliography =
   style :: "string option" -- "''LNCS''"

doc_class article = 
   T     :: "title option"     -- None
   ST    :: "subtitle option" -- None
   AS    :: "author list"
   ABS   :: "abstract option"
   INTRO :: "introduction option" 
   TS    :: "tech_section list"
   CON   :: "conclusion"
   where "(title . 
           [subtitle] .
           (author)+ .
           abstract .
           introduction . 
           (tech_section)+ . 
           conclusion . 
           bibliography)"


end

