section{* An example ontology for a scholarly paper*}

theory scholarly_paper
   imports "../Isa_DOF"
begin

doc_class title =
   short_title :: "string option"  <=  "None"
    
doc_class subtitle =
   abbrev :: "string option"       <=  "None"
   
-- \<open>adding a contribution list and checking that it is cited as well in tech as in conclusion. ? \<close>

doc_class author =
   email       :: "string"
   orcid       :: "string"
   affiliation :: "string"

doc_class abstract =
  keywordlist    :: "string list"   <= "[]"


doc_class text_section = 
   main_author :: "author option"  <=  None

(*
doc_class text_section = 
   main_author :: "string option"  <=  None
 *)  
   
doc_class introduction = text_section +
   comment :: string

doc_class technical = text_section +
   definition_list :: "string list" <=  "[]"
   formula :: "term list"
   
text{* A very rough formatting style could be modeled as follows:*}   
   
datatype mesure = points  "int" | inch "int" | textwidth "int"  (* given by the inverse of the integer *)   

datatype placement = left | center | right  
  
doc_class figure   = text_section +
   width   :: "mesure option"  <= "Some(textwidth 1)"    
   height  :: "mesure option"  <= "Some(textwidth 1)"
   scale   :: "int option"                              (* in per cent *)
   "file"  :: string
   plmt    :: placement 
   caption :: string

(* something similar on tables ? Idea: rough abstraction of table attributes in LaTeX *)
   
doc_class example    = text_section +
   comment :: "string"

doc_class conclusion = text_section +
   main_author :: "author option"  <=  None
   
doc_class related_work = conclusion +
   main_author :: "author option"  <=  None

doc_class bibliography =
   style :: "string option"  <=  "Some ''LNCS''"

text{* Besides subtyping, there is another relation between
       doc_classes: a class can be a \emph{monitor} to other ones,
       which is expressed by occurrence in the where clause.
       While sub-classing refers to data-inheritance of attributes,
       a monitor captures structural constraints -- the order --
       in which instances of monitored classes may occur.

       The control of monitors is done by the commands:
       -- monitor <doc-class>
       -- close_monitor <doc-class> 
       where the automaton of the monitor class is expected
       to be in a final state.

       Monitors can be nested.
 
       Classes neither directly or via inheritance indirectly
       mentioned in the monitor are \emph{independent} from
       a monitor and may occur freely. 
*}


-- \<open>underlying idea: capture the essence of a monitor class as trace.
                trace would be `predefined id` like `main` in C. \<close>
text{* @{cite bla} *}

doc_class article = 
   style_id :: string                <= "''LNCS''"
   version  :: "(int \<times> int \<times> int)"  <= "(0,0,0)"
   trace    :: "(title + subtitle + author+ abstract +
                introduction + technical + example +
                conclusion + bibliography) list"
   where "(title ~ 
           [subtitle] ~
           (author)+  ~ 
           abstract   ~
           introduction ~ 
           (technical || example)+ . 
           conclusion ~  
           bibliography)"



end

