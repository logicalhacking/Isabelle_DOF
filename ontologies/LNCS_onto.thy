text{* dfgdfg n*}

theory LNCS_onto
  imports "../Isa_DOF"
begin

doc_class title =
   short_title :: "string option" -- None
     
doc_class subtitle =
   abbrev :: "string option"      -- None
   
-- \<open>adding a contribution list and checking that it is cited as well in tech as in conclusion. ? \<close>

doc_class author =
   affiliation :: "string"

doc_class abstract =
   keyword_list :: "string list"        -- None

doc_class text_section = 
   main_author :: "author option" -- None

doc_class introduction = text_section +
   comment :: string

doc_class technical = text_section +
   definition_list :: "string list" -- "[]"

doc_class example   = text_section +
   comment :: string

doc_class conclusion = text_section +
   main_author :: "author option" -- None
   
doc_class related_work = conclusion +
   main_author :: "author option" -- None

doc_class bibliography =
   style :: "string option" -- "''LNCS''"

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


doc_class article = 
   T     :: "title option"     -- None
   ST    :: "subtitle option"  -- None
   AS    :: "author list"
   ABS   :: "abstract option"
   INTRO :: "introduction option" 
   TS    :: "technical list"
   EXS   :: "example list"
   CON   :: "conclusion"
   where "(title . 
           [subtitle] .
           (author)+ .
           abstract .
           introduction . 
           (technical | example)+ . 
           conclusion . 
           bibliography)"

-- \<open>other idea: capture the essence of a monitor class as trace.
                trace would be `predefined id` like `main` in C. \<close>
text{* @{cite bla} *}

doc_class article' = 
   trace :: "(title + subtitle + author+ abstract +
              introduction + technical + example +
              conclusion + bibliography) list"
   where "(title . 
           [subtitle] .
           (author)+ .
           abstract .
           introduction . 
           (technical | example)+ . 
           conclusion . 
           bibliography)"



end

