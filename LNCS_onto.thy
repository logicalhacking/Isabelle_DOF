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
   keywds :: "string list"        -- None

doc_class introduction =
   main_author :: "author option" -- None

doc_class tech_section =
   main_author :: "author option" -- None

doc_class example_section =
   main_author :: "author option" -- None


doc_class conclusion =
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
   TS    :: "tech_section list"
   EXS   :: "example_section list"
   CON   :: "conclusion"
   where "(title . 
           [subtitle] .
           (author)+ .
           abstract .
           introduction . 
           (tech_section)+ . 
           conclusion . 
           bibliography)"

-- \<open>other idea: capture the essence of a monitor class as trace.
                trace would be `predefined id` like `main` in C.
   \<close>

doc_class article' = 
   trace :: "(title + subtitle + author+ abstract +
              introduction + tech_section + example_section +
              conclusion + bibliography) list"
   where "(title . 
           [subtitle] .
           (author)+ .
           abstract .
           introduction . 
           (tech_section | example_section)+ . 
           conclusion . 
           bibliography)"



end

