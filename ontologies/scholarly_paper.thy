section{* An example ontology for a scholarly paper*}

theory scholarly_paper
   imports "../Isa_COL"
begin

doc_class title =
   short_title :: "string option"  <=  "None"
    
doc_class subtitle =
   abbrev :: "string option"       <=  "None"
   
-- \<open>adding a contribution list and checking that it is cited as well in tech as in conclusion. ? \<close>

doc_class author =
   email       :: "string" <= "''''"
   http_site   :: "string" <= "''''"
   orcid       :: "string" <= "''''"
   affiliation :: "string"

doc_class abstract =
   keywordlist        :: "string list"   <= "[]" 
   principal_theorems :: "thm list"

doc_class text_section = 
   main_author :: "author option"  <=  None
   fixme_list  :: "string list"    <=  "[]" 
   level       :: "int  option"    <=  "None"   
                                  (* we follow LaTeX terminology on levels 
                                               part          = Some -1
                                               chapter       = Some 0
                                               section       = Some 1
                                               subsection    = Some 2
                                               subsubsection = Some 3
                                      ... *)
   (* for scholarly paper: invariant level > 0 *)

doc_class introduction = text_section +
   comment :: string
   claims  :: "thm list"

doc_class technical = text_section +
   definition_list :: "string list" <=  "[]"
   formal_results  :: "thm list"
   
text{* A very rough formatting style could be modeled as follows:*}   

   
doc_class example    = text_section +
   comment :: "string"

doc_class "conclusion" = text_section +
   main_author :: "author option"  <=  None
   
doc_class related_work = "conclusion" +
   main_author :: "author option"  <=  None

doc_class bibliography =
   style :: "string option"  <=  "Some ''LNCS''"

text\<open> Besides subtyping, there is another relation between
doc_classes: a class can be a \<^emph>\<open>monitor\<close> to other ones,
which is expressed by occurrence in the where clause.
While sub-classing refers to data-inheritance of attributes,
a monitor captures structural constraints -- the order --
in which instances of monitored classes may occur.

The control of monitors is done by the commands:
\<^item> \<^verbatim>\<open> monitor <oid::class_type, <attributes-defs> > \<close>
\<^item> \<^verbatim>\<open> close_monitor <oid[::class_type],<attributes-updates>> \<close>

where the automaton of the monitor class is expected
to be in a final state.

Monitors can be nested.

Classes neither directly or  indirectly (via inheritance)
mentioned in the monitor clause are \<^emph>\<open>independent\<close> from
the monitor and may occur freely, \ie{} in arbitrary order.n \<close>


text \<open>underlying idea: a monitor class automatically receives a  
    \<^verbatim>\<open>trace\<close> attribute in which a list of observed class-ids is maintained.
    The \<^verbatim>\<open>trace\<close> is a \<^emph>\<open>`predefined id`\<close> like \<^verbatim>\<open>main\<close> in C. It can be accessed
    like any other attribute of a class instance, \ie{} a document item.\<close>

doc_class article = 
   style_id :: string                <= "''LNCS''"
   version  :: "(int \<times> int \<times> int)"  <= "(0,0,0)"
   accepts "(title        ~~ 
            \<lbrakk>subtitle\<rbrakk>    ~~
            \<lbrace>author\<rbrace>\<^sup>+     ~~ 
            abstract      ~~
            introduction  ~~ 
            \<lbrace>technical || example\<rbrace>\<^sup>+ ~~
            conclusion   ~~  
            bibliography)"

gen_sty_template


end

