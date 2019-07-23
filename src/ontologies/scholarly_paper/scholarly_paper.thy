section\<open>An example ontology for a scholarly paper\<close>

theory scholarly_paper
   imports "../../DOF/Isa_COL"
begin

doc_class title =
   short_title :: "string option"  <=  "None"
    
doc_class subtitle =
   abbrev :: "string option"       <=  "None"
   
(* adding a contribution list and checking that it is cited as well in tech as in conclusion. ? *)

doc_class author =
   email       :: "string" <= "''''"
   http_site   :: "string" <= "''''"
   orcid       :: "string" <= "''''"
   affiliation :: "string"


doc_class abstract =
   keywordlist        :: "string list"   <= "[]" 
   principal_theorems :: "thm list"

doc_class text_section = text_element +
   main_author :: "author option"  <=  None
   fixme_list  :: "string list"    <=  "[]" 
   level       :: "int  option"    <=  "None"   
   (* this attribute enables doc-notation support section* etc.
      we follow LaTeX terminology on levels 
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
   
text\<open>A very rough formatting style could be modeled as follows:\<close>   

   
doc_class example    = text_section +
   comment :: "string"

doc_class "conclusion" = text_section +
   main_author :: "author option"  <=  None
   
doc_class related_work = "conclusion" +
   main_author :: "author option"  <=  None

doc_class bibliography = text_section +
   style       :: "string option"  <=  "Some ''LNCS''"

doc_class annex = "text_section" +
   main_author :: "author option"  <=  None


text\<open> Besides subtyping, there is another relation between
doc\_classes: a class can be a \<^emph>\<open>monitor\<close> to other ones,
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
            \<lbrace>introduction\<rbrace>\<^sup>+   ~~ 
            \<lbrace>technical || example\<rbrace>\<^sup>+ ~~
            \<lbrace>conclusion\<rbrace>\<^sup>+    ~~  
            bibliography     ~~
            \<lbrace>annex\<rbrace>\<^sup>* )"


ML\<open>
structure Scholarly_paper_trace_invariant =
struct 
local

fun group f g cidS [] = []
   |group f g cidS (a::S) = case find_first (f a) cidS of
                            NONE => [a] :: group f g cidS S
                          | SOME cid => let val (pref,suff) =  chop_prefix  (g cid) S
                                        in (a::pref)::(group f g cidS suff) end;

fun partition ctxt cidS trace = 
    let fun find_lead (x,_) = DOF_core.is_subclass ctxt x;
        fun find_cont cid (cid',_) =  DOF_core.is_subclass ctxt cid' cid
    in group find_lead find_cont cidS trace end;

fun dest_option _ (Const (@{const_name "None"}, _)) = NONE
  | dest_option f (Const (@{const_name "Some"}, _) $ t) = SOME (f t)

in 

fun check ctxt cidS mon_id pos =
    let val trace  = AttributeAccess.compute_trace_ML ctxt mon_id pos @{here}
        val groups = partition (Context.proof_of ctxt) cidS trace
        fun get_level_raw oid = AttributeAccess.compute_attr_access ctxt "level" oid @{here} @{here};
        fun get_level oid = dest_option (snd o HOLogic.dest_number) (get_level_raw (oid));
        fun check_level_hd a = case (get_level (snd a)) of
                                  NONE => error("Invariant violation: leading section" ^ snd a ^ 
                                                " must have lowest level")
                                | SOME X => X
        fun check_group_elem level_hd a = case (get_level (snd a)) of
                                              NONE => true
                                            | SOME y => if level_hd <= y then true
                                                        (* or < ? But this is too strong ... *)
                                                        else error("Invariant violation: "^
                                                                   "subsequent section " ^ snd a ^ 
                                                                   " must have higher level.");
        fun check_group [] = true
           |check_group [_] = true
           |check_group (a::S) = forall (check_group_elem (check_level_hd a)) (S)
    in if forall check_group groups then () 
       else error"Invariant violation: leading section must have lowest level" 
    end
end

end
\<close>


setup\<open> let val cidS = ["scholarly_paper.introduction","scholarly_paper.technical", 
                       "scholarly_paper.example", "scholarly_paper.conclusion"];
           fun body moni_oid _ ctxt = (Scholarly_paper_trace_invariant.check 
                                                    ctxt cidS moni_oid @{here};
                                       true)
       in  DOF_core.update_class_invariant "scholarly_paper.article" body end\<close>


(* some test code *)
ML\<open>
(*

val trace  = AttributeAccess.compute_trace_ML (Context.Proof @{context}) "this" @{here} @{here}
val groups = partition (  @{context}) cidS trace
val _::_::_::_:: _ ::_ ::_ ::a::_ = groups;
check;

fun get_level_raw oid = AttributeAccess.compute_attr_access (Context.Proof @{context}) "level" oid @{here} @{here};
fun get_level oid = dest_option (snd o HOLogic.dest_number) (get_level_raw (oid));
fun check_level_hd a = case (get_level (snd a)) of
                 NONE => error("Invariant violation: leading section" ^ snd a ^ 
                               " must have lowest level")
               | SOME X => X
fun check_group_elem level_hd a = case (get_level (snd a)) of
                            NONE => true
                          | SOME y => if y > level_hd then true
                                      else error("Invariant violation: subsequent section " ^ snd a ^ 
                                                 " must have higher level.");
fun check_group a = map (check_group_elem (check_level_hd (hd a))) (tl a) ;
*)
\<close>

end
