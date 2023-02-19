(*************************************************************************
 * Copyright (C) 
 *               2019      The University of Exeter 
 *               2018-2019 The University of Paris-Saclay
 *               2018      The University of Sheffield
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

chapter\<open>An example ontology for a math paper\<close>

theory small_math
   imports 
"document_setup"
"Isabelle_DOF.Isa_COL"
begin

doc_class title =
   short_title :: "string option"  <=  "None"

doc_class author =
   email       :: "string" <= "''''"

datatype classification = algebra | geometry | topology

doc_class abstract =
    keyword_list :: "classification list"   <= "[]" 

doc_class text_section = 
    authored_by :: "author set"   <=  "{}"
    level       :: "int  option"  <=  "None"   
    (* this attribute enables doc-notation support section* etc.
       we follow LaTeX terminology on levels 
                 part          = Some -1
                 chapter       = Some 0
                 section       = Some 1
                 subsection    = Some 2
                 subsubsection = Some 3
        ... *)
    (* for scholarly paper: invariant level > 0 *)

type_synonym notion = string

doc_class introduction = text_section +
    uses :: "notion set"

doc_class contribution_claim = introduction +
    based_on :: "notion list"

doc_class technical = text_section +
    formal_results  :: "thm list"

doc_class "definition" = technical +
    is_formal :: "bool"
    property  :: "term list" <= "[]"

datatype kind = expert_opinion | argument | "proof"

doc_class result = technical +
    evidence  :: kind 
    c  :: "thm list" <= "[]"



ML\<open>
fn thy =>
let fun check_invariant_invariant oid {is_monitor:bool} ctxt =
      let val kind_term = ISA_core.compute_attr_access ctxt "kind" oid NONE @{here} 
          val property_termS = ISA_core.compute_attr_access ctxt "property" oid NONE @{here} 
          val tS = HOLogic.dest_list property_termS
      in  case kind_term of
            @{term "proof"} => if not(null tS) then true
                               else error("class class invariant violation") 
           | _ => false
      end
      val binding = DOF_core.binding_from_onto_class_pos "result" thy
in DOF_core.add_ml_invariant binding check_invariant_invariant thy end
\<close>

(*setup\<open>DOF_core.add_ml_invariant "small_math.result" check_invariant_invariant\<close>*)


doc_class example    = technical +
    referring_to :: "(notion + definition) set" <=  "{}"

doc_class "conclusion" = text_section +
    establish   :: "(contribution_claim \<times> result) set"

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
    accepts "(title           ~~ \<lbrace>author\<rbrace>\<^sup>+               ~~   abstract      ~~
             \<lbrace>introduction\<rbrace>\<^sup>+  ~~  \<lbrace>technical || example\<rbrace>\<^sup>+ ~~ \<lbrace>conclusion\<rbrace>\<^sup>+)"


ML\<open>
structure Small_Math_trace_invariant =
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

fun check ctxt cidS mon_id pos_opt =
    let val trace  = AttributeAccess.compute_trace_ML ctxt mon_id pos_opt @{here}
        val groups = partition (Context.proof_of ctxt) cidS trace
        fun get_level_raw oid = ISA_core.compute_attr_access ctxt "level" oid NONE @{here};
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

setup\<open>
fn thy =>
let val cidS = ["small_math.introduction","small_math.technical", "small_math.conclusion"];
           fun body moni_oid _ ctxt = (Small_Math_trace_invariant.check  ctxt cidS moni_oid NONE;
                                       true)
    val ctxt = Proof_Context.init_global thy
    val binding = DOF_core.binding_from_onto_class_pos "article" thy
in DOF_core.add_ml_invariant binding body thy end
\<close>

end

