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

section\<open>An example ontology for a scholarly paper\<close>

theory scholarly_paper
   imports "../../DOF/Isa_COL"
begin

text\<open>Scholarly Paper provides a number of standard text - elements for scientific papers.
They were introduced in the following.\<close>

subsection\<open>General Paper Structuring Elements\<close>
doc_class title =
   short_title :: "string option"  <=  "None"
    
doc_class subtitle =
   abbrev ::      "string option"       <=  "None"
   
(* adding a contribution list and checking that it is cited as well in tech as in conclusion. ? *)

doc_class author =
   email       :: "string" <= "''''"
   http_site   :: "string" <= "''''"
   orcid       :: "string" <= "''''"
   affiliation :: "string"


doc_class abstract =
   keywordlist        :: "string list"   <= "[]" 
   principal_theorems :: "thm list"

text\<open>Scholarly Paper is oriented towards the classical domains in science:
\<^enum> mathematics
\<^enum> informatics
\<^enum> natural sciences
\<^enum> technology (= engineering)

which we formalize into:\<close>

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


doc_class "conclusion" = text_section +
   main_author :: "author option"  <=  None
   
doc_class related_work = "conclusion" +
   main_author :: "author option"  <=  None

doc_class bibliography = text_section +
   style       :: "string option"  <=  "Some ''LNCS''"

doc_class annex = "text_section" +
   main_author :: "author option"  <=  None

(*
datatype sc_dom = math | info | natsc | eng 
*)


subsection\<open>Introductions\<close>

doc_class introduction = text_section +
   comment :: string
   claims  :: "thm list"

text\<open>Technical text-elements posses a status: they can be either an \<^emph>\<open>informal explanation\<close> /
description or a kind of introductory text to definition etc. or a \<^emph>\<open>formal statement\<close> similar
to :

\<^bold>\<open>Definition\<close> 3.1: Security. 
As Security of the system we define etc...

A formal statement can, but must not have a reference to true formal Isabelle/Isar definition. 
\<close>

subsection\<open>Technical Content and its Formats\<close>

datatype status = semiformal | description

text\<open>The class \<^verbatim>\<open>technical\<close> regroups a number of text-elements that contain typical 
"technical content" in mathematical or engineering papers: definitions, theorems, lemmas, examples.  \<close>

(* OPEN PROBLEM: connection between referentiable and status. This should be explicit 
   and computable. *)

(* TODO : RENAME "tag" by "short_name" *)

doc_class technical = text_section +
   definition_list :: "string list" <=  "[]"
   status :: status <= "description"
   formal_results  :: "thm list"

type_synonym tc = technical (* technical content *)



subsection\<open>Mathematical Content\<close>

text\<open>We follow in our enumeration referentiable mathematical content class the AMS style and its
provided \<^emph>\<open>theorem environments\<close> (see \<^verbatim>\<open>texdoc amslatex\<close>). We add, however, the concepts 
\<^verbatim>\<open>axiom\<close>, \<^verbatim>\<open>rule\<close> and \<^verbatim>\<open>assertion\<close> to the list. A particular advantage of \<^verbatim>\<open>texdoc amslatex\<close> is 
that it is well-established and compatible with many LaTeX - styles.\<close>

datatype math_content_class = "defn" | "axm" | "thm" | "lem" | "cor" | "prop" 
                            | "ex" | "rule" | "assn"

(*
thm Theorem Italic 
cor Corollary Italic 
lem Lemma Italic
prop Proposition 
defn Definition
ex Example 

rem Remark
notation
terminology
*)
text\<open>Instances of the \<open>doc_class\<close> \<^verbatim>\<open>math_content\<close> are by definition @{term "semiformal"}; they may
be non-referential, but in this case they will not have a @{term "short_name"}.\<close>

doc_class math_content = tc +
   referentiable :: bool <= True
   short_name    :: string <= "''''"
   status        :: status <= "semiformal"
   mcc           :: "math_content_class" <= "thm" 
   invariant s1  :: "\<lambda> \<sigma>::math_content. \<not>referentiable \<sigma> \<longrightarrow> short_name \<sigma> = ''''"
   invariant s2  :: "\<lambda> \<sigma>::math_content. status \<sigma> = semiformal"
type_synonym math_tc = math_content


find_theorems name:"s1" name:"scholarly"

(* type qualification is a work around *)

text\<open>The intended use for the \<open>doc_class\<close>es \<^verbatim>\<open>math_motivation\<close> (or \<^verbatim>\<open>math_mtv\<close> for short),
     \<^verbatim>\<open>math_explanation\<close> (or \<^verbatim>\<open>math_exp\<close> for short) and 
     \<^verbatim>\<open>math_example\<close> (or \<^verbatim>\<open>math_ex\<close> for short)
     are \<^emph>\<open>informal\<close> descriptions of semi-formal definitions (by inheritance).
     Math-Examples can be made referentiable triggering explicit, numbered presentations.\<close>
doc_class math_motivation  = tc +  
   referentiable :: bool <= False
type_synonym math_mtv = math_motivation

doc_class math_explanation  = tc +
   referentiable :: bool <= False
type_synonym math_exp = math_explanation

doc_class math_example  = tc +
   referentiable :: bool <= False
   short_name    :: string <= "''''"
   invariant s3  :: "\<lambda> \<sigma>::math_example. \<not>referentiable \<sigma> \<longrightarrow> short_name \<sigma> = ''''"
type_synonym math_ex = math_example


text\<open>The intended use for the \<open>doc_class\<close> \<^verbatim>\<open>math_semiformal_statement\<close> (or \<^verbatim>\<open>math_sfs\<close> for short) 
     are semi-formal mathematical content (definition, lemma, etc.). They are referentiable entities.
     They are NOT formal, i.e. Isabelle-checked formal content, but can be in close link to these.\<close>
doc_class math_semiformal  = math_content +
   referentiable :: bool <= True
type_synonym math_sfc = math_semiformal

subsection\<open>old style onto model.\<close>

text\<open>A rough structuring is modeled as follows:\<close>   
(* non-evident-statement *)
doc_class "definition"  = tc +
   referentiable :: bool <= True
   tag :: "string" <=  "''''"

doc_class "theorem"     = tc +
   referentiable :: bool <= True
   tag :: "string" <=  "''''"

text\<open>Note that the following two text-elements are currently set to no-keyword in LNCS style.\<close>
doc_class "lemma"     = tc +
   referentiable :: bool <= "True"
   tag :: "string" <=  "''''"

doc_class "corollary"     = tc +
   referentiable :: bool <= "True"
   tag :: "string" <=  "''''"

subsection\<open>Example Statements\<close>

text\<open> \<^verbatim>\<open>examples\<close> are currently considered \<^verbatim>\<open>technical\<close>. Is a main category to be refined
      via inheritance. \<close> 

doc_class example       = technical +
   referentiable :: bool <= True
   tag :: "string" <=  "''''"

subsection\<open>Code Statement Elements\<close>

doc_class "code"     = technical +
   checked :: bool <=  "False"
   tag :: "string" <=  "''''"

text\<open>The @{doc_class "code"} is a general stub for free-form and type-checked code-fragments
such as:
\<^enum> SML code
\<^enum> bash code
\<^enum> isar code (although this might be an unwanted concurrence to the Isabelle standard cartouche)
\<^enum> C code.

it is intended that later refinements of this "stub" as done in \<^verbatim>\<open>Isabelle_C\<close> which come with their
own content checking and, of course, presentation styles. 
\<close>


doc_class "SML"     = code +
   checked :: bool <=  "False"

doc_class "ISAR"     = code +
   checked :: bool <=  "False"

doc_class "LATEX"     = code +
   checked :: bool <=  "False"



subsection\<open>Content in Engineering/Tech Papers \<close>


doc_class engineering_statement = tc +
   short_name :: string <= "''''"
   status     :: status
type_synonym eng_stmt = engineering_statement

doc_class "experiment"  = eng_stmt +
   tag :: "string" <=  "''''"

doc_class "evaluation"  = eng_stmt +
   tag :: "string" <=  "''''"

doc_class "data"  = eng_stmt +
   tag :: "string" <=  "''''"


subsection\<open>Structuring Enforcement in Engineering/Math Papers \<close>
(* todo : could be finer *)

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
   accepts "(title           ~~ 
            \<lbrakk>subtitle\<rbrakk>        ~~
            \<lbrace>author\<rbrace>\<^sup>+         ~~ 
            abstract          ~~
            \<lbrace>introduction\<rbrace>\<^sup>+   ~~ 
            \<lbrace>technical\<rbrace>\<^sup>+      ~~
            \<lbrace>conclusion\<rbrace>\<^sup>+     ~~  
            bibliography      ~~
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

