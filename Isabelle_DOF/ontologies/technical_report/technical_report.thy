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

theory technical_report
   imports "Isabelle_DOF.scholarly_paper"
begin              

define_ontology "DOF-technical_report.sty" "Writing technical reports."

(* for reports paper: invariant: level \<ge> -1 *)

section\<open>More Global Text Elements for Reports\<close>

doc_class table_of_contents =
   bookmark_depth :: int <= 3
   depth          :: int <= 3

doc_class front_matter = 
   front_matter_style :: string    (* TODO Achim :::: *)

doc_class index =
   kind  :: "doc_class" 
   level :: "int option"

section\<open>Code Statement Elements\<close>

doc_class "code"     = technical +
   checked :: bool     <=  "False"
   caption :: "string" <=  "''''"

typ code

text\<open>The \<^doc_class>\<open>code\<close> is a general stub for free-form and type-checked code-fragments such as:
        \<^enum> SML code                                
        \<^enum> bash code
        \<^enum> isar code (although this might be an unwanted concurrence 
          to the Isabelle standard cartouche)
        \<^enum> C code.

It is intended that later refinements of this "stub" as done in \<^verbatim>\<open>Isabelle_C\<close> which come with their
own content checking and presentation styles. 
\<close>

doc_class "SML"     = code +
   checked :: bool <=  "False"

doc_class "ISAR"     = code +
   checked :: bool <=  "False"

doc_class "LATEX"     = code +
   checked :: bool <=  "False"

print_doc_class_template "SML" (* just a sample *)


doc_class report = 
   style_id :: string                <= "''LNCS''"
   version  :: "(int \<times> int \<times> int)"  <= "(0,0,0)"
   accepts "(title                 ~~ 
           \<lbrakk>subtitle\<rbrakk>              ~~
           \<lbrace>author\<rbrace>\<^sup>+               ~~ 
           \<lbrakk>front_matter\<rbrakk>          ~~
           abstract                ~~
           \<lbrakk>table_of_contents\<rbrakk>     ~~
           \<lbrace>introduction\<rbrace>\<^sup>+         ~~ 
           \<lbrace>background\<rbrace>\<^sup>*           ~~ 
           \<lbrace>technical || example \<rbrace>\<^sup>+ ~~ 
           \<lbrace>conclusion\<rbrace>\<^sup>+           ~~  
           bibliography            ~~ 
           \<lbrakk>index\<rbrakk> ~~ \<lbrace>annex\<rbrace>\<^sup>*   )"


(*
ML\<open>@{doc_class "report"}\<close>
*)
ML\<open> fun get_class_2_ML ctxt (str,_) =
        let val thy = Context.theory_of ctxt
            val DOF_core.Onto_Class S = (DOF_core.get_onto_class_global' str thy) 
         in ML_Syntax.atomic(ML_Syntax.print_string(@{make_string} S)) end \<close>

setup\<open>ML_Antiquotation.inline  \<^binding>\<open>doc_class2\<close>  
               (fn (ctxt,toks) => (AttributeAccess.parse_cid >> get_class_2_ML ctxt) (ctxt, toks))\<close>

ML\<open>@{term \<open>a + b\<close>}\<close>

ML\<open>@{doc_class2 "report"}\<close>

ML\<open>fun constant_def (decl, spec, prems, params) = #2 o Specification.definition decl params prems spec\<close>


ML\<open> val DOF_core.Onto_Class S = (DOF_core.get_onto_class_global' "report" @{theory});
    val regexp = #rex S 
    val binding = #name S 
    val doc_class_ty = @{typ doc_class}
    val rexp_ty = @{typ "doc_class rexp"}
    fun meta_eq_const T = Const (\<^const_name>\<open>Pure.eq\<close>, T --> T --> propT);
    fun mk_meta_eq (t, u) = meta_eq_const (fastype_of t) $ t $ u;

\<close>
    

ML\<open>
   fun define (binding, rhs) (lthy)=  
            let val Const(cname, _) = Syntax.read_term lthy (Binding.name_of binding)
                val lhs = Const(cname, rexp_ty)
                val bdg = Binding.suffix_name "_monitor" binding
                val eq =  mk_meta_eq(Free(Binding.name_of bdg, rexp_ty),rhs)
                val args = (SOME(bdg,NONE,NoSyn), (Binding.empty_atts,eq),[],[]) ;
            in  constant_def args lthy end;
\<close>

setup\<open>Named_Target.theory_map(define (binding, hd regexp)) \<close>

ML\<open>
val DOF_core.Onto_Class S = (DOF_core.get_onto_class_global' "article" @{theory});
    val regexp = #rex S 
    val binding = #name S \<close>

setup\<open>Named_Target.theory_map(define (binding, hd regexp)) \<close>

find_theorems (500) name:report_rexp
thm article_def report_def title_def subtitle_def introduction_def


notation Star  ("\<lbrace>(_)\<rbrace>\<^sup>*" [0]100)
notation Plus  (infixr "||" 55)
notation Times (infixr "~~" 60)
notation Atom  ("\<lfloor>_\<rfloor>" 65)

lemma regexp_seq_mono : 
      "Lang(a) \<subseteq> Lang (a') \<Longrightarrow> Lang(b) \<subseteq> Lang (b') \<Longrightarrow> Lang(a ~~ b) \<subseteq> Lang(a' ~~ b')"
  by auto

lemma regexp_unit_right : "Lang (a) = Lang (a ~~ One) " by simp 
lemma regexp_unit_left  : "Lang (a) = Lang (One ~~ a) " by simp 

lemma opt_star_incl :"Lang (opt a) \<subseteq> Lang (Star a)"  by (simp add: opt_def subset_iff)
lemma rep1_star_incl:"Lang (rep1 a) \<subseteq> Lang (Star a)" 
  unfolding rep1_def by(subst L_Star, subst L_Conc)(force)
lemma cancel_rep1 : "Lang (a) \<subseteq> Lang (rep1 a)"
  unfolding rep1_def  by auto


lemma seq_cancel_opt : "Lang (a) \<subseteq> Lang (c) \<Longrightarrow> Lang (a) \<subseteq> Lang (opt b ~~ c)"
  by(subst regexp_unit_left, rule regexp_seq_mono)(simp_all add: opt_def)
  
lemma seq_cancel_Star : "Lang (a) \<subseteq> Lang (c) \<Longrightarrow> Lang (a) \<subseteq> Lang (Star b ~~ c)" 
  by auto

text\<open>Not a terribly deep theorem, but an interesting property of consistency between
ontologies - so, a lemma that shouldn't break if the involved ontologies were changed:
the structural language of articles should be included in the structural language of 
reports, that is to say, reports should just have a richer structure than ordinary papers. \<close>

theorem articles_sub_reports: \<open>(Lang article_monitor) \<subseteq> Lang report_monitor\<close>
  unfolding article_monitor_def report_monitor_def
  apply(rule regexp_seq_mono[OF subset_refl] | rule seq_cancel_opt | rule subset_refl)+ 
  done


end
