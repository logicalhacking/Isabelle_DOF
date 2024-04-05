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
           \<lbrace>technical || example || float \<rbrace>\<^sup>+ ~~ 
           \<lbrace>conclusion\<rbrace>\<^sup>+           ~~  
           bibliography            ~~ 
           \<lbrakk>index\<rbrakk> ~~ \<lbrace>annex\<rbrace>\<^sup>*   )"







section\<open>Experimental\<close>

ML\<open> fun get_class_2_ML ctxt (str,_) =
        let val thy = Context.theory_of ctxt
            val DOF_core.Onto_Class S = (DOF_core.get_onto_class_global' str thy) 
        in ML_Syntax.atomic(ML_Syntax.print_string(@{make_string} S)) end \<close>

setup\<open>ML_Antiquotation.inline  \<^binding>\<open>doc_class2\<close>  
        (fn (ctxt,toks) => (AttributeAccess.parse_cid >> get_class_2_ML ctxt) (ctxt, toks))\<close>

ML\<open>@{term \<open>a + b\<close>}\<close>

ML\<open>@{doc_class2 "report"}\<close>

ML\<open>
   fun constant_def (decl, spec, prems, params) = #2 o Specification.definition decl params prems spec
   fun meta_eq_const T = Const (\<^const_name>\<open>Pure.eq\<close>, T --> T --> propT);
   fun mk_meta_eq (t, u) = meta_eq_const (fastype_of t) $ t $ u;
   val rexp_ty = @{typ "doc_class rexp"}

   fun define (binding, rhs) (lthy)=  
            let val Const(cname, _) = Syntax.read_term lthy (Binding.name_of binding)
                val lhs = Const(cname, rexp_ty)
                val bdg = Binding.suffix_name "_monitor" binding
                val eq =  mk_meta_eq(Free(Binding.name_of bdg, rexp_ty),rhs)
                val args = (SOME(bdg,NONE,NoSyn), (Binding.empty_atts,eq),[],[]) ;
            in  constant_def args lthy end;
\<close>



ML\<open> val DOF_core.Onto_Class S = (DOF_core.get_onto_class_global' "report" @{theory}) \<close>
setup\<open>Named_Target.theory_map(define (#name S, hd (#rex S))) \<close>


ML\<open> val DOF_core.Onto_Class S = (DOF_core.get_onto_class_global' "article" @{theory}) \<close>
setup\<open>Named_Target.theory_map(define (#name S, hd (#rex S))) \<close>


(* switch on regexp syntax *)
notation Star  ("\<lbrace>(_)\<rbrace>\<^sup>*" [0]100)
notation Plus  (infixr "||" 55)
notation Times (infixr "~~" 60)
notation Atom  ("\<lfloor>_\<rfloor>" 65)


lemma regexp_sub : "a \<le> b \<Longrightarrow> L\<^sub>s\<^sub>u\<^sub>b (\<lfloor>a\<rfloor>) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (\<lfloor>b\<rfloor>)"
  using dual_order.trans by auto


lemma regexp_seq_mono:
      "Lang(a) \<subseteq> Lang (a') \<Longrightarrow> Lang(b) \<subseteq> Lang (b') \<Longrightarrow> Lang(a ~~ b) \<subseteq> Lang(a' ~~ b')"  by auto

lemma regexp_seq_mono':
      "L\<^sub>s\<^sub>u\<^sub>b(a) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (a') \<Longrightarrow> L\<^sub>s\<^sub>u\<^sub>b(b) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (b') \<Longrightarrow> L\<^sub>s\<^sub>u\<^sub>b(a ~~ b) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b(a' ~~ b')"  by auto

lemma regexp_alt_mono :"Lang(a) \<subseteq> Lang (a') \<Longrightarrow> Lang(a || b) \<subseteq> Lang(a' || b)"  by auto

lemma regexp_alt_mono' :"L\<^sub>s\<^sub>u\<^sub>b(a) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (a') \<Longrightarrow> L\<^sub>s\<^sub>u\<^sub>b(a || b) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b(a' || b)"  by auto

lemma regexp_alt_commute : "Lang(a || b) = Lang(b || a)"  by auto

lemma regexp_alt_commute' : "L\<^sub>s\<^sub>u\<^sub>b(a || b) = L\<^sub>s\<^sub>u\<^sub>b(b || a)"  by auto

lemma regexp_unit_right : "Lang (a) = Lang (a ~~ One) " by simp 

lemma regexp_unit_right' : "L\<^sub>s\<^sub>u\<^sub>b (a) = L\<^sub>s\<^sub>u\<^sub>b (a ~~ One) " by simp 

lemma regexp_unit_left  : "Lang (a) = Lang (One ~~ a) " by simp 

lemma regexp_unit_left'  : "L\<^sub>s\<^sub>u\<^sub>b (a) = L\<^sub>s\<^sub>u\<^sub>b (One ~~ a) " by simp

lemma opt_star_incl :"Lang (opt a) \<subseteq> Lang (Star a)"  by (simp add: opt_def subset_iff)

lemma opt_star_incl':"L\<^sub>s\<^sub>u\<^sub>b (opt a) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (Star a)"  by (simp add: opt_def subset_iff)

lemma rep1_star_incl:"Lang (rep1 a) \<subseteq> Lang (Star a)"
  unfolding rep1_def by(subst L_Star, subst L_Conc)(force)

lemma rep1_star_incl':"L\<^sub>s\<^sub>u\<^sub>b (rep1 a) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (Star a)"
  unfolding rep1_def by(subst L\<^sub>s\<^sub>u\<^sub>b_Star, subst L\<^sub>s\<^sub>u\<^sub>b_Conc)(force)

lemma cancel_rep1 : "Lang (a) \<subseteq> Lang (rep1 a)"
  unfolding rep1_def by auto

lemma cancel_rep1' : "L\<^sub>s\<^sub>u\<^sub>b (a) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (rep1 a)"
  unfolding rep1_def by auto

lemma seq_cancel_opt : "Lang (a) \<subseteq> Lang (c) \<Longrightarrow> Lang (a) \<subseteq> Lang (opt b ~~ c)"
  by(subst regexp_unit_left, rule regexp_seq_mono)(simp_all add: opt_def)

lemma seq_cancel_opt' : "L\<^sub>s\<^sub>u\<^sub>b (a) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (c) \<Longrightarrow> L\<^sub>s\<^sub>u\<^sub>b (a) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (opt b ~~ c)"
  by(subst regexp_unit_left', rule regexp_seq_mono')(simp_all add: opt_def)

lemma seq_cancel_Star : "Lang (a) \<subseteq> Lang (c) \<Longrightarrow> Lang (a) \<subseteq> Lang (Star b ~~ c)" 
  by auto

lemma seq_cancel_Star' : "L\<^sub>s\<^sub>u\<^sub>b (a) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (c) \<Longrightarrow> L\<^sub>s\<^sub>u\<^sub>b (a) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (Star b ~~ c)" 
  by auto

lemma mono_Star : "Lang (a) \<subseteq> Lang (b) \<Longrightarrow> Lang (Star a) \<subseteq> Lang (Star b)" 
  by(auto)(metis in_star_iff_concat order.trans)

lemma mono_Star' : "L\<^sub>s\<^sub>u\<^sub>b (a) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (b) \<Longrightarrow> L\<^sub>s\<^sub>u\<^sub>b (Star a) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (Star b)" 
  by(auto)(metis in_star_iff_concat order.trans)

lemma mono_rep1_star:"Lang (a) \<subseteq> Lang (b) \<Longrightarrow> Lang (rep1 a) \<subseteq> Lang (Star b)"
  using mono_Star rep1_star_incl by blast

lemma mono_rep1_star':"L\<^sub>s\<^sub>u\<^sub>b (a) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (b) \<Longrightarrow> L\<^sub>s\<^sub>u\<^sub>b (rep1 a) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b (Star b)"
  using mono_Star' rep1_star_incl' by blast


text\<open>Not a terribly deep theorem, but an interesting property of consistency between
ontologies - so, a lemma that shouldn't break if the involved ontologies were changed.
It reads as follows: 
"The structural language of articles should be included in the structural language of
reports, that is to say, reports should just have a richer structure than ordinary papers." \<close>

theorem articles_sub_reports: \<open>(Lang article_monitor) \<subseteq> Lang report_monitor\<close>
  unfolding article_monitor_def report_monitor_def
  apply(rule regexp_seq_mono[OF subset_refl] | rule seq_cancel_opt | rule subset_refl)+ 
  done

text\<open>The proof proceeds by blindly applying the monotonicity rules 
     on the language of regular expressions.\<close>

print_doc_classes
text\<open>All Class-Id's --- should be generated.\<close>

lemmas class_ids =
             SML_def code_def annex_def  title_def figure_def chapter_def  article_def theorem_def 
             paragraph_def tech_code_def assumption_def   definition_def  hypothesis_def 
             eng_example_def text_element_def math_content_def tech_example_def subsubsection_def  
             engineering_content_def data_def float_def axiom_def LATEX_def author_def listing_def 
             abstract_def assertion_def technical_def background_def evaluation_def math_proof_def 
             math_formal_def bibliography_def math_example_def text_section_def conclusion_stmt_def
             math_explanation_def ISAR_def frame_def lemma_def index_def report_def section_def 
             subtitle_def corollary_def subsection_def conclusion_def experiment_def consequence_def
             proposition_def introduction_def related_work_def front_matter_def math_motivation_def
             example_def table_of_contents_def tech_definition_def premise_def




definition allClasses 
  where \<open>allClasses \<equiv> 
             {SML, code, annex, title,figure,chapter, article, theorem, paragraph,
              tech_code, assumption, definition, hypothesis, eng_example, text_element,
              math_content,tech_example, subsubsection,tech_definition,
              engineering_content,data,float,axiom,LATEX,author,listing, example,abstract,
              assertion,technical,background,evaluation,math_proof,math_formal,bibliography,
              math_example,text_section,conclusion_stmt,math_explanation,ISAR,frame,
              lemma,index,report,section,premise,subtitle,corollary,subsection,conclusion,
              experiment, consequence,proposition,introduction,related_work,front_matter,
              math_motivation,table_of_contents}\<close>

text\<open>A rudimentary fragment of the class hierarchy re-modeled on classid's :\<close>


definition cid_of where \<open>cid_of = inv Regular_Exp.Atom\<close>

lemma Atom_inverse[simp]:\<open>cid_of (Regular_Exp.Atom a) = a\<close>
  unfolding cid_of_def by (meson UNIV_I f_inv_into_f image_eqI rexp.inject(1))



definition doc_class_rel
  where  \<open>doc_class_rel \<equiv> {(cid_of proposition,cid_of math_content),
                            (cid_of listing,cid_of float),
                            (cid_of figure,cid_of float)} \<close>

instantiation "doc_class" :: ord
begin

definition
  less_eq_doc_class: "x \<le> y \<longleftrightarrow> (x,y) \<in> doc_class_rel\<^sup>*"

definition
  less_doc_class: "(x::doc_class) < y \<longleftrightarrow> (x \<le> y \<and> \<not> y \<le> x)"

instance .. 

end

lemma drc_acyclic : "acyclic doc_class_rel"
  proof -
        let ?measure = "(\<lambda>x.3::int)(cid_of float := 0, cid_of math_content := 0, 
                                    cid_of listing := 1, cid_of figure := 1, cid_of proposition := 1)"
  show ?thesis
        unfolding doc_class_rel_def
        apply(rule_tac f = "?measure" in acyclicI_order)
        by(simp only: class_ids)(auto)
  qed


instantiation "doc_class" :: order
begin
instance 
   proof 
     fix x::"doc_class"
     show \<open>x \<le> x\<close>   
       unfolding less_eq_doc_class by simp
   next
     fix x y z:: "doc_class"
     show \<open>x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z\<close>
       unfolding less_eq_doc_class
       by force
   next
     fix x y::"doc_class"
     have * : "antisym (doc_class_rel\<^sup>*)" 
       by (simp add: acyclic_impl_antisym_rtrancl drc_acyclic)    
     show \<open>x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y\<close>
       apply(insert antisymD[OF *])
       using less_eq_doc_class by auto
   next
     fix x y::"doc_class"
     show \<open>(x < y) = (x \<le> y \<and> \<not> y \<le> x)\<close> 
       by(simp add: less_doc_class)
   qed
end

theorem articles_Lsub_reports: \<open>(L\<^sub>s\<^sub>u\<^sub>b article_monitor) \<subseteq> L\<^sub>s\<^sub>u\<^sub>b report_monitor\<close>
  unfolding article_monitor_def report_monitor_def
  by (meson order_refl regexp_seq_mono' seq_cancel_opt')


end
