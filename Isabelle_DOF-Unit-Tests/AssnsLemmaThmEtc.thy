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

chapter\<open>Testing Freeform and Formal Elements from the scholarly-paper Ontology\<close>

theory 
  AssnsLemmaThmEtc
imports 
  "Isabelle_DOF-Ontologies.Conceptual"  
  "Isabelle_DOF.scholarly_paper"
  "Isabelle_DOF_Unit_Tests_document"
  TestKit
begin

section\<open>Test Objective\<close>

text\<open>Testing Core Elements for \<^theory>\<open>Isabelle_DOF.scholarly_paper\<close> wrt. to 
existance, controlability via implicit and explicit default classes, and potential 
LaTeX Layout.\<close>

text\<open>Current status:\<close>
print_doc_classes
print_doc_items


section\<open>An Example for use-before-declaration of Formal Content\<close>

text*[aa::F, properties = "[@{term ''True''}]"]
\<open>Our definition of the HOL-Logic has the following properties:\<close>
assert*\<open>F.properties @{F \<open>aa\<close>} = [@{term ''True''}]\<close>

text\<open>For now, as the term annotation is not bound to a meta logic which will translate
\<^term>\<open>[@{term ''True''}]\<close> to \<^term>\<open>[True]\<close>, we can not use the HOL \<^const>\<open>True\<close> constant
in the assertion.\<close>

ML\<open> @{term_ "[@{term \<open>True \<longrightarrow> True \<close>}]"}; (* with isa-check *)  \<close>

ML\<open> 
    (* Checking the default classes which should be in a neutral(unset) state. *)
    (* Note that in this state, the "implicit default" is "math_content". *) 
    @{assert} (Config.get_global @{theory} Definition_default_class = "");
    @{assert} (Config.get_global @{theory} Lemma_default_class = "");
    @{assert} (Config.get_global @{theory} Theorem_default_class = "");
    @{assert} (Config.get_global @{theory} Proposition_default_class = "");
    @{assert} (Config.get_global @{theory} Premise_default_class = "");
    @{assert} (Config.get_global @{theory} Corollary_default_class = "");
    @{assert} (Config.get_global @{theory} Consequence_default_class = "");
    @{assert} (Config.get_global @{theory} Assumption_default_class = "");
    @{assert} (Config.get_global @{theory} Hypothesis_default_class = "");
    @{assert} (Config.get_global @{theory} Consequence_default_class = "");
    @{assert} (Config.get_global @{theory} Assertion_default_class = "");
    @{assert} (Config.get_global @{theory} Proof_default_class = "");
    @{assert} (Config.get_global @{theory} Example_default_class = "");
\<close>


Definition*[e1]\<open>Lorem ipsum dolor sit amet, ... \<close>
text\<open>Note that this should yield a warning since \<^theory_text>\<open>Definition*\<close>  uses as "implicit default" the class
    \<^doc_class>\<open>math_content\<close> which has no \<^term>\<open>text_element.level\<close> set, however in this context,
    it is required to be a positive number since it is \<^term>\<open>text_element.referentiable\<close> . 
    This is intended behaviour in order to give the user a nudge to be more specific.\<close> 

text\<open>A repair looks like this:\<close>
declare [[Definition_default_class = "definition"]]

text\<open>Now, define a forward reference to the formal content: \<close>

declare_reference*[e1bisbis::"definition"]

text\<open>... which makes it possible to refer in a freeform definition to its formal counterpart
which will appear textually later. With this pragmatics, an "out-of-    order-presentation" 
can be achieved within \<^theory>\<open>Isabelle_DOF.scholarly_paper\<close> for the most common cases.\<close>



Definition*[e1bis::"definition", short_name="\<open>Nice lemma.\<close>"]
   \<open>Lorem ipsum dolor sit amet, ... 
    This is formally defined as follows in @{definition (unchecked) "e1bisbis"}\<close>
definition*[e1bisbis, status=formal] e :: int where "e = 2"

section\<open>Tests for Theorems, Assertions, Assumptions, Hypothesis, etc.\<close>

declare [[Theorem_default_class     = "theorem",
          Premise_default_class     = "premise",
          Hypothesis_default_class  = "hypothesis",
          Assumption_default_class  = "assumption",
          Conclusion_default_class  = "conclusion",
          Consequence_default_class = "consequence",
          Assertion_default_class   = "assertion",
          Corollary_default_class   = "corollary",
          Proof_default_class       = "math_proof",
          Conclusion_default_class  = "conclusion_stmt"]]

Theorem*[e2]\<open>... suspendisse non arcu malesuada mollis, nibh morbi, ... \<close>

theorem*[e2bis::"theorem", status=formal] f : "e = 1+1" unfolding e_def by simp

(*<*) (* @{theorem "e2bis"} breaks LaTeX generation ... *)
Lemma*[e3,level="Some 2"]
\<open>... phasellus amet id massa nunc, pede suscipit repellendus, ... @{theorem "e2bis"} \<close>
(*>*) 
Proof*[d10, short_name="\<open>Induction over Tinea pedis.\<close>"]\<open>Freeform Proof\<close>

lemma*[dfgd::"lemma"] q: "All (\<lambda>x. X \<and> Y \<longrightarrow> True)" oops
text-assert-error\<open>@{lemma dfgd} \<close>\<open>Undefined instance:\<close> \<comment> \<open>oops‘ed objects are not referentiable.\<close>

text\<open>... in ut tortor eleifend augue pretium consectetuer...  
     Lectus accumsan velit ultrices, ...\<close>

Proposition*[d2::"proposition"]\<open>"Freeform Proposition"\<close> 

Assumption*[d3] \<open>"Freeform Assertion"\<close>

Premise*[d4]\<open>"Freeform Premise"\<close> 

Corollary*[d5]\<open>"Freeform Corollary"\<close> 

Consequence*[d6::scholarly_paper.consequence]\<open>"Freeform Consequence"\<close> \<comment> \<open>longname just for test\<close>

declare_reference*[ababa::scholarly_paper.assertion]
Assertion*[d7]\<open>Freeform Assumption with forward reference to the formal  
               @{assertion (unchecked) ababa}.\<close>  
assert*[ababa::assertion] "3 < (4::int)"
assert*[ababab::assertion] "0 < (4::int)"


Conclusion*[d8]\<open>"Freeform Conclusion"\<close>

Hypothesis*[d9]\<open>"Freeform Hypothesis"\<close> 

Example*[d11::math_example]\<open>"Freeform Example"\<close> 

text\<open>An example for the ontology specification character of the short-cuts such as 
@{command  "assert*"}: in the following, we use the same notation referring to a completely
different class. "F" and "assertion" have only in common that they posses the attribute
@{const [names_short] \<open>properties\<close>}: \<close>

section\<open>Exhaustive Scholarly\_paper Test\<close>

subsection\<open>Global Structural Elements\<close>
(* maybe it is neither necessary nor possible to test these here... title is unique in
   a document, for example. To be commented out of needed. *)
text*[tt1::scholarly_paper.title]\<open>Lectus accumsan velit ultrices, ...\<close> 
text*[tt2::scholarly_paper.author]\<open>Lectus accumsan velit ultrices, ...\<close>  
text*[tt3::scholarly_paper.article]\<open>Lectus accumsan velit ultrices, ...\<close> 
text*[tt4::scholarly_paper.annex]\<open>Lectus accumsan velit ultrices, ...\<close>  
text*[tt5::scholarly_paper.abstract]\<open>Lectus accumsan velit ultrices, ...\<close>  
text*[tt6::scholarly_paper.subtitle]\<open>Lectus accumsan velit ultrices, ...\<close> 
text*[tt7::scholarly_paper.bibliography]\<open>Lectus accumsan velit ultrices, ...\<close>        
text*[tt8::scholarly_paper.introduction]\<open>Lectus accumsan velit ultrices, ...\<close> 
text*[tt9::scholarly_paper.related_work]\<open>Lectus accumsan velit ultrices, ...\<close>        
text*[tt11::scholarly_paper.text_section]\<open>Lectus accumsan velit ultrices, ...\<close>        
text*[tt12::scholarly_paper.background ]\<open>Lectus accumsan velit ultrices, ...\<close>
text*[tt13::scholarly_paper.conclusion ]\<open>Lectus accumsan velit ultrices, ...\<close>

subsection\<open>Technical Content Specific Elements\<close>

text*[tu1::scholarly_paper.axiom    ]\<open>Lectus accumsan velit ultrices, ...\<close>
text*[tu1bis::scholarly_paper.math_content, mcc="axm"   ]\<open>Lectus accumsan velit ultrices, ...\<close>
text*[tu2::scholarly_paper.lemma    ]\<open>Lectus accumsan velit ultrices, ...\<close>
text*[tu3::scholarly_paper.example  ]\<open>Lectus accumsan velit ultrices, ...\<close>
text*[tu4::scholarly_paper.premise  ]\<open>Lectus accumsan velit ultrices, ...\<close>
text*[tu5::scholarly_paper.theorem  ]\<open>Lectus accumsan velit ultrices, ...\<close>
text*[tu6::scholarly_paper.assertion]\<open>Lectus accumsan velit ultrices, ...\<close>
text*[tu7::scholarly_paper.corollary]\<open>Lectus accumsan velit ultrices, ...\<close>
text*[tu9::scholarly_paper.technical]\<open>Lectus accumsan velit ultrices, ...\<close>
text*[tu10::scholarly_paper.assumption ]\<open>Lectus accumsan velit ultrices, ...\<close>
text*[tu13::scholarly_paper.definition ]\<open>Lectus accumsan velit ultrices, ...\<close>
text*[tu15::scholarly_paper.experiment ]\<open>Lectus accumsan velit ultrices, ...\<close>
text*[tu16::scholarly_paper.hypothesis ]\<open>Lectus accumsan velit ultrices, ...\<close>
text*[tu17::scholarly_paper.math_proof ]\<open>Lectus accumsan velit ultrices, ...\<close>
text*[tu18::scholarly_paper.consequence]\<open>Lectus accumsan velit ultrices, ...\<close>
text*[tu19::scholarly_paper.math_formal]\<open>Lectus accumsan velit ultrices, ...\<close>
text*[tu20::scholarly_paper.proposition]\<open>Lectus accumsan velit ultrices, ...\<close>
text*[tu21::scholarly_paper.math_content    ]\<open>Lectus accumsan velit ultrices, ...\<close>
text*[tu22::scholarly_paper.math_example    ]\<open>Lectus accumsan velit ultrices, ...\<close>
text*[tu23::scholarly_paper.conclusion_stmt ]\<open>Lectus accumsan velit ultrices, ...\<close>
text*[tu24::scholarly_paper.math_motivation ]\<open>Lectus accumsan velit ultrices, ...\<close>
text*[tu25::scholarly_paper.tech_definition ]\<open>Lectus accumsan velit ultrices, ...\<close>
text*[tu28::scholarly_paper.eng_example     ]\<open>Lectus accumsan velit ultrices, ...\<close>
text*[tt10::scholarly_paper.tech_example]\<open>Lectus accumsan velit ultrices, ...\<close>        
text*[tu8::scholarly_paper.tech_code]        \<open>Lectus accumsan velit ultrices, ...\<close>
text*[tu27::scholarly_paper.engineering_content]\<open>Lectus accumsan velit ultrices, ...\<close>
text*[tu14::scholarly_paper.evaluation ]\<open>Lectus accumsan velit ultrices, ...\<close>

text\<open> @{axiom tu1} @{lemma tu2} @{example tu3} @{premise tu4} @{theorem tu5} @{assertion tu6} 
      @{technical tu9} @{assumption             tu10 }  @{definition             tu13 }
      @{experiment      tu15 } @{hypothesis      tu16 } @{math_proof      tu17 }
      @{consequence     tu18 } @{math_formal     tu19 } @{proposition     tu20 }
      @{math_content    tu21 } @{math_example    tu22 } @{conclusion_stmt tu23 }
      @{math_motivation tu24 } @{tech_definition tu25 } @{eng_example     tu28 }
      @{tech_example    tt10 } @{tech_code       tu8 }  @{engineering_content tu27 }
      @{evaluation      tu14 }
    \<close>

subsection\<open>The Use in Macros\<close>

Lemma*[ttu2::scholarly_paper.lemma    ]\<open>Lectus accumsan velit ultrices, ...\<close>
Example*[ttu3::scholarly_paper.math_example  ]\<open>Lectus accumsan velit ultrices, ...\<close>
Premise*[ttu4::scholarly_paper.premise  ]\<open>Lectus accumsan velit ultrices, ...\<close>
Theorem*[ttu5::scholarly_paper.theorem  ]\<open>Lectus accumsan velit ultrices, ...\<close>
Assertion*[ttu6::scholarly_paper.assertion]\<open>Lectus accumsan velit ultrices, ...\<close>
Corollary*[ttu7::scholarly_paper.corollary]\<open>Lectus accumsan velit ultrices, ...\<close>
Assumption*[ttu10::scholarly_paper.assumption ]\<open>Lectus accumsan velit ultrices, ...\<close>
Definition*[ttu13::scholarly_paper.definition ]\<open>Lectus accumsan velit ultrices, ...\<close>
Hypothesis*[ttu16::scholarly_paper.hypothesis ]\<open>Lectus accumsan velit ultrices, ...\<close>
Proof*[ttu17::scholarly_paper.math_proof ]\<open>Lectus accumsan velit ultrices, ...\<close>
Consequence*[ttu18::scholarly_paper.consequence]\<open>Lectus accumsan velit ultrices, ...\<close>
Proposition*[ttu20::scholarly_paper.proposition]\<open>Lectus accumsan velit ultrices, ...\<close>
Conclusion*[ttu23::scholarly_paper.conclusion_stmt ]\<open>Lectus accumsan velit ultrices, ...\<close>
(* Definition*[ttu25::scholarly_paper.tech_definition ]\<open>Lectus accumsan velit ultrices, ...\<close> 
   interesting modeling bug.
*)
(*Example*[ttu28::scholarly_paper.eng_example     ]\<open>Lectus accumsan velit ultrices, ...\<close>
   interesting modeling bug.
*)  
text\<open> @{lemma ttu2} @{math_example ttu3} @{premise ttu4} @{theorem ttu5} @{assertion ttu6} 
      @{assumption ttu10 }  @{definition ttu13 }
      @{hypothesis      ttu16 } @{math_proof      ttu17 }
      @{consequence     ttu18 } @{proposition     ttu20 }
      @{math_content    tu21 }  @{conclusion_stmt ttu23 }
      @ \<open>{eng_example     ttu28 }\<close>
      @ \<open>{tech_example    tt10 }\<close>  
    \<close>

end
