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
  "Isabelle_DOF-Unit-Tests_document"
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

ML\<open> @{term "[@{term \<open>True \<longrightarrow> True \<close>}]"}; (* with isa-check *)  \<close>

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
which will appear textually later. With this pragmatics, an "out-of-order-presentation" 
can be achieved within \<^theory>\<open>Isabelle_DOF.scholarly_paper\<close> for the most common cases.\<close>

(*<*)  (*LATEX FAILS *)
Definition*[e1bis::"definition", short_name="\<open>Nice lemma.\<close>"]
   \<open>Lorem ipsum dolor sit amet, ... 
    This is formally defined as follows in @{definition (unchecked) "e1bisbis"}\<close>
(*>*)
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

theorem*[e2bis, status=formal] f : "e = 1+1" unfolding e_def by simp

Lemma*[e3,level="Some 2"]\<open>... phasellus amet id massa nunc, pede suscipit repellendus, ... \<close>
(*<*)(*LATEX FAILS *)
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
(*>*)

end
(*>*)
