(*************************************************************************
 * Copyright (C) 
 *               2019-2023 The University of Exeter 
 *               2018-2023 The University of Paris-Saclay
 *               2018      The University of Sheffield
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

chapter\<open>High-level Class Invariants\<close>

theory Concept_High_Level_Invariants
  imports "Isabelle_DOF.Isa_DOF"
          "Isabelle_DOF_Unit_Tests_document"
          TestKit
begin

section\<open>Test Purpose.\<close>
text\<open>
  Without invariants, ontological classes as such are too liberal in many situations.
  Similarly to UML constraints, invariants or hand-programmed checking functions
  can be added in ODL ontologies in order to constrain class instances or
  (via monitor traces) impose structural constraints over an entire document.

  While hand-programmed checking functions were tested in test-case 
  \<^verbatim>\<open>Concept_Example_Low_Level_Invariant\<close>, in this text case, we test 
  high-level invariants, i.e. data-constraints speicified as executable 
  HOL-predicates in the @{theory_text \<open>invariant\<close>} clause of ODL definitions.

  To enable the checking of the invariants, the \<open>invariants_checking\<close>
  theory attribute must be set:\<close>


section\<open>The Scenario.\<close>

text\<open> This is merely an example that shows that the generated invariants
      fit nicely together; i.e. allow for sensible consistency and invariant
      preservation proofs related to ontological matchings. \<close>


text\<open>Using HOL, we can define a mapping between two ontologies.
  It is called ontology matching or ontology alignment.
  Here is an example which show how to map two classes.
  HOL also allows us to map the invariants (ontological rules) of the classes!\<close>

text\<open>
  Ontological classes as described so far are too liberal in many situations.
  There is a first high-level syntax implementation for class invariants.
  These invariants can be checked when an instance of the class is defined.
  To enable the checking of the invariants, the \<open>invariants_checking\<close>
  theory attribute must be set:\<close>


declare[[invariants_strict_checking = true]]

text\<open>For example, let's define the following two classes:\<close>

doc_class class_inv1 =
  int1 :: "int"
  invariant inv1 :: "int1 \<sigma> \<ge> 3"

doc_class class_inv2 = class_inv1 +
  int2 :: "int"
  invariant inv2 :: "int2 \<sigma> < 2"

text\<open>The  symbol \<^term>\<open>\<sigma>\<close> is reserved and references the future instance class.
  By relying on the implementation of the Records
  in Isabelle/HOL~@{cite "wenzel:isabelle-isar:2020"},
  one can reference an attribute of an instance using its selector function.
  For example, \<^term>\<open>int1 \<sigma>\<close> denotes the value
  of the \<^term>\<open>int1\<close> attribute
  of the future instance of the class @{doc_class class_inv1}.
  Now let's define two instances, one of each class:\<close>

text*[testinv1::class_inv1, int1=4]\<open>lorem ipsum...\<close>
update_instance*[testinv1::class_inv1, int1:="3"]
(* When not commented, should violated the invariant:
update_instance*[testinv1::class_inv1, int1:=1]
*)

text*[testinv2::class_inv2, int1=3, int2=1]\<open>lorem ipsum...\<close>

text\<open>
  The value of each attribute defined for the instances is checked against their classes invariants.
  As the class @{doc_class class_inv2} is a subsclass of the class @{doc_class class_inv1},
  it inherits @{doc_class class_inv1} invariants.
  Hence the \<^term>\<open>int1\<close> invariant is checked when the instance @{docitem testinv2} is defined.\<close>

text\<open>Test invariant for attributes of attributes: \<close>

doc_class inv_test1 =
  a :: int

doc_class inv_test2 =
  b :: "inv_test1"
  c:: int
  invariant inv_test2 :: "c \<sigma> = 1"
  invariant inv_test2' :: "a (b \<sigma>) = 2"

doc_class inv_test3 = inv_test1 +
  b :: "inv_test1"
  c:: int
  invariant inv_test3 :: "a \<sigma> = 2"
  invariant inv_test3' :: "a (b \<sigma>) = 2"

doc_class inv_test4 = inv_test2 +
  d :: "inv_test3"
  invariant inv_test4 :: "a (inv_test2.b \<sigma>) = 2"
  invariant inv_test4' :: "a (d \<sigma>) = 2"

text*[inv_test1_instance::inv_test1, a=2]\<open>\<close>
text*[inv_test3_instance::inv_test3, a=2, b="@{inv-test1 \<open>inv_test1_instance\<close>}" ]\<open>\<close>
text*[inv_test4_instance::inv_test4, b="@{inv-test1 \<open>inv_test1_instance\<close>}"
                                   , c=1, d="@{inv-test3 \<open>inv_test3_instance\<close>}"]\<open>\<close>

text\<open>To support invariant on attributes in attributes
and invariant on attributes of the superclasses,
we check that the type of the attribute of the subclass is ground:\<close>
ML\<open>
val Type(st, [ty]) = \<^typ>\<open>inv_test1\<close>
val Type(st', [ty']) = \<^typ>\<open>'a inv_test1_scheme\<close>
val t = ty = \<^typ>\<open>unit\<close>
\<close>

text\<open>Now assume the following ontology:\<close>

doc_class title =
  short_title :: "string option" <= "None"

doc_class author =
  email :: "string" <= "''''"

datatype classification = SIL0 | SIL1 | SIL2 | SIL3 | SIL4

doc_class abstract =
  keywordlist :: "string list" <= "[]"
  safety_level :: "classification" <= "SIL3"

doc_class text_section =
  authored_by :: "author set" <= "{}"
  level :: "int option" <= "None"

type_synonym notion = string

doc_class introduction = text_section +
  authored_by :: "author set"  <= "UNIV" 
  uses :: "notion set"
  invariant author_finite :: "finite (authored_by \<sigma>)"
  and force_level :: "(level \<sigma>) \<noteq> None \<and> the (level \<sigma>) > 1"

doc_class claim = introduction +
  based_on :: "notion list"

doc_class technical = text_section +
  formal_results :: "thm list" 

doc_class "definition" = technical +
  is_formal :: "bool"
  property  :: "term list" <= "[]" 

datatype kind = expert_opinion | argument | "proof"

doc_class result = technical +
  evidence :: kind
  property :: "thm list" <= "[]"
  invariant has_property :: "evidence \<sigma> = proof \<longleftrightarrow> property \<sigma> \<noteq> []"

doc_class example = technical +
  referring_to :: "(notion + definition) set" <= "{}"

doc_class conclusion = text_section +
  establish :: "(claim \<times> result) set"
  invariant establish_defined :: "\<forall> x. x \<in> Domain (establish \<sigma>)
                                           \<longrightarrow> (\<exists> y \<in> Range (establish \<sigma>). (x, y) \<in> establish \<sigma>)"

text\<open>Next we define some instances (docitems): \<close>

declare[[invariants_checking_with_tactics = true]]

text*[church::author, email="\<open>church@lambda.org\<close>"]\<open>\<close>

text\<open>We can also reference instances of classes defined in parent theories:\<close>
text*[church'::scholarly_paper.author, email="\<open>church'@lambda.org\<close>"]\<open>\<close>

text*[resultProof::result, evidence = "proof", property="[@{thm \<open>HOL.refl\<close>}]"]\<open>\<close>
text*[resultArgument::result, evidence = "argument"]\<open>\<close>

text\<open>The invariants \<^theory_text>\<open>author_finite\<close> and \<^theory_text>\<open>establish_defined\<close> can not be checked directly
  and need a little help.
  We can set the \<open>invariants_checking_with_tactics\<close> theory attribute to help the checking.
  It will enable a basic tactic, using unfold and auto:\<close>

declare[[invariants_checking_with_tactics = true]]

text*[curry::author, email="\<open>curry@lambda.org\<close>"]\<open>\<close>

text*[introduction2::introduction, authored_by = "{@{author \<open>church\<close>}}", level = "Some 2"]\<open>\<close>
(* When not commented, should violated the invariant:
update_instance*[introduction2::Introduction
                  , authored_by := "{@{Author \<open>church\<close>}}"
                  , level := "Some 1"]
*)
text\<open>Use of the instance @{docitem_name "church'"}
     to instantiate a \<^doc_class>\<open>scholarly_paper.introduction\<close> class:\<close>
text*[introduction2'::scholarly_paper.introduction,
      main_author = "Some @{scholarly-paper.author \<open>church'\<close>}", level = "Some 2"]\<open>\<close>

value*\<open>@{scholarly-paper.author \<open>church'\<close>}\<close>
value*\<open>@{author \<open>church\<close>}\<close>
value*\<open>@{Concept-High-Level-Invariants.author \<open>church\<close>}\<close>

value*\<open>@{scholarly-paper.author-instances}\<close>
value*\<open>@{author-instances}\<close>
value*\<open>@{Concept-High-Level-Invariants.author-instances}\<close>

text*[introduction3::introduction, authored_by = "{@{author \<open>church\<close>}}", level = "Some 2"]\<open>\<close>
text*[introduction4::introduction, authored_by = "{@{author \<open>curry\<close>}}", level = "Some 4"]\<open>\<close>

text*[resultProof2::result, evidence = "proof", property="[@{thm \<open>HOL.sym\<close>}]"]\<open>\<close>

text\<open>Then we can evaluate expressions with instances:\<close>

term*\<open>authored_by @{introduction \<open>introduction2\<close>} = authored_by @{introduction \<open>introduction3\<close>}\<close>
value*\<open>authored_by @{introduction \<open>introduction2\<close>} = authored_by @{introduction \<open>introduction3\<close>}\<close>
value*\<open>authored_by @{introduction \<open>introduction2\<close>} = authored_by @{introduction \<open>introduction4\<close>}\<close>

value*\<open>@{introduction \<open>introduction2\<close>}\<close>

value*\<open>{@{author \<open>curry\<close>}} = {@{author \<open>church\<close>}}\<close>

term*\<open>property @{result \<open>resultProof\<close>} = property @{result \<open>resultProof2\<close>}\<close>
value*\<open>property @{result \<open>resultProof\<close>} = property @{result \<open>resultProof2\<close>}\<close>

value*\<open>evidence @{result \<open>resultProof\<close>} = evidence @{result \<open>resultProof2\<close>}\<close>

declare[[invariants_checking_with_tactics = false]]

declare[[invariants_strict_checking = false]]

end
