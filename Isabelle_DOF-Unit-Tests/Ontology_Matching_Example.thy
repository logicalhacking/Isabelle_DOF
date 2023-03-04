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

chapter\<open>Ontologys Matching\<close>

theory Ontology_Matching_Example
  imports TestKit
          "Isabelle_DOF.Isa_DOF"
          "Isabelle_DOF-Unit-Tests_document"

begin

section\<open>Test Purpose.\<close>
text\<open> This is merely an example that shows that the generated invariants 
      fit nicely together; i.e. allow for sensible consistency and invariant
      preservation proofs related to ontological matchings. \<close>

section\<open>The Scenario.\<close>

text\<open>Using HOL, we can define a mapping between two ontologies.
  It is called ontology matching or ontology alignment.
  Here is an example which show how to map two classes.
  HOL also allows us to map the invariants (ontological rules) of the classes!\<close>

type_synonym UTF8 = string

definition utf8_to_string
  where "utf8_to_string xx = xx"


doc_class A =
  first_name  :: UTF8
  last_name   :: UTF8
  age         :: nat
  married_to  :: "string option"
  invariant a :: "age \<sigma> < 18 \<longrightarrow> married_to \<sigma> = None"


doc_class B =
  name        :: string 
  adult       :: bool
  is_married  :: bool
  invariant b :: "is_married \<sigma> \<longrightarrow> adult \<sigma>"

text\<open>We define the mapping between the two classes,
  i.e. how to transform the class @{doc_class A} in to the class @{doc_class B}:\<close>

definition A_to_B_morphism
  where "A_to_B_morphism X =
        \<lparr> tag_attribute = A.tag_attribute X
          , name = utf8_to_string (first_name X) @ '' ''  @ utf8_to_string (last_name X)
          , adult = (age X \<ge> 18)
          , is_married = (married_to X \<noteq> None) \<rparr>" 

text\<open>Sanity check: Invariants are non-contradictory, i.e. there is a witness.\<close>

lemma inv_a_satisfyable : " Ex (a_inv::A \<Rightarrow> bool)"
  unfolding a_inv_def
  apply(rule_tac x ="\<lparr>Ontology_Matching_Example.A.tag_attribute = xxx, 
                      first_name = yyy, last_name = zzz, age = 17, 
                      married_to = None\<rparr>" in exI)
  by auto

text\<open>Now we check that the invariant is preserved through the morphism:\<close>

lemma inv_a_preserved :
  "a_inv X \<Longrightarrow> b_inv (A_to_B_morphism X)"
  unfolding a_inv_def b_inv_def A_to_B_morphism_def
  by auto

text\<open>This also implies that B invariants are non-contradictory: \<close>

lemma inv_b_preserved : "\<exists>x. (b_inv::B \<Rightarrow> bool) x"
   apply(rule_tac x ="A_to_B_morphism \<lparr>Ontology_Matching_Example.A.tag_attribute = xxx, 
                                       first_name = yyy, last_name = zzz, age = 17, 
                                        married_to = None\<rparr>" in exI)
   by(rule inv_a_preserved,auto simp: a_inv_def)


lemma A_morphism_B_total :
  "A_to_B_morphism ` ({X::A. a_inv X}) \<subseteq> ({X::B. b_inv X})"
  using inv_a_preserved
  by auto

end
