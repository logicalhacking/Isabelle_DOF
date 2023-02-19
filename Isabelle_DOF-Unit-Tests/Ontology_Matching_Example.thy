chapter\<open>Ontologys Mathing\<close>

theory Ontology_Matching_Example
  imports "Isabelle_DOF.Isa_DOF"
begin

text\<open>Using HOL, we can define a mapping between two ontologies.
  It is called ontology matching or ontology alignment.
  Here is an example which show how to map two classes.
  HOL also allows us to map the invariants (ontological rules) of the classes!\<close>

type_synonym UTF8 = string

definition utf8_to_string
  where "utf8_to_string x = x"


doc_class A =
  first_name :: UTF8
  last_name :: UTF8
  age :: nat
  married_to :: "string option"
  invariant a :: "age \<sigma> < 18 \<longrightarrow> married_to \<sigma> = None"
doc_class B =
  name :: string 
  adult :: bool
  is_married :: bool
  invariant b :: "is_married \<sigma> \<longrightarrow> adult \<sigma>"

text\<open>We define the mapping between the two classes,
  i.e. how to transform the class @{doc_class A} in to the class @{doc_class B}:\<close>

definition A_to_B_morphism
  where "A_to_B_morphism X =
        \<lparr> tag_attribute = A.tag_attribute X
          , name = utf8_to_string (first_name X) @ '' ''  @ utf8_to_string (last_name X)
          , adult = (age X \<ge> 18)
          , is_married = (married_to X \<noteq> None) \<rparr>" 

text\<open>Now we check that the invariant is preserved through the morphism:\<close>

lemma inv_a_preserved :
  "a_inv X \<Longrightarrow> b_inv (A_to_B_morphism X)"
  unfolding a_inv_def b_inv_def A_to_B_morphism_def
  by auto

lemma A_morphism_B_total :
  "A_to_B_morphism ` ({X::A. a_inv X}) \<subseteq> ({X::B. b_inv X})"
  using inv_a_preserved
  by auto

end