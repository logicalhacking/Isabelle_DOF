(*************************************************************************
 * Copyright (C) 
 *               2026      The University of Exeter 
 *               2026      The University of Paris-Saclay
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

chapter\<open>Structural Construction of the Value of Instances\<close>

theory 
  Structural_Object_Value
imports 
  "Isabelle_DOF-Ontologies.Conceptual"
  "Isabelle_DOF.scholarly_paper"
begin

section\<open>Test Purpose.\<close>
text\<open>The value of an instance is built structurally by rewriting with the record definitions
of its class and super-classes (option @{attribute object_value_fast}, default on); only attribute
values that are not constructor terms or literals are evaluated, one by one. With the option
@{attribute monitor_trace_check} the result is compared with the evaluation of the whole term
(by normalization by evaluation) for each instance, and an error is raised if they differ.
The attributes below cover literals of several types, computed values (which must still be
evaluated), several levels of inheritance, and updates of instances.\<close>

declare[[monitor_trace_check, invariants_checking = true, invariants_batch = true]]

datatype colour = Red | Green

doc_class c0 =
  v0 :: int <= "0"
  invariant nonneg :: "v0 \<sigma> \<ge> 0"

doc_class c1 = c0 +
  v1   :: int <= "3"
  s    :: string <= "''ab''"
  o    :: "int option"
  n    :: nat <= "3"
  L    :: "int list" <= "[1,2]"
  col  :: colour <= "Red"
  neg  :: int <= "-5"
  P    :: "int \<times> string" <= "(1,''x'')"
  st   :: "int set" <= "{1,2}"
  expr :: int <= "2+3"             \<comment> \<open>a computation: not a normal form\<close>
  invariant big :: "v1 \<sigma> > 0 \<and> n \<sigma> > 0"

doc_class c2 = c1 +
  w :: "int list" <= "[]"

section\<open>Literals and Defaults\<close>

text*[a1::c0]\<open>defaults only\<close>
text*[a2::c0, v0="4"]\<open>one attribute set\<close>
text*[b1::c1]\<open>defaults of two levels\<close>
text*[b2::c1, v0="7", o="Some 4", n="5"]\<open>literals of int, option and nat\<close>
text*[b4::c1, neg="-7", col="Green", P="(2,''yz'')", o="None"]\<open>negative, enumeration, pair\<close>

section\<open>Computed Attribute Values\<close>

text*[b3::c1, expr="10 * 2", st="{3} \<union> {4}", L="[1] @ [2,3]", s="''q''"]
  \<open>values that need evaluation (arithmetic, union, append)\<close>

section\<open>Three Levels of Inheritance and Updates\<close>

text*[d1::c2, w="[1,2]", v1="9"]\<open>attributes of all three levels\<close>
update_instance*[b2::c1, L += "[9]", v1 := "11"]

value*\<open>L @{c1 \<open>b2\<close>}\<close>
value*\<open>expr @{c1 \<open>b3\<close>}\<close>
value*\<open>w @{c2 \<open>d1\<close>}\<close>

section\<open>Access to Attributes, in Particular the Trace of a Monitor\<close>

text\<open>The access to the attribute of an instance (the value command with a star, antiquotations,
invariants written in ML) projects the field of the stored value structurally; with
@{attribute monitor_trace_check} the result is compared with the evaluation.\<close>

doc_class mon =
  tag_m :: int <= "0"
  accepts "\<lbrace>c0\<rbrace>\<^sup>*"

open_monitor*[m1::mon]
text*[mc1::c0]\<open>first item of the monitor\<close>
text*[mc2::c0, v0="2"]\<open>second item of the monitor\<close>
value*\<open>map snd @{trace_attribute \<open>m1\<close>}\<close>
close_monitor*[m1]

ML\<open>
val trace = AttributeAccess.compute_trace_ML (Context.Proof @{context}) "m1" NONE \<^here>;
val _ = if map snd trace = ["mc1", "mc2"] then () else error "wrong trace of the monitor m1"
\<close>

section\<open>An Ontology Class\<close>

text*[intro1::introduction, level="Some 1"]\<open>a class of the scholarly paper ontology\<close>

end
