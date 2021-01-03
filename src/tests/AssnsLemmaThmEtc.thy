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

theory 
  AssnsLemmaThmEtc
imports 
  "Isabelle_DOF.Conceptual"  
  "Isabelle_DOF.math_paper"
  "Isabelle_DOF.scholarly_paper" (* for assert notation *)
begin

section\<open>Elementary Creation of Doc-items and Access of their Attibutes\<close>

text\<open>Current status:\<close>
print_doc_classes
print_doc_items



section\<open>Definitions, Lemmas, Theorems, Assertions\<close>


text*[aa::F, properties = "[@{term ''True''}]"]
\<open>Our definition of the HOL-Logic has the following properties:\<close>
assert*[aa::F] "True"

(* does not work in batch mode ... 
(* sample for accessing a property filled with previous assert's of "aa" *)
ML\<open> ISA_core.property_list_dest @{context} @{docitem_attribute property :: aa};\<close>



assert*[aa::F] " X \<and> Y \<longrightarrow> True" (*example with uni-code *)
ML\<open> ISA_core.property_list_dest @{context} @{docitem_attribute property :: aa};
    app writeln (tl (rev it));\<close>



assert*[aa::F] "\<forall>x::bool. X \<and> Y \<longrightarrow> True" (*problem with uni-code *)
*)
ML\<open>
Syntax.read_term_global @{theory} "[@{termrepr ''True @<longrightarrow> True''}]";
(* this only works  because the isa check is not activated in "term" !!! *)
@{term "[@{term '' True @<longrightarrow> True ''}]"}; (* with isa-check *) 
@{term "[@{termrepr '' True @<longrightarrow> True ''}]"}; (* without isa check *)
\<close>
(*
ML\<open>val [_,_,Const _ $ s,_] = (HOLogic.dest_list @{docitem_attribute property :: aa});
val t = HOLogic.dest_string s;
holstring_to_bstring @{context} t 
\<close>
*)
lemma "All (\<lambda>x. X \<and> Y \<longrightarrow> True)" oops


text\<open>An example for the ontology specification character of the short-cuts such as 
@{command  "assert*"}: in the following, we use the same notation referring to a completely
different class. "F" and "assertion" have only in common that they posses the attribute
\<^verbatim>\<open>property\<close>: \<close>

text\<open>Creation just like that: \<close>
assert*[aaa::assertion] "3 < (4::int)"
assert*[aaa::assertion] "0 < (4::int)"


end
(*>*)
