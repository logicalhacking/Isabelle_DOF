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
  "Isabelle_DOF-Ontologies.Conceptual"  
  "Isabelle_DOF.scholarly_paper"
  "Isabelle_DOF-Unit-Tests_document"
begin

section\<open>Elementary Creation of Doc-items and Access of their Attibutes\<close>

text\<open>Current status:\<close>
print_doc_classes
print_doc_items



section\<open>Definitions, Lemmas, Theorems, Assertions\<close>

term\<open>True\<close>
text*[aa::F, properties = "[@{term ''True''}]"]
\<open>Our definition of the HOL-Logic has the following properties:\<close>
assert*\<open>F.properties @{F \<open>aa\<close>} = [@{term ''True''}]\<close>

text\<open>For now, as the term annotation is not bound to a meta logic which will translate
\<^term>\<open>[@{term ''True''}]\<close> to \<^term>\<open>[True]\<close>, we can not use the HOL \<^const>\<open>True\<close> constant
in the assertion.
\<close>

ML\<open>
@{term "[@{term \<open>True \<longrightarrow> True \<close>}]"}; (* with isa-check *) 
\<close>

Definition*[ertert]\<open>dfgdfg\<close>
Theorem*[dgdfgddfg]\<open>dfgdfg\<close>

lemma "All (\<lambda>x. X \<and> Y \<longrightarrow> True)" oops


text\<open>An example for the ontology specification character of the short-cuts such as 
@{command  "assert*"}: in the following, we use the same notation referring to a completely
different class. "F" and "assertion" have only in common that they posses the attribute
@{const [names_short] \<open>properties\<close>}: \<close>

text\<open>Creation just like that: \<close>
assert*[ababa::assertion] "3 < (4::int)"
assert*[ababab::assertion] "0 < (4::int)"


end
(*>*)
