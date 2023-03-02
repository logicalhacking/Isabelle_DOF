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

chapter\<open>Testing Nested Monitors\<close>

theory 
  Concept_MonitorTest1
  imports 
  "Isabelle_DOF-Unit-Tests_document"
  "Isabelle_DOF-Ontologies.Conceptual" (* we use the generic "Conceptual" ontology *)
  TestKit
begin


open_monitor*[aaa::Conceptual.M]  
text*[test::A]\<open>For Test and Validation\<close>

text\<open>Defining some document elements to be referenced in later on in another theory: \<close>
text*[sdf]         \<open> Lorem ipsum ... \<close>         \<comment> \<open>anonymous reference, ignored by monitor.\<close>
text*[sdfg :: F]   \<open> Lorem ipsum ...\<close>          \<comment> \<open>causes just warnings for invariant violations  
                                                   due to non-strict checking mode\<close>
close_monitor*[aaa]                            \<comment> \<open>causes warning: accept clause 1 
                                                   not in final state .\<close>

section\<open>A Local Monitor Class Definition\<close>

doc_class test_monitor_free =
  tmhd :: int
doc_class test_monitor_head =
  tmhd :: int
doc_class test_monitor_A = test_monitor_head +
  tmA :: int
doc_class test_monitor_B = test_monitor_A +
  tmB :: int
doc_class test_monitor_C = test_monitor_A +
  tmC :: int
doc_class test_monitor_D = test_monitor_B +
  tmD :: int
doc_class test_monitor_E = test_monitor_D +
  tmE :: int

doc_class monitor_M =
  tmM :: int
  rejects "test_monitor_A"
  accepts "test_monitor_head ~~ test_monitor_B ~~ test_monitor_C"

section\<open>Example: Standard Class Invariant\<close>

text\<open>Consult the status of the DOF engine:\<close>
print_doc_classes
print_doc_items



declare[[free_class_in_monitor_checking]]

open_monitor*[test_monitor_M::monitor_M]

text*[testFree::test_monitor_free]\<open>...\<close>

open_monitor*[test_monitor_M2::monitor_M]

declare[[strict_monitor_checking]]
text-assert-error[test_monitor_A1::test_monitor_A]\<open>\<close> 
                  \<open>accepts clause 1 of monitor Concept_MonitorTest1.test_monitor_M rejected\<close>
declare[[strict_monitor_checking=false]]
text*[test_monitor_A1::test_monitor_A]\<open>\<close> \<comment> \<open>the same in non-strict monitor checking.\<close>

text*[testFree2::test_monitor_free]\<open>\<close>
text*[test_monitor_head1::test_monitor_head]\<open>\<close>
text*[testFree3::test_monitor_free]\<open>\<close>
text*[test_monitor_B1::test_monitor_B]\<open>\<close>
text*[testFree4::test_monitor_free]\<open>\<close>
text*[test_monitor_D1::test_monitor_D]\<open>\<close>
text*[testFree5::test_monitor_free]\<open>\<close>
text*[test_monitor_C1::test_monitor_C]\<open>\<close>
text*[testFree6::test_monitor_free]\<open>\<close>

close_monitor*[test_monitor_M2]

close_monitor*[test_monitor_M]

declare[[free_class_in_monitor_checking = false]]

text\<open>Consult the final status of the DOF engine:\<close>
print_doc_classes
print_doc_items

ML\<open>
val (oid, DOF_core.Instance {value, ...}) =
    Name_Space.check (Context.Proof \<^context>) (DOF_core.get_instances \<^context>) ("aaa", Position.none)
\<close>
term*\<open>map fst @{trace-attribute \<open>test_monitor_M\<close>}\<close>
value*\<open>map fst @{trace-attribute \<open>test_monitor_M\<close>}\<close>

ML\<open>@{assert} ([("Conceptual.A", "test"), ("Conceptual.F", "sdfg")] =  @{trace_attribute aaa})       \<close>

end 
  
