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
  Concept_MonitorTest2
  imports
  Concept_MonitorTest1
begin

section\<open>Test Purpose.\<close>
text\<open> Creation of document parts that are controlled by (nested, locally defined) monitors. \<close>

doc_class test_monitor_B =
  tmB :: int

doc_class monitor_M =
  tmM :: int
  rejects "Concept_MonitorTest1.test_monitor_B"
  accepts "test_monitor_E ~~ test_monitor_C"

doc_class test_monitor_head =
  tmhd :: int

declare[[free_class_in_monitor_checking]]

declare[[free_class_in_monitor_strict_checking]]
text-assert-error[test_monitor_head1::test_monitor_head]\<open>\<close>
                  \<open>accepts clause 1 of monitor Concept_MonitorTest1.test_monitor_M3 not enabled\<close>
declare[[free_class_in_monitor_strict_checking=false]]
text*[test_monitor_head2::Concept_MonitorTest1.test_monitor_head]\<open>\<close>

open_monitor*[test_monitor_M3::monitor_M]

text*[test_monitor_head3::Concept_MonitorTest1.test_monitor_head]\<open>\<close>
text*[testFree3::test_monitor_free]\<open>\<close>
declare[[strict_monitor_checking]]
text-assert-error[test_monitor_B1::test_monitor_B]\<open>\<close>
                  \<open>accepts clause 1 of monitor Concept_MonitorTest2.test_monitor_M3 rejected\<close>
declare[[strict_monitor_checking=false]]
text*[testFree4::test_monitor_free]\<open>\<close>
declare[[strict_monitor_checking]]
text-assert-error[test_monitor_D1::test_monitor_D]\<open>\<close>
                  \<open>accepts clause 1 of monitor Concept_MonitorTest2.test_monitor_M3 rejected\<close>
declare[[strict_monitor_checking=false]]
text*[testFree5::test_monitor_free]\<open>\<close>
text*[test_monitor_E1::test_monitor_E]\<open>\<close>
text*[test_monitor_C1::test_monitor_C]\<open>\<close>
text*[testFree6::test_monitor_free]\<open>\<close>

close_monitor*[Concept_MonitorTest1.test_monitor_M3]

close_monitor*[test_monitor_M3]

declare[[free_class_in_monitor_checking = false]]

end