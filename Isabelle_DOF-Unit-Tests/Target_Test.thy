(*************************************************************************
 * Copyright (C) 
 *               2026      The University of Paris-Saclay
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

chapter\<open>Regression Tests for Local Theory Targets of DOF Commands\<close>

theory 
  Target_Test
imports 
  "Isabelle_DOF-Ontologies.Conceptual"
  TestKit
begin

section\<open>Test Purpose.\<close>
text\<open>The commands \<open>text*\<close> and \<open>Theorem*\<close> accept a target \<open>(in L)\<close>: the body is checked in the
context of the locale \<open>L\<close> (its facts are visible unqualified), whereas the instance stays global.\<close>

locale L = fixes f :: "nat \<Rightarrow> nat" assumes ax: "f 0 = 0"
begin
lemma loc_fact: "f 0 + 0 = 0" using ax by simp
end

text*[tt1::A, x = "3"] \<open>No target: qualified fact @{thm L.loc_fact}.\<close>

text* (in L) [tt2::A, x = "4"] \<open>Target: unqualified fact @{thm loc_fact}.\<close>

text* (in L) [tt3::A, x = "5"] \<open>Qualified fact with instantiation @{thm (lhs) L.loc_fact[of f]}.\<close>

\<comment> \<open>The instances of targeted commands are global, not qualified with the locale name:\<close>
text*[tt4::A, x = "6"] \<open>@{A tt2} and @{A tt3}\<close>

section\<open>Attribute Names that are Keywords\<close>
text\<open>The name of an attribute may be a keyword of the outer syntax, as \<open>options\<close>.\<close>

doc_class kw_class =
  "options" :: string <= "''none''"

text*[tkw1::kw_class, options = "''allowframebreaks''"]\<open>An attribute named as a keyword.\<close>

end
