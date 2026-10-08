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

chapter\<open>Evaluation of Values and Invariants in a Stable Theory\<close>

theory 
  Static_Evaluation
imports 
  "Isabelle_DOF-Ontologies.Conceptual"
  TestKit
begin

section\<open>Test Purpose.\<close>
text\<open>Values and invariants of instances are evaluated in an earlier theory of the same theory
file (option @{attribute invariants_static_eval}, default on), because the caches of the code
generator are lost whenever the theory is extended. The evaluation theory must be replaced by
the current one if a term uses constants (functions, classes with their invariants) that were
declared later, and the results must be the same as without the option.\<close>

declare[[invariants_checking = true, invariants_strict_checking = true,
         monitor_trace_check, invariants_timeout = 60]]

doc_class first =
  n :: int <= "1"
  invariant pos :: "n \<sigma> > 0"

text*[f1::first]\<open>the evaluation theory is fixed here\<close>
text*[f2::first, n="5"]\<open>same theory, new value\<close>

section\<open>Constants Declared Later\<close>

definition double :: "int \<Rightarrow> int" where "double k = 2 * k"

doc_class second = first +
  m :: int <= "double 3"                    \<comment> \<open>a default that needs the new constant\<close>
  invariant dbl :: "m \<sigma> = double 3"     \<comment> \<open>an invariant that needs it as well\<close>

text*[s1::second]\<open>the default value is computed with the new function\<close>
text*[s2::second, m="double 3", n="2"]\<open>the same, given explicitly\<close>

value*\<open>m @{second \<open>s1\<close>}\<close>

section\<open>The Option Switched Off\<close>

declare[[invariants_static_eval = false]]

text*[s3::second, n="7"]\<open>evaluation in the current theory: same result\<close>

declare[[invariants_static_eval = true]]

section\<open>A Violation is Still Detected\<close>

text-assert-error[bad1::first, n="0"]\<open>\<close>\<open>Invariant\<close>

end
