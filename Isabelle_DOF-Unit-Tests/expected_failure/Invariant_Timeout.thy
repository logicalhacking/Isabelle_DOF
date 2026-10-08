(*************************************************************************
 * Regression test for the option invariants_timeout.
 *
 * The invariant "slow" takes (practically) forever to evaluate. With
 * invariants_timeout = 2 (seconds) and invariants_strict_checking, the
 * evaluation is interrupted and the timeout is an ERROR:
 *    Evaluation of invariant Invariant_Timeout.slow_doc.slow_inv exceeded the timeout of 2.0 s
 *
 * The value of the instance is not lost: the later command "after1" can still
 * read it. (The session containing this theory is EXPECTED TO FAIL.)
 *************************************************************************)

theory Invariant_Timeout
  imports "Isabelle_DOF.Isa_DOF" "Isabelle_DOF.technical_report"
begin

fun busy :: "nat \<Rightarrow> nat" where
  "busy 0 = 1"
| "busy (Suc n) = busy n + busy n"       \<comment> \<open>2^n calls: hopeless for n = 60\<close>

declare[[invariants_checking = true, invariants_strict_checking = true,
         invariants_timeout = 2]]
(* declare[[invariants_parallel = false]]  \<comment> \<open>synchronous: the error is raised at the command\<close> *)

doc_class slow_doc =
  n :: int <= "0"
  invariant slow :: "int (busy 60) > n \<sigma>"

text*[slow1::slow_doc, n="1"]\<open>its invariant cannot be evaluated within the time limit\<close>
text*[after1::slow_doc, n="1"]\<open>a later command, not blocked by the evaluation above\<close>

end
