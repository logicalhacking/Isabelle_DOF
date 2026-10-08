(*************************************************************************
 * Same as Invariant_Timeout, but without invariants_strict_checking: the
 * timeout of the invariant evaluation is only a WARNING and the session
 * builds successfully (the warning is printed for the text* command).
 *************************************************************************)

theory Invariant_Timeout_Warning
  imports "Isabelle_DOF.Isa_DOF" "Isabelle_DOF.technical_report"
begin

fun busy :: "nat \<Rightarrow> nat" where
  "busy 0 = 1"
| "busy (Suc n) = busy n + busy n"       \<comment> \<open>2^n calls: hopeless for n = 60\<close>

declare[[invariants_checking = true, invariants_strict_checking = false,
         invariants_timeout = 2]]
(* declare[[invariants_parallel = false]]  \<comment> \<open>synchronous: the error is raised at the command\<close> *)

doc_class slow_doc =
  n :: int <= "0"
  invariant slow :: "int (busy 60) > n \<sigma>"

text*[slow1::slow_doc, n="1"]\<open>its invariant cannot be evaluated within the time limit\<close>
text*[after1::slow_doc, n="1"]\<open>a later command, not blocked by the evaluation above\<close>

end
