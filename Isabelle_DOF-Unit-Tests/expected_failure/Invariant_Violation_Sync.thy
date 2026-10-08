(*************************************************************************
 * Same as Invariant_Violation, but with synchronous invariant checking
 * (invariants_parallel = false): the error is raised by the text* command
 * itself, so that the following commands are not evaluated.
 *
 * EXPECTED TO FAIL with:  Invariant Invariant_Violation_Sync.bad.pos_inv violated
 *************************************************************************)

theory Invariant_Violation_Sync
  imports "Isabelle_DOF.Isa_DOF" "Isabelle_DOF.technical_report"
begin

declare[[invariants_checking = true, invariants_strict_checking = true]]
declare[[invariants_parallel = false]]  \<comment> \<open>synchronous check: the error is raised at the command itself\<close>

doc_class bad =
  n :: int <= "0"
  invariant pos :: "n \<sigma> > 0"

text*[ok1::bad, n="1"]\<open>satisfies the invariant\<close>
text*[bad1::bad, n="0"]\<open>violates the invariant n > 0\<close>   \<comment> \<open>error expected here\<close>
text*[after1::bad, n="2"]\<open>a later command, evaluated in parallel with the failing check\<close>

end
