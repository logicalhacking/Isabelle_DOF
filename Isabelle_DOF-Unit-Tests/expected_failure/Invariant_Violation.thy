(*************************************************************************
 * Regression test: a violated high-level invariant must be reported as an
 * error at the text* command that creates the offending instance, also when
 * the invariants are checked in parallel (invariants_parallel, the default).
 *
 * This session is EXPECTED TO FAIL: building it must end with the message
 *    Invariant Invariant_Violation.bad.pos_inv violated
 * If it builds without error, the error report of the forked check is lost.
 *
 * Run (from Isabelle_DOF/upstream_afp):
 *   isabelle build -d . -d ../Isabelle_DOF-Unit-Tests/expected_failure \
 *                  Isabelle_DOF-Unit-Tests-Expected_Failure
 *************************************************************************)

theory Invariant_Violation
  imports "Isabelle_DOF.Isa_DOF" "Isabelle_DOF.technical_report"
begin

declare[[invariants_checking = true, invariants_strict_checking = true]]
(* declare[[invariants_parallel = false]]   \<comment> \<open>synchronous check: error at the command itself\<close> *)

doc_class bad =
  n :: int <= "0"
  invariant pos :: "n \<sigma> > 0"

text*[ok1::bad, n="1"]\<open>satisfies the invariant\<close>
text*[bad1::bad, n="0"]\<open>violates the invariant n > 0\<close>   \<comment> \<open>error expected here\<close>
text*[after1::bad, n="2"]\<open>a later command, evaluated in parallel with the failing check\<close>

end
