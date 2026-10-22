(*<*)
theory "big_steps"
  imports   "Isabelle_DOF.scholarly_paper"
            (* "Isabelle_DOF-Ontologies.document_templates" *)
            "HOL-CSP_OpSem.Conclusion"
          (*  "HOL-CSP_OpSem.Determinism"
            "HOL-CSP_OpSem.AfterDeadlockResults" *)
            "annex"
begin

(*>*)


section*["bigSteps"::technical,main_author="Some(@{author ''ben''}::author)", level= "Some 3"]
\<open>Big Steps Semantics\<close>
(*<*) context OpSemTransitions begin (*>*)
text\<open>\<^noindent> The notation \<open>P / [e]\<close> sometimes appearing in the classical literature will now
be given a formal definition in terms of the  @{const [source] After\<^sub>t\<^sub>i\<^sub>c\<^sub>k} (@{definition After_tick_def})
operator. From there, the generalization to an operator ``connecting'' two processes \<open>P\<close> and \<open>Q\<close>
via a trace \<open>s\<close>
--- analogously to the notion of \<open>\<delta>\<close> function in automata theory  ---  is straightforward.
In the same manner, we can combine small steps transitions to a trace transition.
These generalized notions will allow for both establishing new
formats of refinement proofs as well as (bi)simulation theorems.
\<close>

(*<*) end  (*>*)

subsection*["extensions_traces"::technical,main_author="Some(@{author ''ben''}::author)"]
\<open>Extensions to Traces\<close>

text \<open>\<^noindent> The definition of the generalized \<open>After\<close> operator proceeds inductively:\<close>

Definition*[After_trace_def::"definition", short_name=\<open>\<open>$After_{trace}$ operator\<close>\<close>]
\<open>@{theory_text [display, indent = 5]\<open>
fun After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e :: \<open>['\<alpha> process, '\<alpha> trace] \<Rightarrow> '\<alpha> process\<close> (infixl \<open>after\<^sub>\<T>\<close> 77)
  where \<open>P after\<^sub>\<T> [] = P\<close>
  |       \<open>P after\<^sub>\<T> (e # s) = (P after\<^sub>\<checkmark> e) after\<^sub>\<T> s\<close>\<close>}\<close>

(*<*) context OpSemTransitions begin (*>*)


text\<open>\<^noindent> The definition of the generalized trace-transition is done analogously:\<close>

(*<*)end (*>*)

Definition*[trace_trans_def::"definition", short_name = \<open>\<open>Transition with a trace\<close>\<close>]
\<open>@{theory_text [display, indent = 5]\<open>
inductive trace_trans :: \<open>['\<alpha> process, '\<alpha> trace, '\<alpha> process] \<Rightarrow> bool\<close> (\<open>_/ \<leadsto>\<^sup>*_/ _\<close> [50, 3, 51] 50)
  where   trace_\<tau>_trans : \<open>P \<leadsto>\<^sub>\<tau> P' \<Longrightarrow> P \<leadsto>\<^sup>* [] P'\<close>
  |          trace_tick_trans : \<open>P \<leadsto>\<^sub>\<checkmark> P' \<Longrightarrow> P \<leadsto>\<^sup>* [\<checkmark>] P'\<close>
  |          trace_Cons_ev_trans : \<open>P \<leadsto>\<^bsub>e\<^esub> P' \<Longrightarrow> P' \<leadsto>\<^sup>* s P'' \<Longrightarrow> P \<leadsto>\<^sup>* (ev e) # s P''\<close>\<close>}\<close>


text (in OpSemTransitions) \<open>
\<^noindent> The @{const [source] After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e} operator and the trace transition \<^term>\<open>P \<leadsto>\<^sup>*s Q\<close> are deeply 
related, which is expressed in the following theorem:
\<close>

(*<*)
(* BU : WAS : >>>>>> *)
abbreviation  local_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> trace \<Rightarrow> '\<alpha> process\<close> (infixl \<open>after\<^sub>\<T>\<close> 77)
  where \<open>P after\<^sub>\<T> e \<equiv> AfterExt.After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e \<Psi> \<Omega> P e\<close>
(* <<<<<< *)

(* BU's patch (a more closer error to the problem) : >>>>>> *)
abbreviation (in OpSemTransitions)  local_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> trace \<Rightarrow> '\<alpha> process\<close> (infixl \<open>after\<^sub>\<T>\<close> 77)
  where \<open>P after\<^sub>\<T> e \<equiv> AfterExt.After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e \<Psi> \<Omega> P e\<close>

(* notation local_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e (infixl \<open>after\<^sub>\<T>\<close> 77) *)

axiomatization \<tau>_trans :: \<open>['\<alpha> process, '\<alpha> process] \<Rightarrow> bool\<close> (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50)
  where OpSem_axioms_ok : \<open>OpSemTransitions \<Psi> \<Omega> \<tau>_trans\<close>

abbreviation  local_trace_trans :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> trace \<Rightarrow> '\<alpha> process \<Rightarrow> bool\<close> 
                                 (\<open>_/ \<leadsto>\<^sup>*_/ _\<close> [50, 3, 51] 50)
                                 where \<open>P \<leadsto>\<^sup>*s Q \<equiv> OpSemTransitions.trace_trans \<Psi> \<Omega> \<tau>_trans P s Q\<close>

(* notation \<tau>_trans (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50)
notation local_trace_trans (\<open>_/ \<leadsto>\<^sup>*_/ _\<close> [50, 3, 51] 50) *)
(*>*)

Theorem* (in OpSemTransitions) [trace_trans_After_trace_correspondence :: "theorem",
         short_name = \<open>\<open>Bridge between trace transition and $After_{trace}$ operator\<close>\<close>]\<open>\

\<^bigskip> @{thm (lhs) OpSemTransitions.trace_trans_iff_T_and_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_\<tau>_trans[of \<Psi> \<Omega> \<open>(\<leadsto>\<^sub>\<tau>)\<close>]}
if and only if @{thm (rhs) OpSemTransitions.trace_trans_iff_T_and_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_\<tau>_trans[of \<Psi> \<Omega> \<open>(\<leadsto>\<^sub>\<tau>)\<close>]}.
\<close>

(*<*)
no_notation local_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e (infixl \<open>after\<^sub>\<T>\<close> 77) 
no_notation \<tau>_trans (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50)
no_notation local_trace_trans (\<open>_/ \<leadsto>\<^sup>*_/ _\<close> [50, 3, 51] 50)

context OpSemTransitions
begin
(*>*)

(*
text \<open>
Of course one can remark that this result is clearly corresponding to the definitions of the
event transition (@{technical implem}) where:
  \<^item> \<^term>\<open>P \<leadsto>\<^bsub>e\<^esub> Q\<close> (resp. \<^term>\<open>P \<leadsto>\<^sub>\<checkmark> Q\<close>) is replaced by \<^term>\<open>P \<leadsto>\<^sup>*s Q\<close>
  \<^item> \<^term>\<open>P\<^sup>0\<close> is replaced by \<^term>\<open>\<T> P\<close>
  \<^item> \<^term>\<open>P after\<^sub>\<checkmark> (ev e)\<close> (resp. \<^term>\<open>P after\<^sub>\<checkmark> \<checkmark>\<close>) is replaced by \<^term>\<open>P after\<^sub>T\<^sub>r\<^sub>a\<^sub>c\<^sub>e s\<close>.\<close>
  \<^item> \<^term>\<open>P after\<^sub>\<checkmark> (ev e)\<close> (resp. \<^term>\<open>P after\<^sub>\<checkmark> \<checkmark>\<close>) is replaced by \<^term>\<open>P after\<^sub>\<T> s\<close>.

*)
text \<open>Informally spoken, \<^term>\<open>P after\<^sub>\<T> s\<close> is the the least deterministic process that we can
expect from process \<^term>\<open>P\<close> after the trace \<^term>\<open>s\<close>. This interpretation will become clearer
when we will instantiate the formal \<open>(\<leadsto>\<^sub>\<tau>)\<close>-relation of the locale with concrete
refinements in @{technical (unchecked) variants}.

Since the projections for the @{const [source] After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e} operator are relatively easy to handle,
this theorem is an important new weapon in our arsenal.
We will illustrate this by the following ``reality checks'' which have concrete applications
when certifying traces or divergences.
\<close>

(*<*)
end

notation local_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e (infixl \<open>after\<^sub>\<T>\<close> 77)
notation \<tau>_trans (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50)
notation local_trace_trans (\<open>_/ \<leadsto>\<^sup>*_/ _\<close> [50, 3, 51] 50)

lemma Refusals_def: \<open>\<R> Q = {X. ([], X) \<in> \<F> Q}\<close>
  by (simp add: Refusals_iff set_eq_iff)

(*>*)

Theorem*[reality_checks_equivalences::"theorem", short_name = \<open>\<open>Reality Checks\<close>\<close>]\<open>\
   \<^item> We have @{thm (lhs) OpSemTransitions.T_trace_trans_reality_check[OF OpSem_axioms_ok]}
     if and only if @{thm (rhs) OpSemTransitions.T_trace_trans_reality_check[OF OpSem_axioms_ok]}.
   \<^item> Under the assumption @{thm (prem 1) OpSemTransitions.D_trace_trans_reality_check_weak[OF OpSem_axioms_ok]}
     of unicity of the least element of \<open>(\<leadsto>\<^sub>\<tau>)\<close>, a trace
     @{thm (prem 2) OpSemTransitions.D_trace_trans_reality_check_weak[OF OpSem_axioms_ok]} verifies
     @{thm (lhs) OpSemTransitions.D_trace_trans_reality_check_weak[OF OpSem_axioms_ok]} if and only if
     @{thm (rhs) OpSemTransitions.D_trace_trans_reality_check_weak[OF OpSem_axioms_ok]}.
   \<^item> Under the assumption @{thm (prem 1) OpSemTransitions.F_trace_trans_reality_check_weak[OF OpSem_axioms_ok]}
     that a \<open>\<tau>\<close> transition implies F-refinement, and if
     @{thm (prem 2) OpSemTransitions.F_trace_trans_reality_check_weak[OF OpSem_axioms_ok]},
     we have @{thm (lhs) OpSemTransitions.F_trace_trans_reality_check_weak[OF OpSem_axioms_ok]} if and only if
     @{thm (rhs) OpSemTransitions.F_trace_trans_reality_check_weak[OF OpSem_axioms_ok]}.
\<close>
text\<open>\<^noindent>(where @{thm (lhs) Refusals_def[of Q]} is the set of refusals of \<^term>\<open>Q\<close>, defined as @{thm (rhs) Refusals_def[of Q]}).\<close>
(*

Proposition*[projections_After_trace :: "proposition", short_name = \<open>\<open>Projections of $After_{trace}$\<close>\<close>]\<open>\
@{thm [display] AfterExt.F_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_eq[of _ _ \<Psi> \<Omega>]
                AfterExt.D_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_eq[of _ _ \<Psi> \<Omega>]
                AfterExt.T_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_eq[of _ _ \<Psi> \<Omega>]}\<close>

text \<open>These equivalences are proved with @{theorem trace_trans_After_trace_correspondence}
      (for direct implication, indirect is easier).
      They may have concrete applications by paving the way for trace or divergence certification.\<close> 

*)


subsection*[bisimulation::technical, main_author="Some(@{author ''ben''}::author)", level= "Some 3"]
\<open>Strong Induction and (Bi)Simulations\<close>

text\<open>\<^noindent> The following theorem (and its generalizations not shown here) represents a new form of
induction over the set of reachable processes:  \<close>
Theorem*[strong_induct :: "theorem",
         short_name = \<open>\<open>Strong Induction for Refinements\<close>\<close>]\<open>Let \<open>f\<close> be a continuous function:

@{prop [break, indent=5]
\<open>\<exists>s\<in>\<T> P. tickFree s \<and> Q = P after\<^sub>\<T> s 
  \<Longrightarrow> (\<And>s x. s \<in> \<T> P \<Longrightarrow> \<forall>y. (\<exists>s\<in>\<T> P. tickFree s \<and> y = P after\<^sub>\<T> s) \<longrightarrow> x \<sqsubseteq>\<^sub>F\<^sub>D y \<Longrightarrow> f x \<sqsubseteq>\<^sub>F\<^sub>D P after\<^sub>\<T> s) 
  \<Longrightarrow> (\<mu> x. f x) \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>}\<close>

(*<*)
no_notation local_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e (infixl \<open>after\<^sub>\<T>\<close> 77)
no_notation \<tau>_trans (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50)
no_notation local_trace_trans (\<open>_/ \<leadsto>\<^sup>*_/ _\<close> [50, 3, 51] 50)
context OpSemTransitions begin (*>*)
(*>*)

text \<open>Note that as in Hoare and Jifengs approach, there will  always be infinite sequences of
 \<open>\<tau>\<close> transitions. This is a consequence of the fact that the FD-refinement is
reflexive. More generally speaking, since any process equality \<^term>\<open>P = Q\<close> is subsumed by 
the reflexivity  \<^term>\<open>P \<leadsto>\<^sub>\<tau> Q\<close>, this is unavoidable: unfolding fixed points, for example, also 
falls into the category of infinite sequences of \<open>\<tau>\<close> transitions. Compared to classical operational 
semantics in CCS, which is defined purely in terms of syntactic manipulations on process-terms, 
this means that we can never have  ``strong simulations'' in our denotational 
framework, which is based on higher-order abstract syntax and a congruence generated from the equality
on the semantic domain. Rather, we will target \<^emph>\<open>weak\<close> transitions resp. simulations, which are,
as we argue, more suited for the semantic treatment we are heading for.\<close>


(*<*)
end

end

(*  which can be interpreted as "when \<^term>\<open>s\<close> is a trace of
\<^term>\<open>P\<close>, we can expect at least \<^term>\<open>P after\<^sub>\<T> s\<close> from \<^term>\<open>P\<close> after \<^term>\<open>s\<close>"

Initially defined on @{term [show_types] \<open>P :: '\<alpha> process\<close>} and @{term [show_types] \<open>e :: '\<alpha>\<close>},
the @{const [source] After} was extended to @{term [show_types] \<open>e :: '\<alpha> event\<close>} with 
@{const [source] After\<^sub>t\<^sub>i\<^sub>c\<^sub>k}. Reformulating this explication with the notation \<open>P / s\<close>, we first 
defined \<open>P / [ev e]\<close> and extended it to \<open>P / [e]\<close>. It is now time to construct the full version \<open>P / s\<close>.
Without any surprise, since a trace is just of type \<^typ>\<open>'\<alpha> event set\<close>, we use an inductive definition.
 
 definition \<Omega> :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> process\<close>
  where \<open>\<Omega> \<equiv> undefined\<close> 


text \<open>
On this new operator, the authors proved classical properties (monotony, continuity under some
assumptions on \<^term>\<open>\<Psi>\<close> and \<^term>\<open>\<Omega>\<close>, etc.) but also more elaborated ones like the following:
\<close> 


text \<open>\<^noindent> This becomes really interesting when we associate the
        trace transition that we will define below.\<close>
 

(* no_notation local_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e (infixl \<open>after\<^sub>\<T>\<close> 77) *)

subsection*[trace_trans::technical,main_author="Some(@{author ''ben''}::author)"]
\<open>The Trace Transition\<close>


text \<open>
The two event transitions \<^term>\<open>P \<leadsto>\<^bsub>e\<^esub> Q\<close> and \<^term>\<open>P \<leadsto>\<^sub>\<checkmark> Q\<close> can also be extended to a trace
@{term [show_types] \<open>s :: '\<alpha> trace\<close>} with the following inductive definition.
\<close>


text \<open>
The reason why we have to handle differently \<^term>\<open>\<checkmark>\<close> and \<^term>\<open>ev e\<close> is deeply related to the
fact that a trace of a process is \<^const>\<open>front_tickFree\<close>, that is to say \<^term>\<open>\<checkmark>\<close> can only
occur at the end. Therefore we can add an event at the beginning of a trace only if this
event is not \<^term>\<open>\<checkmark>\<close>, or if this trace is empty.

This notion is quite powerful and behaves well: the authors proved the following "reality checks".
\<close>


Proposition*[reality_checks_one_side::"proposition", short_name = \<open>\<open>Reality checks\<close>\<close>]\<open>\
@{thm [display] OpSemTransitions.trace_trans_imp_F_if_\<tau>_trans_imp_leF[OF OpSem_axioms_ok]
                OpSemTransitions.trace_trans_imp_T[OF OpSem_axioms_ok]
                OpSemTransitions.tickFree_trace_trans_BOT_imp_D_if_\<tau>_trans_BOT_imp_eq_BOT[OF OpSem_axioms_ok]}
\<close>


text \<open>
This is for now only one-sided implications, the other sides will come from the link between
this trace transition and the @{const [source] After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e} operator.\<close>


subsection*[trace_trans_and_After_trace::technical,main_author="Some(@{author ''ben''}::author)"]
\<open>Reality Checks as Equivalences\<close>


text \<open>
\<^noindent> From this equivalence, one can establish:\<close>

Corollary*[reality_checks_other_side::"corollary", short_name = \<open>\<open>Reality Checks\<close>\<close>]\<open>\
@{thm [display] OpSemTransitions.tickFree_F_imp_exists_trace_trans[OF OpSem_axioms_ok]
                OpSemTransitions.T_imp_exists_trace_trans[OF OpSem_axioms_ok]
                OpSemTransitions.tickFree_D_imp_trace_trans_BOT[OF OpSem_axioms_ok]}
\<close>


*)
(*>*)

