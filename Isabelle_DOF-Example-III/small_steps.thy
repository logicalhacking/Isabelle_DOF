(*<*)
theory "small_steps"
  imports   "HOL-Library.LaTeXsugar"
            "Isabelle_DOF.scholarly_paper"
            "Isabelle_DOF-Ontologies.document_templates"
            "HOL-CSP_OpSem.Conclusion"
            "background" (* "HOL-CSP_OpSem.NewLaws" *)
begin

declare [[show_question_marks = false]]
(* show_brackets show_types show_sorts show_markup 
   show_structs show_question_marks show_type_emphasis *)

(*>*)




(* 
context AfterExt
begin

find_theorems \<open>Mprefix _ _ \<box> Mprefix _ _\<close>

lemma \<open>((STOP \<sqinter> (a \<rightarrow> (a \<rightarrow> STOP))) after a) = (a \<rightarrow> STOP)\<close>
  by (simp add: After_Ndet After_prefix initials_STOP initials_prefix)

find_theorems Sliding Mprefix

find_theorems \<open>Mprefix _ _ \<rhd> Mprefix _ _\<close>

lemma Mprefix_Sliding_Mprefix_same_set:
  \<open>(\<box> a \<in> A \<rightarrow> P a) \<rhd> (\<box> a \<in> A \<rightarrow> Q a) = \<box> a \<in> A \<rightarrow> (P a \<sqinter> Q a)\<close>
  by (simp add: F_Ndet D_Ndet Process_eq_spec
                F_Sliding F_Mprefix D_Sliding D_Mprefix) blast

thm D_After\<^sub>t\<^sub>r\<^sub>a\<^sub>c\<^sub>e_eq

lemma \<open>\<Omega> P = STOP\<close> if \<open>\<checkmark> \<in> initials P\<close>
proof -
  have \<open>P after\<^sub>\<checkmark> \<checkmark> = \<Omega> P\<close> by (simp add: After_tick_def)
  

end end

 *)

section*["smallSteps"::technical,main_author="Some(@{author ''ben''}::author)", level= "Some 3"]
\<open>Small Steps Semantics\<close>
(*<*)
context OpSemTransitions
begin
(*>*)

text \<open>
\<^noindent> Operational semantics of CSP involve two kinds of transitions that we need to define:

   \<^item> the \<open>\<tau>\<close> transition, denoted \<^term>\<open>P \<leadsto>\<^sub>\<tau> Q\<close>, (\<^emph>\<open>internal transition\<close>)
   \<^item> and the transition with an observable event (\<^emph>\<open>external transition\<close>) where we distinguish 
     the two cases resulting from the type sum of ``real'' events \<^term>\<open>ev e\<close> and the special event \<^term>\<open>\<checkmark>\<close>.
     The former transition will be denoted by \<^term>\<open>P \<leadsto>\<^bsub>e\<^esub> Q\<close>, the latter by \<^term>\<open>P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> Q\<close>.

Initially, Hoare and Jifeng in \<^cite>\<open>jifeng1993algebra\<close> proposed the following link
between the operational and denotational semantics: 
 \<^term>\<open>P \<leadsto>\<^sub>\<tau> Q \<equiv> P \<sqsubseteq>\<^sub>F\<^sub>D Q \<close> and \<^term>\<open>P \<leadsto>\<^bsub>e\<^esub> Q \<equiv> P \<sqsubseteq>\<^sub>F\<^sub>D (e \<rightarrow> Q) \<box> P \<close>.

\<^noindent> This approach is fine as long as we do not consider explicit termination of processes via
the special event \<^term>\<open>\<checkmark>\<close>. Moreover, the initial presentation was referring to fragment of
the language which foundation wrt. the underlying denotational semantics (including process ordering)
was still prone to subtle errors \<^cite>\<open>"tej.ea:corrected:1997"\<close>. For these reasons, we opted
for another bridge based on the @{term [source] \<open>After\<close>} operator, denoted \<^term>\<open>P after e\<close>, 
which represents a kind of inversion of \<^term>\<open>e \<rightarrow> P\<close>.
We will investigate the precise connection between both definitions in 
@{technical (unchecked)\<open>variants\<close>}.
\<close>
(* \<^vs>\<open>-0.2cm\<close> *)

(*<*)
end
(*>*)


subsection*["initials"::technical,main_author="Some(@{author ''ben''}::author)"]
\<open>The Notion of initials\<close>

(*<*)
context After
begin
(*>*)


text \<open>\<^noindent> As prerequisite, we need the events \<^term>\<open>P\<close> can start with,
called @{term [source] \<open>initials P\<close>} and denoted \<^term>\<open>P\<^sup>0\<close>.\<close>

(*
term\<open>
A first interesting observation is that by prefixing \<^term>\<open>P\<close> with \<^term>\<open>e\<close>,
we force the nonempty traces of \<^term>\<open>e \<rightarrow> P\<close> to begin with \<^term>\<open>ev e\<close>.
Therefore, the traces of \<^term>\<open>P after e\<close> should consist of the tails of the traces of \<^term>\<open>P\<close>
that were beginning with \<^term>\<open>ev e\<close>. 
This conclusion is quite simple but already raises an issue:
what happens if no trace of \<^term>\<open>P\<close> was beginning with \<^term>\<open>ev e\<close> ? Our process \<^term>\<open>P after e\<close>
would have its traces set empty, which is impossible since the empty trace \<^term>\<open>[]\<close> is always
a trace because of the invariant on top of which we built the \<^typ>\<open>'\<alpha> process\<close> type.

Since this seemed central, the authors decided first to capture and precisely study this
notion. Informally, @{term [source] \<open>initials P\<close>} (denoted \<^term>\<open>P\<^sup>0\<close>) is the set of events
with which \<^term>\<open>P\<close> can start. \<close>
*)
(* put a ref to the invariant ? is_process should be in a Definition* then *)

(*<*)
end
(*>*)

(*  \<^term>\<open>ev e\<close> (the non-tick-event \<^term>\<open>e::'\<alpha>\<close> of \<^typ>\<open>'\<alpha> event\<close>) in \<^term>\<open>P\<^sup>0\<close>*)

Definition*["initials_def"::"definition", short_name = \<open>\<open>$initials$\<close>\<close>]\<open>
The definition is straightforward: @{thm initials_def}

\<^noindent> or equivalently, thanks to \<^typ>\<open>'\<alpha> process\<close> properties, @{thm initials_def_bis}.\<close>

(*<*)
context After
begin
(*>*)

text\<open>Intuitively, for each \<^term>\<open>ev e\<close> in \<^term>\<open>P\<^sup>0\<close>,
the traces of \<^term>\<open>P after e\<close> should be the tails of the traces of \<^term>\<open>P\<close> beginning with \<^term>\<open>ev e\<close>.
The question arises what happens with processes \<^term>\<open>P\<close> where no trace is beginning with
\<^term>\<open>ev e\<close>. The semantic domain of \<^term>\<open>P after e\<close> will require that the set of traces is 
non-empty (recall the \<^term>\<open>is_process\<close> invariant from which we built the \<^typ>\<open>'\<alpha> process\<close> type).

The \<^const>\<open>initials\<close> are a notion commonly evoked in
\<^cite>\<open>"BrookesHR84" and "roscoe:csp:1998" and "Roscoe:UCS:2010"\<close>;
for now let us derive the general computational rules for it.
\<close>

(*<*)
end

(* 
text \<open>
One can observe that with the invariant, if \<^term>\<open>e # s\<close> is a trace of \<^term>\<open>P\<close>, \<^term>\<open>[e]\<close> is also a
trace of \<^term>\<open>P\<close>. Then (the other implication is straightforward) we have the equivalent definition:
\<close>

Definition*[initials_def_bis::"definition"]\<open>@{thm [show_question_marks = false] initials_def_bis}\<close> *)

(*>*)

Theorem*["initials_easy_laws"::"theorem", short_name = "\<open>Basic rules for $initials$\<close>"]\<open>
We derive:
\begin{center}
@{thm initials_BOT} \qquad @{thm initials_empty_iff_STOP} \qquad @{thm initials_SKIP}

@{thm initials_Ndet} \qquad @{thm initials_Det} \qquad @{thm initials_Mprefix[of e P]}

@{thm initials_Sliding} \qquad @{thm initials_Interrupt} \qquad @{thm [eta_contract = false] initials_Throw}
\end{center}
\<close>

(*<*)
lemma non_BOT_initials_Sync:
  \<open>P \<noteq> \<bottom> \<Longrightarrow> Q \<noteq> \<bottom> \<Longrightarrow> (P \<lbrakk>S\<rbrakk> Q)\<^sup>0 = P\<^sup>0 \<union> Q\<^sup>0 - ({\<checkmark>} \<union> ev ` S) \<union> P\<^sup>0 \<inter> Q\<^sup>0 \<inter> ({\<checkmark>} \<union> ev ` S)\<close>
  apply (simp add: initials_Sync)
  by auto

lemma BOT_initials_Sync: \<open>(\<bottom> \<lbrakk>S\<rbrakk> Q)\<^sup>0 = UNIV\<close> \<open>(P \<lbrakk>S\<rbrakk> \<bottom>)\<^sup>0 = UNIV\<close>
 by (simp_all add: initials_Sync)
(*>*)

Theorem*["initials_hard_laws"::"theorem", short_name = "\<open>More complex rules for $initials$\<close>"]\<open>
The following list requires more caution:
\<^item> @{thm initials_Renaming}
\<^item> @{thm initials_Seq}
\<^item> @{thm (concl) non_BOT_initials_Sync}

  if @{thm (prem 1) non_BOT_initials_Sync} and @{thm (prem 2) non_BOT_initials_Sync}
  (otherwise @{thm BOT_initials_Sync(1)} and @{thm BOT_initials_Sync(2)}).
\<close>

text \<open>
\<^noindent> The equality for the \<^const>\<open>Hiding\<close> operator, proved but omitted here, is downright difficult.
Note that the function \<^const>\<open>initials\<close> is of type \<^typ>\<open>'\<alpha> process \<Rightarrow> '\<alpha> event set\<close>.  
This implies that we may have \<^term>\<open>\<checkmark> \<in> P\<^sup>0\<close>, especially when \<^term>\<open>P = SKIP\<close> 
for which it serves as a refinement characterization.
\<close>

Theorem*["initial_tick_iff_FD_SKIP"::"theorem", short_name = \<open>\<open>Characterization of initial $\checkmark$\<close>\<close>]\<open>
@{thm (lhs) initial_tick_iff_FD_SKIP} if and only if @{thm (rhs) initial_tick_iff_FD_SKIP}.\<close>


(* This work was achieved for every CSP operator defined in the framework and some of the proofs
turned out to be extremely complex, clearly out of reach of paper-and-pencil reasoning. *)


subsection*[After::technical,main_author="Some(@{author ''ben''}::author)"]
\<open>The After Operator\<close>
(*<*)
context After
begin

(*>*)

(* and a precise clarification of the intended
relation to the operational semantics *)

(* Theorem*[After_Ndet::"theorem"]\<open>After_Ndet\<close> *)
text\<open>\<^noindent> There is no comprehensive treatment of the @{const [source] After} operator in the CSP 
literature, at least not with a formal definition and a precise clarification of the behaviour
wrt. the other operators; we had to do a number of trials and second-guessing here.
A key element is the notion of \<^const>\<open>initials\<close> (@{definition initials_def}); assuming 
\<^term>\<open>ev e \<in> initials P\<close> for @{term [show_types] \<open>P :: '\<alpha> process\<close>}, we obviously choose its failures
to be \<^term>\<open>{(s, X). (ev e # s, X) \<in> \<F> P}\<close> and its divergences \<^term>\<open>{s. ev e # s \<in> \<D> P}\<close>.

This solves part of the problem, but is not enough.
We will need a \<^emph>\<open>total\<close> definition of this operator in  HOL, \<^ie> we need to deal with the case
\<^term>\<open>ev e \<notin> initials P\<close>. There are basically the alternatives  \<^const>\<open>STOP\<close>,  \<^term>\<open>\<bottom>\<close>, or just
some underspecified constant \<^term>\<open>undefined\<close>. Since the actual choice made leads to
subtle differences in corner cases but does not impact the operational rules that 
we establish, we use Isabelle \<^theory_text>\<open>locale\<close>s mentioned in @{technical locales} to model this: 
\<close>

(*With , we can now provide a formal
definition of the @{const [source] After} operator. Given @{term [show_types] \<open>P :: '\<alpha> process\<close>} and
@{term [show_types] \<open>e :: '\<alpha>\<close>}, and assuming \<^term>\<open>ev e \<in> initials P\<close>, we choose its failures
to be \<^term>\<open>{(s, X). (ev e # s, X) \<in> \<F> P}\<close> and its divergences \<^term>\<open>{s. ev e # s \<in> \<D> P}\<close>.
*)

(*<*)
end
(*>*)
Definition*[After_def::"definition", short_name = \<open>\<open>$After$ operator\<close>\<close>]\<open>\
@{theory_text [display,indent=10]
\<open>locale After =  fixes \<Psi> :: \<open>['\<alpha> process, '\<alpha>] \<Rightarrow> '\<alpha> process\<close> begin

lift_definition After :: \<open>['\<alpha> process, '\<alpha>] \<Rightarrow> '\<alpha> process\<close> (infixl \<open>after\<close> 77)
  is \<open>\<lambda>P e.   if ev e \<in> initials P
              then ({(s, X). (ev e # s, X) \<in> \<F> P}, {s. ev e # s \<in> \<D> P})
              else (\<F> (\<Psi> P e), \<D> (\<Psi> P e))\<close>\<close>}\<close>

(*<*)
context After
begin
(*>*)


text \<open>Here, \<^theory_text>\<open>lift_definition\<close> is a variant of Isabelle constant \<^theory_text>\<open>definition\<close> which gives
automatic support for ``lifting'' an operation of the \<^typ>\<open>('\<alpha>,'\<delta>) process\<^sub>0\<close>-level to \<^typ>\<open>'\<alpha> process\<close>.
Note that \<^term>\<open>\<Psi>\<close> is a parameter of the locale requiring no assumption which can be 
instantiated freely.

The need of the theory of the  @{const [source] After} operator and its straightforward 
generalisation to traces denoted by \<open>P / s\<close> was identified at many places in the CSP literature
 \<^cite>\<open>"Hoare:1985:CSP:3921" and "roscoe:csp:1998" and "Roscoe:UCS:2010"\<close>, especially after 
basing the process-ordering \<^term>\<open>(\<sqsubseteq>)\<close> on its refusals.
@{const [source] After} and  \<open>P / s\<close> play a pivotal role when linking CSP to automata-theoretic
concepts; nevertheless it was commonly treated as something ``meta''\<^footnote>\<open>Roscoe states 
that ``this operator should not be thought of as an ordinary part of the CSP language''\<^cite>\<open>"roscoe:csp:1998"\<close>.\<close>.

In our work, we turn @{const [source] After} into an ordinary operator,
compatible with all other concepts, preserving the invariant of \<^typ>\<open>'\<alpha> process\<close>, 
enjoying monotony and continuity, and a number of distributivities (that one could call
``algebraic laws'') useful for establishing an operational semantics.
The formal proofs of this part of our theory amount to 2000 lines.
For example, we obtain equalities like the following:\<close>

(*<*)
end
  
definition \<Psi> :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> \<Rightarrow> '\<alpha> process\<close>
  where \<open>\<Psi> \<equiv> undefined\<close> 

abbreviation local_After :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> \<Rightarrow> '\<alpha> process\<close> (infixl \<open>after\<close> 77)
  where \<open>P after e \<equiv> After.After \<Psi> P e\<close>

thm After.After_Sync[of \<Psi>]
(*>*)

(* Theorem*[After_Sync::"theorem", short_name = \<open>\<open>$After$ distributes over $Sync$\<close>\<close>]\<open>\

@{thm [display, indent=10] After.After_Sync[of \<Psi>]}
\<close> *)

Theorem*[After_Sync::"theorem", short_name = \<open>\<open>$After$ and $Sync$\<close>\<close>]\<open>
@{thm [break] (lhs) After.After_Sync[of \<Psi>]} is equal to:

@{thm [break, indent = 10] (rhs) After.After_Sync[of \<Psi>]}
\<close>

text\<open>
The only operator for which we have not managed to establish such a property is \<^const>\<open>Hiding\<close>. 
However, we have at least the following monotonies:\<close>

Theorem*[After_Hiding::"theorem", short_name = \<open>\<open>$After$ and $Hiding$\<close>\<close>]\<open>\

@{thm [display, indent=10] After.Hiding_FD_Hiding_After_if_initial_inside[of _ _ _ \<Psi>]
                After.After_Hiding_FD_Hiding_After_if_initial_notin[of _ _ _ \<Psi>]}
\<close>

(*<*)
no_notation local_After (infixl \<open>after\<close> 77)

context After
begin
(*>*)

text \<open>\<^noindent> This will not be too restrictive for our construction thanks to the following theorem.\<close>

(*<*)
end
(*>*)

Theorem*[FD_iff_eq_Ndet::"theorem", short_name = \<open>\<open>Characterization of FD-refinement\<close>\<close>]\<open>\

The FD-refinement @{thm (lhs) FD_iff_eq_Ndet} holds if and only if @{thm (rhs) FD_iff_eq_Ndet}.
\<close>

subsection*["motivations"::technical,main_author="Some(@{author ''ben''}::author)"]
\<open>The Rationale for an Operational Semantics\<close>

(*<*)
context OpSemTransitions
begin
(*>*)

text \<open>
\<^noindent> With respect to the  \<open>\<tau>\<close> transition, \<^term>\<open>(\<leadsto>\<^sub>\<tau>)\<close>, we follow the choice of
Jifeng and Hoare in \<^cite>\<open>jifeng1993algebra\<close>, \<^ie> we define it by \<^term>\<open>P \<leadsto>\<^sub>\<tau> Q \<equiv> P \<sqsubseteq>\<^sub>F\<^sub>D Q\<close> .

With respect to the external transitions, we expect that:
  \<^item> \<^term>\<open>P \<leadsto>\<^bsub>e\<^esub> Q\<close> (resp. \<^term>\<open>P \<leadsto>\<^sub>\<checkmark>\<^bsub>r\<^esub> Q\<close>) is impossible if \<^term>\<open>ev e \<notin> P\<^sup>0\<close> (resp. \<^term>\<open>\<checkmark> \<notin> P\<^sup>0\<close>)
  \<^item> event transitions should absorb \<open>\<tau>\<close> transitions (on both sides) because \<^term>\<open>(\<sqsubseteq>\<^sub>F\<^sub>D)\<close> is transitive
  \<^item> since \<^term>\<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q\<close> can be interpreted as ``\<^term>\<open>Q\<close> is more deterministic than \<^term>\<open>P\<close>'',
    \<open>Q\<close> should be at least as deterministic as \<^term>\<open>P after e\<close>  when \<^term>\<open>P\<close> 
    makes a transition via event \<^term>\<open>e\<close>. \<^vs>\<open>-0.2cm\<close>

\<^noindent> The formalization still requires an extension of the @{const [source] After} operator to deal with \<^term>\<open>\<checkmark>\<close>.
This is achieved by extending the \<^theory_text>\<open>locale\<close> with an additional parameter \<^term>\<open>\<Omega>\<close>.
\<close>

(*<*)
end
(*>*)

Definition*[After_tick_def::"definition", short_name = \<open>\<open>$After_{tick}$ operator\<close>\<close>]\<open>\

@{theory_text [display, indent = 10] 
\<open>definition After\<^sub>t\<^sub>i\<^sub>c\<^sub>k :: \<open>['\<alpha> process, '\<alpha> event] \<Rightarrow> '\<alpha> process\<close> (infixl \<open>after\<^sub>\<checkmark>\<close> 77)
  where \<open>P after\<^sub>\<checkmark> e \<equiv> case e of ev x \<Rightarrow> P after x | \<checkmark> \<Rightarrow> \<Omega> P\<close>\<close>}\<close>


subsection*["implem"::technical,main_author="Some(@{author ''ben''}::author)"]
\<open>Finally: Formal Definitions of the Transition Relations\<close>

(* text\<open>
Coming back to the remaining issue: how do we handle \<^term>\<open>\<checkmark>\<close> ? We provide an extended
definition of \<^term>\<open>After\<close> by extending the \<^theory_text>\<open>locale\<close> with an additional parameter \<^term>\<open>\<Omega>\<close>.
\<close>

text\<open>The definition of the @{term [source] After} operator needed to be extended and the authors first
proposed \<^const>\<open>STOP\<close>. But here again, the value is not really important so it was later replaced
by a placeholder closer to Roscoe's book notation \<^cite>\<open>"Roscoe:UCS:2010"\<close>.
\<close>
*)

(*<*)
context OpSemTransitions
begin
(*>*)

text\<open>
\<^noindent> To make our construction as general as possible, we formalize the requirements of
@{technical motivations} by parameterizing the \<open>\<tau>\<close> transition in a \<^theory_text>\<open>locale\<close> with four hypotheses:

@{theory_text [display, indent=9,margin=78] \<open>locale OpSemTransitions = AfterExt \<Psi> \<Omega>
    for \<Psi> :: \<open>['\<alpha> process, '\<alpha>] \<Rightarrow> '\<alpha> process\<close> and \<Omega> :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> process\<close> +
  fixes \<tau>_trans :: \<open>['\<alpha> process, '\<alpha> process] \<Rightarrow> bool\<close> (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50)
assumes \<tau>_trans_NdetL: \<open>P \<sqinter> Q \<leadsto>\<^sub>\<tau> P\<close>
    and \<tau>_trans_transitivity: \<open>P \<leadsto>\<^sub>\<tau> Q \<Longrightarrow> Q \<leadsto>\<^sub>\<tau> R \<Longrightarrow> P \<leadsto>\<^sub>\<tau> R\<close>
    and \<tau>_trans_anti_mono_initials: \<open>P \<leadsto>\<^sub>\<tau> Q \<Longrightarrow> Q\<^sup>0 \<subseteq> P\<^sup>0\<close>
    and \<tau>_trans_mono_AfterExt: \<open>Q\<^sup>0 \<Longrightarrow> P \<leadsto>\<^sub>\<tau> Q \<Longrightarrow> P after\<^sub>\<checkmark> e \<leadsto>\<^sub>\<tau> Q after\<^sub>\<checkmark> e\<close>
begin

abbreviation ev_trans :: \<open>['\<alpha> process, '\<alpha>, '\<alpha> process] \<Rightarrow> bool\<close> (\<open>_ \<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
  where \<open>P \<leadsto>\<^bsub>e\<^esub> Q \<equiv> ev e \<in> P\<^sup>0 \<and> P after\<^sub>\<checkmark> ev e \<leadsto>\<^sub>\<tau> Q\<close>

abbreviation tick_trans :: \<open>['\<alpha> process, '\<alpha> process] \<Rightarrow> bool\<close> (\<open>_ \<leadsto>\<^sub>\<checkmark> _\<close> [50, 51] 50)
  where \<open>P \<leadsto>\<^sub>\<checkmark> Q \<equiv> \<checkmark> \<in> P\<^sup>0 \<and> P after\<^sub>\<checkmark> \<checkmark> \<leadsto>\<^sub>\<tau> Q\<close>\<close>}

\<^noindent> To sum up, this \<^theory_text>\<open>locale\<close> needs to be instantiated with:
 \<^item> \<^vs>\<open>-0.2cm\<close> a function \<^term>\<open>\<Psi>\<close> that is a placeholder for the value
   of \<^term>\<open>P after e\<close> when \<^term>\<open>ev e \<notin> initials P\<close>
 \<^item> a function \<^term>\<open>\<Omega>\<close> that is a placeholder for the value of \<^term>\<open>P after\<^sub>\<checkmark> \<checkmark>\<close>
 \<^item> a binary relation @{term [show_types] \<open>(\<leadsto>\<^sub>\<tau>)\<close>} which is compatible with \<^term>\<open>(\<sqinter>)\<close>,
   is transitive, makes \<^const>\<open>initials\<close> anti-monotonic and makes @{const [source] After\<^sub>t\<^sub>i\<^sub>c\<^sub>k} monotonic.\<close>
(*<*)
end

definition \<Omega> :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> process\<close>
  where \<open>\<Omega> P \<equiv> undefined\<close>

axiomatization \<tau>_trans :: \<open>['\<alpha> process, '\<alpha> process] \<Rightarrow> bool\<close> (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50)
  where OpSem_axioms_ok : \<open>OpSemTransitionsSync \<Psi> \<Omega> \<tau>_trans\<close>

abbreviation local_ev_trans :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> \<Rightarrow> '\<alpha> process \<Rightarrow> bool\<close> (\<open>_ \<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
  where \<open>P \<leadsto>\<^bsub>e\<^esub> P' \<equiv> ev e \<in> P\<^sup>0 \<and> AfterExt.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Psi> \<Omega> P (ev e) \<leadsto>\<^sub>\<tau> P'\<close>

abbreviation local_after :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> \<Rightarrow> '\<alpha> process\<close> (infixl \<open>after\<close> 77)
  where \<open>P after e \<equiv> After.After \<Psi> P e\<close>

(* definition S :: \<open>'\<alpha> set\<close> where \<open>S \<equiv> undefined\<close> 

definition e :: \<open>'\<alpha>\<close> where \<open>e \<equiv> undefined\<close>     

axiomatization precond_ok :: \<open>bool\<close> 
  where precond_ok : \<open>e \<notin> S\<close> *)


thm OpSemTransitionsSync.ev_trans_SyncL[OF OpSem_axioms_ok, of e S P P' Q]
(*>*)

text\<open>\<^vs>\<open>-0.2cm\<close> With these only four local axioms, we can derive most of the basic operational rules for 
 \<^const>\<open>SKIP\<close>, \<^term>\<open>e \<rightarrow> P\<close>, etc., and some of the rules for \<^term>\<open>P \ S\<close> or \<^term>\<open>P \<^bold>; Q\<close>, \<open>\<dots>\<close>
In order to recover the remaining rules, we divide the work. For each operator with a missing rule, 
we introduce a \<^theory_text>\<open>locale\<close> inheriting from \<^locale>\<open>OpSemTransitions\<close> in which we add a local axiom 
(about \<^term>\<open>(\<leadsto>\<^sub>\<tau>)\<close>). With the rules already proven and the denotational properties of the 
operator, we can derive the missing rules. Here, we illustrate the case of one of the rules for 
the \<^const>\<open>Sync\<close> operator:
\begin{center}
@{thm[mode=Rule, indent=15, margin=70] OpSemTransitionsSync.ev_trans_SyncL[OF OpSem_axioms_ok, of e S P P' Q]}
\end{center}
\<^vs>\<open>-0.3cm\<close>
\<close>

Proof*[proof_ev_trans_SyncL::"math_proof", short_name = \<open>\<open>Derivation of one of the $Sync$ Operational Rules\<close>\<close>]\<open>\

\<^noindent> Case \<^term>\<open>P = \<bottom>\<close> or \<^term>\<open>Q = \<bottom>\<close>, this is obvious because of the properties of \<^term>\<open>\<bottom>\<close>.

\<^noindent> Otherwise since @{thm (prem 2) OpSemTransitionsSync.ev_trans_SyncL[OF OpSem_axioms_ok, of e S P P' Q]} we have \<^term>\<open>ev e \<in> P\<^sup>0\<close>.

\<^noindent> With @{theorem initials_hard_laws} and
  @{thm (prem 1) OpSemTransitionsSync.ev_trans_SyncL[OF OpSem_axioms_ok, of e S P P' Q]},
  we additionally have \<^term>\<open>ev e \<in> (P \<lbrakk>S\<rbrakk> Q)\<^sup>0\<close>.

\<^noindent> Thus, from @{theorem After_Sync}, \<^term>\<open>(P \<lbrakk>S\<rbrakk> Q) after e\<close> is equal to \<^term>\<open>(P after e \<lbrakk>S\<rbrakk> Q) \<sqinter> (P \<lbrakk>S\<rbrakk> Q after e)\<close>
  if \<^term>\<open>ev e \<in> Q\<^sup>0\<close>, and \<^term>\<open>(P after e \<lbrakk>S\<rbrakk> Q)\<close> otherwise.

\<^noindent> In both cases, with \<^term>\<open>(\<leadsto>\<^sub>\<tau>)\<close> properties, we obtain \<^term>\<open>(P \<lbrakk>S\<rbrakk> Q) after e \<leadsto>\<^sub>\<tau> P after e \<lbrakk>S\<rbrakk> Q\<close>.

\<^noindent> Using the additional assumption that, in general,
  @{thm OpSemTransitionsSync.\<tau>_trans_SyncL[OF OpSem_axioms_ok]}, 
  we finally conclude that @{thm (concl) OpSemTransitionsSync.ev_trans_SyncL[OF OpSem_axioms_ok, of e S P P' Q]}.
\<close>

(*<*)
no_notation \<tau>_trans (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50)
no_notation local_ev_trans  (\<open>_ \<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
no_notation local_after (infixl \<open>after\<close> 77)

context OpSemTransitionsSliding
begin
(*>*)

text \<open>
% The case of \<^term>\<open>Renaming P f\<close> is a bit more tricky
% (involving polymorphic variables in @{term [show_types] \<open>f :: '\<alpha> \<Rightarrow> '\<beta>\<close>}).
% We solved the issue by a construction involving a duplication of the \<^theory_text>\<open>locale\<close>. 
Finally, by assembling the \<^theory_text>\<open>locale\<close>s of each operator (which is inheriting of all these \<^theory_text>\<open>locale\<close>s),
their instantiations lead to formal proofs that the core of the ruleset shown in @{technical (unchecked) "laws"}
are actually derivable for T,F, and FD semantics.
In the end, they all rely on the four assumptions of \<^locale>\<open>OpSemTransitions\<close> and on eight additional
assumptions of monotony for the first argument wrt. \<^term>\<open>(\<leadsto>\<^sub>\<tau>)\<close> for the operators @{const [source] Det},
@{const [source] Seq}, @{const [source] Hiding}, @{const [source] Sync}, @{const [source] Sliding},
@{const [source] Interrupt}, @{const [source] Throw} and @{const [source] Renaming} \<^eg> @{thm \<tau>_trans_SlidingL}.
Special cases of rules not in the core ruleset will be discussed in the subsequent sections.\<close>

(*<*)
end

end
(*>*) 
