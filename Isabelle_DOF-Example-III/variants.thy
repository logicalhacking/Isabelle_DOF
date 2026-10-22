(*<*)
theory "variants"
  imports   "Isabelle_DOF.scholarly_paper"
            (* "Isabelle_DOF-Ontologies.document_templates" *)
            "HOL-CSP_OpSem.Conclusion"
            "ComparisonWithJifengHoare"
            "big_steps"
begin
(*>*)

section*["variants"::technical,main_author="Some(@{author ''ben''}::author)", level= "Some 3"]
\<open>The Construction put into a Global Perspective\<close>

(* text \<open>As mentioned earlier, we are encouraged to define the \<open>\<tau>\<close> transition \<open>P \<leadsto>\<^sub>\<tau> Q\<close> as the well
      known failures divergences refinement \<^term>\<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>. Our \<^theory_text>\<open>locale\<close> construction was made
      for this, but we will also present here some variations.\<close>
 *)

subsection*["refinements"::technical,main_author="Some(@{author ''ben''}::author)", level= "Some 3"]
\<open>Transitions as Local Refinements\<close>

(*<*)
context OpSemFD
begin
(*>*)


text \<open>
\<^noindent> We use a \<^theory_text>\<open>sublocale\<close> to partially instantiate \<^locale>\<open>OpSemTransitions\<close> 
with @{term [source] \<open>(\<sqsubseteq>\<^sub>F\<^sub>D)\<close>}, \<^ie> by leaving \<^term>\<open>\<Psi>\<close> and \<^term>\<open>\<Omega>\<close> as parameters.
In this context we prove that we have only one remaining hypothesis : @{thm mono_\<Omega>_FD},
which is obvious if \<^term>\<open>\<Omega>\<close> takes the value \<^term>\<open>STOP\<close> (a choice commonly used in the literature, 
whether explicitly stated or implied). However, in principle, any constant function
is acceptable for \<^term>\<open>\<Omega>\<close> since we do not care about the traces after a termination\<^footnote>\<open>Therefore, 
we are free to choose for \<^term>\<open>\<Omega>\<close> \<^term>\<open>\<lambda>P. P \<sqinter> STOP\<close> or \<^term>\<open>\<lambda>P. Renaming P f\<close> or 
@{term [eta_contract=false ]\<open>\<lambda>P. (e \<rightarrow> P)\<close>}, \<open>\<dots>\<close>\<close>. 

Independent of this choice, we recover all the rules of operational semantics, and even better for 
the ``reality checks'' (@{theorem reality_checks_equivalences}) since we get rid of the hypotheses.

However, it remains unfortunate that in the right hand side of the equivalence for failures 
appears the denotational notion of refusals. 

One work-around for this problem are \<^emph>\<open>deterministic processes\<close>.
A process \<^term>\<open>P\<close> is said to be \<^const>\<open>deterministic\<close> if @{thm (rhs) deterministic_def[of P]}.
We will not detail much this notion here\<^footnote>\<open>We refer to \<^cite>\<open>"roscoe:csp:1998"\<close>.\<close>, but to cut a
long story short we prove that being in the refusals set of a \<^const>\<open>deterministic\<close> process \<^term>\<open>P\<close> 
is the same as non intersecting its @{const [source] initials} \<^term>\<open>P\<^sup>0\<close>. Moreover, the notion of
\<^const>\<open>deterministic\<close> is preserved by \<^const>\<open>tickFree\<close> trace transitions. We finally prove:\<close>

(*<*)
end

axiomatization \<Omega> :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> process\<close>
  where OpSemFD_axioms_ok : \<open>OpSemFD \<Omega>\<close>

abbreviation local_FD_trace_trans :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> trace \<Rightarrow> '\<alpha> process \<Rightarrow> bool\<close> (\<open>_ \<^sub>F\<^sub>D\<leadsto>\<^sup>*_ _\<close> [50, 3, 51] 50)
  where \<open>P \<^sub>F\<^sub>D\<leadsto>\<^sup>*s Q \<equiv> OpSemTransitions.trace_trans \<Psi> variants.\<Omega> (\<sqsubseteq>\<^sub>F\<^sub>D) P s Q\<close>


lemma local_deterministic_F_trace_trans_reality_check: 
  \<open>deterministic P \<Longrightarrow> tickFree s \<Longrightarrow> ((s, X) \<in> \<F> P) = (\<exists>Q. P \<^sub>F\<^sub>D\<leadsto>\<^sup>*s Q \<and> X \<inter> Q\<^sup>0 = {})\<close>
  by (fact OpSemFD.deterministic_F_trace_trans_reality_check [OF OpSemFD_axioms_ok])

thm local_deterministic_F_trace_trans_reality_check

thm OpSemFD.deterministic_F_trace_trans_reality_check [OF OpSemFD_axioms_ok]

(*>*)

Theorem*[deterministic_F_trace_trans_reality_check::"theorem", 
         short_name=\<open>\<open>Deterministic Version of failures reality Check\<close>\<close>]\<open>\ 

Assuming @{thm (prem 1) local_deterministic_F_trace_trans_reality_check} and
@{thm (prem 2) local_deterministic_F_trace_trans_reality_check}, we have: 

\<^hs>\<open>1.0cm \<close> @{thm (lhs) local_deterministic_F_trace_trans_reality_check} if and only if
  @{thm (rhs) local_deterministic_F_trace_trans_reality_check}.\<close>

(*<*)

context OpSemDT 
begin
(*>*)

text \<open> 
It came as a pleasant surprise when we observed that the same argument applies for the trace 
divergence refinement @{term [source] \<open>(\<sqsubseteq>\<^sub>D\<^sub>T)\<close>}. Initially defined and studied in \<^cite>\<open>TahaWY20\<close> for 
pure curiosity, it behaves remarkably well: the only remaining hypothesis is a monotony for
 \<^term>\<open>\<Omega>\<close> : @{thm mono_\<Omega>_DT} and we recover all the rules of the operational semantics. 

Of course by restricting ourselves to traces and the divergences, we can not reason about failures anymore. \<close>

(*<*)
end
context OpSemTransitions
begin
(*>*)


text \<open>It turns out that it is also possible to instantiate the \<open>\<tau>\<close> transition in the \<^theory_text>\<open>locale\<close>
 \<^locale>\<open>OpSemTransitions\<close> with the failure refinement or the trace refinement.
However, for them, the result is somewhat unimpressive.
The following table summarizes the rule sets corresponding to operators which can be established.

\begin{center}\begin{tabular}{|c|c|c|c|c|c|c|c|c|c|}
\hline
 & basic & \<^term>\<open>(\<box>)\<close> & \<^term>\<open>(\<^bold>;)\<close> & \<^term>\<open>(P \ S)\<close> & \<^term>\<open>P \<lbrakk>S\<rbrakk> Q\<close> & \<^term>\<open>(\<rhd>)\<close> & \<^term>\<open>(\<triangle>)\<close> & \<^term>\<open>Throw\<close> & \<^term>\<open>Renaming\<close>\\
\hline
\<^term>\<open>(\<sqsubseteq>\<^sub>F\<^sub>D)\<close> & \<open>\<checkmark>\<close> & \<open>\<checkmark>\<close> & \<open>\<checkmark>\<close> & \<open>\<checkmark>\<close> & \<open>\<checkmark>\<close> & \<open>\<checkmark>\<close> & \<open>\<checkmark>\<close> & \<open>\<checkmark>\<close> & \<open>\<checkmark>\<close>\\
\hline
\<^term>\<open>(\<sqsubseteq>\<^sub>D\<^sub>T)\<close> & \<open>\<checkmark>\<close> & \<open>\<checkmark>\<close> & \<open>\<checkmark>\<close> & \<open>\<checkmark>\<close> & \<open>\<checkmark>\<close> & \<open>\<checkmark>\<close> & \<open>\<checkmark>\<close> & \<open>\<checkmark>\<close> & \<open>\<checkmark>\<close>\\
\hline
\<^term>\<open>(\<sqsubseteq>\<^sub>F)\<close> & \<open>\<checkmark>\<close> & \<open>\<crossmark>\<close> & \<open>\<crossmark>\<close> & \<open>\<checkmark>\<close> & \<open>\<crossmark>\<close> & \<open>\<crossmark>\<close> & \<open>\<crossmark>\<close> & \<open>\<crossmark>\<close> & \<open>\<crossmark>\<close>\\
\hline
\<^term>\<open>(\<sqsubseteq>\<^sub>T)\<close> & \<open>\<checkmark>\<close> & \<open>\<checkmark>\<close> & \<open>\<crossmark>\<close> & \<open>\<checkmark>\<close> & \<open>\<crossmark>\<close> & \<open>\<checkmark>\<close> & \<open>\<checkmark>\<close> & \<open>\<crossmark>\<close> & \<open>\<crossmark>\<close>\\
\hline
\end{tabular}\end{center}

\<^noindent> where ``basic'' refers to the rules for absorption, \<^const>\<open>SKIP\<close>, \<^term>\<open>e \<rightarrow> P\<close>, 
@{term [source] \<open>\<box> a \<in> A \<rightarrow> P a\<close>}, @{term [source] \<open>\<sqinter> a \<in> A \<rightarrow> P a\<close>},
\<^term>\<open>P \<sqinter> Q\<close> and @{term [source] \<open>\<mu> X. f X\<close>} that we  get as soon as we  instantiate
 \<^locale>\<open>OpSemTransitions\<close>.
\<close>

(* text \<open>

 the \<^theory_text>\<open>locale\<close> \<^locale>\<open>OpSemTransitions\<close>,
the \<open>\<tau>\<close> transition implies the trace refinement \<^term>\<open>(\<sqsubseteq>\<^sub>T)\<close>. 
What else can be used as a \<open>\<tau>\<close> transition ? An interesting observation is that under the assumptions
of the \<^theory_text>\<open>locale\<close> \<^locale>\<open>OpSemTransitions\<close> one can prove that @{thm (concl) \<tau>_trans_imp_leT} when
@{thm (prem 1) \<tau>_trans_imp_leT}. In other words, the \<open>\<tau>\<close> transition we choose must at least
imply the trace refinement.

We tried then with the two remaining refinements that have this property: \<^term>\<open>(\<sqsubseteq>\<^sub>F)\<close>
and \<^term>\<open>(\<sqsubseteq>\<^sub>T)\<close> itself. But the result is in the end is less sensational. If we can instantiate
the first \<^theory_text>\<open>locale\<close>, we can not get much rules of operational semantics. In facts (in addition to
the rules for absorption, \<^const>\<open>SKIP\<close>, \<^term>\<open>e \<rightarrow> P\<close>, \<^term>\<open>P \<sqinter> Q\<close> and @{term [source] \<open>\<mu> X. f X\<close>}
that we automatically obtain as soon as we can instantiate \<^locale>\<open>OpSemTransitions\<close>), we only
recover the operational rules of:
 \<^item> \<^term>\<open>P \ S\<close> for \<^term>\<open>(\<sqsubseteq>\<^sub>F)\<close>
 \<^item> \<^term>\<open>P \<box> Q\<close>, \<^term>\<open>P \ S\<close>, \<^term>\<open>P \<rhd> Q\<close> and \<^term>\<open>P \<triangle> Q\<close> for \<^term>\<open>(\<sqsubseteq>\<^sub>T)\<close>.

\<close> *)
text \<open> 
Being able to instantiate the locale represents the main result: we can formally derive 
an operational semantics from the denotational one developed in \<^session>\<open>HOL-CSP\<close>. This also 
constitutes a formal proof that the expected rules are consistent
(see @{technical laws}).

And last but not least, we obtained actually two interesting variants with FD-refinement and DT-refinement,
plus all the sub-variants resulting from the free choice of \<^term>\<open>\<Psi>\<close> and \<^term>\<open>\<Omega>\<close>.
\<close>

(*<*)
end
(*>*)

subsection*["copy_buffer_illustration"::technical,main_author="Some(@{author ''ben''}::author)", level= "Some 3"]
\<open>Running Example: the Copy Buffer Again\<close>

text \<open>\<^noindent> From the derived laws of @{technical laws} we can formally obtain the following LTSs
for the Copy Buffer example presented in @{technical proofs}. Note that the \<open>\<tau>\<close>-transition are collapsed
thanks to the absorbtion rules, and with the properties of \<^const>\<open>initials\<close> we ensure that
no external transition is missed. Further note that \<open>t1\<close> is a key for the term
\<^term>\<open>mid e \<rightarrow> ack \<rightarrow> SEND\<close>, \<open>t2\<close> for \<^term>\<open>ack \<rightarrow> SEND\<close>, \<open>t3\<close> for
\<^term>\<open>right e \<rightarrow> ack \<rightarrow> REC\<close>, \<open>t4\<close> for \<^term>\<open>ack \<rightarrow> REC\<close>, and finally
\<open>t5\<close> for \<^term>\<open>right e \<rightarrow> SYS\<close>. \<close>

text \<open>
\begin{figure*}[h!]
    \centering
        \begin{tikzpicture}
        \node[state, minimum size = 1.3cm] (0) at (1.5,2.6) {\<^const>\<open>SEND\<close>};
        \node[state, minimum size = 1.3cm] (1) at (0,0) {\<open>t1\<close>};
        \node[state, minimum size = 1.3cm] (2) at (3,0) {\<open>t2\<close>};
        \draw (0) edge[bend right=15, left] node {\<^term>\<open>left\<close> $?e$} (1)
              (1) edge[bend right=15, below] node {\<^term>\<open>mid e\<close>} (2)
              (2) edge[bend right=15, right] node {\<^const>\<open>ack\<close>} (0) ;
        % \node at (1.5,3.5) {\<^const>\<open>SEND\<close>};

        \node[state, minimum size = 1.3cm] (10) at (7,2.6) {\<^const>\<open>REC\<close>};
        \node[state, minimum size = 1.3cm] (11) at (5.5,0) {\<open>t3\<close>};
        \node[state, minimum size = 1.3cm] (12) at (8.5,0) {\<open>t4\<close>};
        \draw (10) edge[bend right=15, left] node {\<^term>\<open>mid\<close> $?e$} (11)
              (11) edge[bend right=15, below] node {\<^term>\<open>right e\<close>} (12)
              (12) edge[bend right=15, right] node {\<^const>\<open>ack\<close>} (10);
        % \node at (7,3.5) {\<^const>\<open>REC\<close>};

        \node[state, minimum size = 1.3cm] (20) at (11,2.6) {\<^const>\<open>SYS\<close>};
        \node[state, minimum size = 1.3cm] (21) at (11,0) {\<open>t5\<close>};
        \draw (20) edge[bend right=15, left] node {\<^term>\<open>left\<close>$?e$} (21)
              (21) edge[bend right=15, right] node {\<^term>\<open>right e\<close>} (20);
        % \node at (11,3.5) {\<^const>\<open>SYS\<close>};

        \end{tikzpicture}
    \caption{LTSs for the Copy Buffer Example}
\end{figure*}\<close>


subsection*["comparison"::technical,main_author="Some(@{author ''ben''}::author)", level= "Some 3"]
\<open>Comparison with the Work of Jifeng and Hoare\<close>

(*<*) context OpSemTransitions begin (*>*)

text \<open>
\<^noindent> As mentioned in @{technical smallSteps}, Hoare and Jifeng in \<^cite>\<open>jifeng1993algebra\<close> defined 
\<^term>\<open>P \<leadsto>\<^sub>\<tau> Q \<equiv> P \<sqsubseteq>\<^sub>F\<^sub>D Q \<close> and

\<^noindent> \<^term>\<open>P \<leadsto>\<^bsub>e\<^esub> Q \<equiv> P \<sqsubseteq>\<^sub>F\<^sub>D (e \<rightarrow> Q) \<box> P \<close>. Looking at our version (instantiated with the
FD-refinement), we differ on the external transition with \<^term>\<open>ev e \<in> P\<^sup>0 \<and> P after e \<sqsubseteq>\<^sub>F\<^sub>D Q\<close> instead.
What happened? Did we miss something?

In general, from the generic \<open>\<tau>\<close> transition in our \<^theory_text>\<open>locale\<close>,
we can define @{thm ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_def}. We immediately prove that their version is stronger than ours
\<^ie> @{thm ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_imp_ev_trans}. However, adding the two hypotheses of monotony on \<^term>\<open>(\<leadsto>\<^sub>\<tau>)\<close>, 
we can prove the reciprocal. The situation is summarized in the following theorem:
\<close>

(*<*)
end

notation \<tau>_trans (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50)
notation local_ev_trans  (\<open>_ \<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
abbreviation local_ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> \<Rightarrow> '\<alpha> process \<Rightarrow> bool\<close>
                                  (\<open>_ \<^bsub>HOARE\<^esub>\<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
                                  where \<open>P \<^bsub>HOARE\<^esub>\<leadsto>\<^bsub>e\<^esub> Q \<equiv> OpSemTransitions.ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E (\<leadsto>\<^sub>\<tau>) P e Q\<close>
(* abbreviation local_After\<^sub>t\<^sub>i\<^sub>c\<^sub>k :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> event \<Rightarrow> '\<alpha> process\<close> (infixl \<open>after\<^sub>\<checkmark>\<close> 77)
  where \<open>P after\<^sub>\<checkmark> e \<equiv> AfterExt.After\<^sub>t\<^sub>i\<^sub>c\<^sub>k \<Psi> \<Omega> P e\<close> *)

thm OpSemTransitions.hyps_on_\<tau>_trans_imp_ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_iff_ev_trans[OF OpSem_axioms_ok]

find_theorems name: ev_trans_is

(*>*)

Theorem*[equivalence_ev_trans::"theorem", short_name = \<open>\<open>Equivalence of Transitions\<close>\<close>]\<open>\

Assuming a \<open>\<tau>\<close> monotony for \<open>prefix\<close>:
@{thm (prem 2) OpSemTransitions.hyps_on_\<tau>_trans_imp_ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_iff_ev_trans[OF OpSem_axioms_ok]}

\<^noindent> and for @{const [source] Det}:
@{thm (prem 1) OpSemTransitions.hyps_on_\<tau>_trans_imp_ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_iff_ev_trans[OF OpSem_axioms_ok]},

\<^noindent> we have @{thm (lhs) OpSemTransitions.hyps_on_\<tau>_trans_imp_ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E_iff_ev_trans[OF OpSem_axioms_ok]}
if and only if \<^term>\<open>P \<leadsto>\<^bsub>e\<^esub> Q\<close>.
\<close>


(*<*)
no_notation \<tau>_trans (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50)
no_notation local_ev_trans (\<open>_ \<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)
no_notation local_ev_trans\<^sub>H\<^sub>O\<^sub>A\<^sub>R\<^sub>E (\<open>_ \<^bsub>HOARE\<^esub>\<leadsto>\<^bsub>_\<^esub> _\<close> [50, 3, 51] 50)

context OpSemTransitions
begin
(*>*)

text \<open>
These two hypotheses are verified by all four refinement relations.
% \<^term>\<open>(\<sqsubseteq>\<^sub>F\<^sub>D)\<close>, \<^term>\<open>(\<sqsubseteq>\<^sub>D\<^sub>T)\<close>,\<^term>\<open>(\<sqsubseteq>\<^sub>F)\<close> and \<^term>\<open>(\<sqsubseteq>\<^sub>T)\<close>. 
In other words, the definition of Jifeng and Hoare is equivalent to ours 
% (even using \<^term>\<open>(\<sqsubseteq>\<^sub>D\<^sub>T)\<close>, \<^term>\<open>(\<sqsubseteq>\<^sub>F)\<close> or \<^term>\<open>(\<sqsubseteq>\<^sub>T)\<close> instead of \<open>(\<sqsubseteq>\<^sub>F\<^sub>D)\<close>) \<open>\<dots>\<close> 
as long as we do not consider \<^term>\<open>\<checkmark>\<close>!

Indeed, as mentioned in @{technical smallSteps}, their definition can not handle \<^term>\<open>\<checkmark>\<close> because
the \<open>prefix\<close> operator only accepts a ``real'' event. In this sense one can say that our construction
is a generalization. Furthermore, the @{const [source] After\<^sub>t\<^sub>i\<^sub>c\<^sub>k} operator gives a direct access
to the least deterministic process that can be expected while doing an external transition, which 
is not easily accessible from the version of Hoare and Jifeng. Finally we  note that the
@{const [source] After} operator is itself of interest, even if we restrict ourselves to
a purely denotational reasoning\<^footnote>\<open>The interested reader is referred to examples
of fixed point induction to reason about deadlock freeness\<^cite>\<open>"HOL-CSP_OpSem-AFP"\<close>.\<close>.
\<close>


(*<*)
end
(*>*)

subsection*["differences_classical_laws"::technical,main_author="Some(@{author ''ben''}::author)", level= "Some 3"]
\<open>Discussion\<close>

(*<*)

locale OpSemTransitionAll_plus_Roscoe_Omega = OpSemTransitionsAll \<Psi> \<Omega> \<tau>_trans 
  for \<Psi> :: \<open>['\<alpha> process, '\<alpha>] \<Rightarrow> '\<alpha> process\<close>
  and \<Omega> :: \<open>'\<alpha> process \<Rightarrow> '\<alpha> process\<close>
  and \<tau>_trans :: \<open>['\<alpha> process, '\<alpha> process] \<Rightarrow> bool\<close> (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50) +
  fixes  \<Omega>' :: \<open>'\<alpha> process\<close>
  assumes Roscoe_tick_trans_SyncL : \<open>P \<leadsto>\<^sub>\<checkmark> P' \<Longrightarrow> P \<lbrakk>S\<rbrakk> Q \<leadsto>\<^sub>\<tau> \<Omega>' \<lbrakk>S\<rbrakk> Q\<close>
      and Roscoe_tick_trans_SyncR : \<open>Q \<leadsto>\<^sub>\<checkmark> Q' \<Longrightarrow> P \<lbrakk>S\<rbrakk> Q \<leadsto>\<^sub>\<tau> P \<lbrakk>S\<rbrakk> \<Omega>'\<close>
      and Roscoe_tick_trans_Sync_both : \<open>\<Omega>' \<lbrakk>S\<rbrakk> \<Omega>' \<leadsto>\<^sub>\<checkmark> \<Omega>'\<close>
begin


notation \<tau>_trans (infixl \<open>\<leadsto>\<^sub>\<tau>\<close> 50)



thm \<tau>_trans_SeqR

lemma ev_trans_SeqR : \<open>P \<leadsto>\<^sub>\<checkmark> P' \<Longrightarrow> Q \<leadsto>\<^bsub>e\<^esub> Q' \<Longrightarrow> P \<^bold>; Q \<leadsto>\<^bsub>e\<^esub> Q'\<close>
  using \<tau>_trans_SeqR \<tau>_trans_eq \<tau>_trans_ev_trans by blast

lemma tick_trans_SeqR : \<open>P \<leadsto>\<^sub>\<checkmark> P' \<Longrightarrow> Q \<leadsto>\<^sub>\<checkmark> Q' \<Longrightarrow> P \<^bold>; Q \<leadsto>\<^sub>\<checkmark> Q'\<close>
  by (meson \<tau>_trans_SeqR \<tau>_trans_eq \<tau>_trans_tick_trans)

lemma \<open>P \<leadsto>\<^sub>\<checkmark> P' \<Longrightarrow> P \<leadsto>\<^sub>\<tau> SKIP\<close>
  using initial_tick_imp_\<tau>_trans_SKIP by blast


(*>*)

text \<open>
\<^noindent> Our construction and the resulting proof rules (@{technical laws}) permit the
following observations:
  \<^enum> As a general rule, when looking at a transition involving the special event \<^term>\<open>\<checkmark>\<close>, we obtain
    something like \<open>P \<otimes> Q \<leadsto>\<^sub>\<checkmark> \<Omega> SKIP\<close>. This is a consequence of @{theorem initial_tick_iff_FD_SKIP}
    and @{theorem FD_iff_eq_Ndet}.
  \<^enum> The ``absorption'' rules at the beginning allow additional rules to be derived directly \<^eg>
    \begin{center}
    @{thm [mode = Rule] ev_trans_SeqR} \qquad @{thm [mode = Rule] tick_trans_SeqR}
    \end{center}
  \<^enum> About the termination of @{const [source] Sync} operator, Roscoe postulates
    in \<^cite>\<open>"roscoe:csp:1998"\<close> that:
    \begin{center}
    @{thm [mode = Rule]  Roscoe_tick_trans_SyncL} \qquad
    @{thm [mode = Rule]  Roscoe_tick_trans_SyncR} \qquad
    @{thm [mode = Axiom] Roscoe_tick_trans_Sync_both}
    \end{center}
    where \<^term>\<open>\<Omega>'\<close> is intended to denote any process that has already terminated. In the common
    interpretation that \<^term>\<open>\<Omega>'\<close> can be identified with \<^term>\<open>STOP\<close>, these rules are incompatible
    with the denotational properties since we have \<^term>\<open>STOP \<lbrakk>S\<rbrakk> STOP = STOP\<close> that
    can not make a \<^term>\<open>\<checkmark>\<close> transition.
    Under the assumptions of the \<^theory_text>\<open>locale\<close>, we rather prove the rules of @{technical laws}.
  \<^enum> We deliberately focus in @{technical laws} on the operational rules that we
    found in the literature. In particular for the @{const [source] Throw} operator,
    where the right argument remains inactive until an exception is triggered, we should not write
    a right \<open>\<tau>\<close> transition rule like:
    \begin{center}
    @{term [mode = Rule, eta_contract = false] \<open>\<forall>a\<in>A. Q a \<leadsto>\<^sub>\<tau> Q' a \<Longrightarrow> P \<Theta> a \<in> A. Q a \<sqsubseteq>\<^sub>F\<^sub>D P \<Theta> a \<in> A. Q' a\<close>}
    \end{center}
    while this is true when instantiating \<^term>\<open>(\<leadsto>\<^sub>\<tau>)\<close> with \<^term>\<open>(\<sqsubseteq>\<^sub>F\<^sub>D)\<close>, \<^term>\<open>(\<sqsubseteq>\<^sub>D\<^sub>T)\<close>, \<^term>\<open>(\<sqsubseteq>\<^sub>F)\<close> or \<^term>\<open>(\<sqsubseteq>\<^sub>T)\<close>.
\<close>

(* 
 \begin{center}
    @{thm [mode = Rule]  \<tau>_trans_SKIP_SyncL} \qquad
    @{thm [mode = Rule]  \<tau>_trans_SKIP_SyncR} \qquad
    @{thm [mode = Axiom] tick_trans_SKIP_Sync_SKIP}
    \end{center}
*)


(*<*)
end

end
(*>*)


