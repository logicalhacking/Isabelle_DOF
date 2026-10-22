(*<*)
theory "conclusion"
  imports   "Isabelle_DOF.scholarly_paper"
            (* "Isabelle_DOF-Ontologies.document_templates" *)
            "HOL-CSP_OpSem.Conclusion"
            "ComparisonWithJifengHoare"
            "variants"
begin

(*>*)



(* text\<open>
We are interested in verification techniques for arbitrary event sets \<open>A\<close> or arbitrarily 
parameterized processes. Such processes can be used to model dense-timed processes, processes 
with dynamic thread creation, and processes with unbounded thread-local variables and buffers. 
However, this adds substantial complexity to the process theory: when it comes to study the 
interplay of different denotational models, refinement-orderings, and side-conditions for 
continuity, paper-and-pencil proofs easily reach their limits of precision. 

\<close> *)

(* see if we mention again Hoare and Jifeng *)
section*["relatedwork"::technical,main_author="Some(@{author ''ben''}::author)",level="Some 3"]
\<open>Related Work\<close>

(*<*) context OpSemTransitions begin (*>*)

text\<open>
\<^noindent> In the introduction, we claimed that HOL-CSP is arguably the most \<^emph>\<open>comprehensive\<close>
formalization of CSP; here, we'd like to substantiate this claim.

The theory of CSP has attracted a lot of interest since the eighties and nineties, both
as a theoretical device as well as a modelling language to analyze complex concurrent systems. 
A wealth of theoretical articles appeared to investigate certain fragments and extensions
of the core framework; it is therefore not surprising that attempts to their formalisations 
have been undertaken with the advent of interactive proof assistants.

Most noteworthy to these attempts is an early CSP trace semantics model in HOL System proposed 
by \<^cite>\<open>"Camilleri90"\<close>.  Its successor \<^cite>\<open>"Camilleri91"\<close> presented a first failure-divergence 
semantics for a restricted set of operators and used the notion of a universal (polymorphic) 
alphabet\<^footnote>\<open>Our first attempts for HOL-CSP \<^cite>\<open>"tej.ea:corrected:1997"\<close> are based on a extended 
version of this theory ported to Isabelle/HOL\<close>. Note that \<^cite>\<open>"tej.ea:corrected:1997"\<close> tackled 
already with subtle difficulties concerning \<^term>\<open>is_process\<close> and \<^term>\<open>\<checkmark>\<close>.

The tool CSP-Prover \<^cite>\<open>"DBLP:conf/concur/IsobeR06"\<close> --- based on a deep embedding of CSP in an 
Isabelle/HOL theory on the stable failures model ---  allows for the refinement 
verification~\<^cite>\<open>"DBLP:conf/concur/IsobeR06"\<close>  by using some automated support for induction. 
However, only if a process is divergence-free, its failures are the same as its stable failures. 
In our view, this is a too strong assumption for both a theory as well as a practical tool.

In the past few years, CSP benefited from a renewed interest with proof assistants.
CSP Agda was introduced in 2026 \<^cite>\<open>"CSP-Agda"\<close> with an implementation quite
different from \<^session>\<open>HOL-CSP\<close> since it is based on coinductive data types. Only trace and stable 
failures semantics have been covered so far, and the library of proven laws is fairly modest
\<^cite>\<open>"igried2017trace"\<close>. In 2020, an operational semantics of CSP in Coq was introduced
 \<^cite>\<open>"CSP-Coq"\<close> by a direct definitional approach. The theory covers only trace refinement and a 
subset of CSP's operators, but offers rather well-developed proof automation for this language 
fragment close to conventional automata theory.

With respect to all these formalizations in HOL, we would like to remind the importance of the 
general fact that invariants (like \<^term>\<open>is_process\<close>) or bridge theorems (like Hoare's
 \<^term>\<open>P \<leadsto>\<^bsub>e\<^esub> Q \<equiv> P \<sqsubseteq>\<^sub>F\<^sub>D (e \<rightarrow> Q) \<box> P \<close>) do not simply generalise from one fragment to the next, 
and that features which are well studied in one fragment are not necessarily
well-understood in the whole picture. It is our main contribution to provide an
integrated formal theory that tackles with the complexities of the necessary generalisations.
This involved a revision of the role of the @{const [source] \<open>After\<close>} operator in the entire theory.

In the late nineties, research focused on automated verification tools for CSP, most notably on
FDR (see \<^cite>\<open>"fdr4"\<close> for the latest instance). It relies on an operational CSP semantics, that 
allows for a conversion of processes into labelled transition systems, where the states were 
normalized by the ``axioms'' derived from the denotational semantics. 
For finite event sets, FDR can reduce refinement proofs to bisimulation problems. With 
efficient compression techniques, state-elimination and factorization by 
semantic equivalence \<^cite>\<open>"Roscoe95"\<close>, FDR was successful in analysing some industrial applications. 
However, such a model checker can never handle infinite cases. 
Another similar model checking tool \<^cite>\<open>"SunLDP09"\<close> implemented some more optimization techniques, 
such as partial order reduction, symmetric reduction, and parallel model checking, but is also 
restricted to the finite case. 
In a way, these tool require for their foundation  integrated denotational/algebraic/operational 
techniques as provided by our theory.

Attempts to find characterizations of processes to generalise finite results to infinite ones by
 \<^emph>\<open>data-independence\<close> \<^cite>\<open>"Lazic1998ASS" and "AnZhangYou14" and "DBLP:journals/jcs/RoscoeB99"\<close>, 
a variant of parametric model-checking, have seen only a limited success. Roscoe developed 
a data independent technology to verify security protocols modelled with CSP/FDR, which allows the 
node to call infinite fresh values for nonces, thus infinite sequence of operations 
\<^cite>\<open>"DBLP:journals/jcs/RoscoeB99"\<close>. An extension of this work was proposed in  \<^cite>\<open>"AnZhangYou14"\<close> 
using the script language \<open>CSP\<^sub>M\<close>. However, in their works, even though each agent in the security 
protocol can perform infinite number of operations,  the number of agent entities remains finite. 
HOL-CSP satisfies the need to parameterization and high-order processes naturally \<^cite>\<open>"ifm_TahaWY20"\<close> as a consequence of their \<^emph>\<open>pcpo\<close>-type structure. A formalization and theory 
development of \<open>CSP\<^sub>M\<close> has been undertaken \<^cite>\<open>"HOL-CSPM-AFP"\<close> but is out of the scope of this paper.
\<close>

(*<*) end (*>*)
section*["conclusion"::"conclusion",main_author="Some(@{author ''bu''}::author)"]
\<open>Conclusion\<close>
text\<open>\<^noindent> We presented a formalisation of a comprehensive semantic theory for CSP, a 'classical' 
language for the specification and analysis of concurrent systems studied in a rich body of 
literature. The theory comprises the denotational part (including recursion and permitting
higher-order processes), the algebraic part paving the way for parametric refinement proofs
involving fixed point induction, and the operational semantics part. The size of the 
latter, which constitutes an original contribution, is about 16 kLOC of Isabelle/HOL proofs.

The resulting framework offers new ways to reason consistently over denotationally defined
CSP processes paving the way to symbolic execution of LTS-based representations of processes
as well as the possibility to \<^emph>\<open>certify\<close> output from model-checkers like  \<^cite>\<open>"fdr4" and "SunLDP09"\<close>,
which excel in the calculational parts related to interleaving processes. As a by-product, the
theory allows for new proof principles like strong induction (cf. \<^theorem>\<open>strong_induct\<close>).

An interesting line of future work is the development of a library of ``process-bricks'' containing,
\<^eg>, semaphores, monitors or just global variables like:\<^vs>\<open>0.1cm\<close>

@{term [indent=5,margin=77,display, eta_contract = false] \<open>VAR Read Update \<equiv> \<mu> X. (\<lambda>\<sigma>. (Read\<^bold>!\<sigma> \<rightarrow> X \<sigma>) \<box> (Update\<^bold>?\<sigma>' \<rightarrow> X \<sigma>'))\<close>} \<^vs>\<open>-0.15cm\<close>

\<^noindent> or non-deterministic key-generators like:\<^vs>\<open>-0.2cm\<close>

@{term [indent=5,margin=77,display, eta_contract = false] \<open>KEY chan \<equiv> (\<mu> X. (\<lambda>\<sigma>. (chan\<^bold>!a\<in>\<sigma> \<rightarrow> X (\<sigma> - {a}))))\<nat>\<close>} \<^vs>\<open>-0.15cm\<close>

\<^noindent> which will have symbolic traces like:\<^vs>\<open>-0.2cm\<close>

@{term [indent=5,margin=77,display, eta_contract = false] \<open>a\<in>\<nat> \<Longrightarrow> b\<in>\<nat>-{a} \<Longrightarrow> c\<in>\<nat>-{a,b} \<Longrightarrow> [C a, C b, C c] \<in> \<T>(KEY C) \<close>} \<^vs>\<open>-0.15cm\<close>

\<^noindent> which can be derived both algebraically as well as operationally.\<^vs>\<open>-0.1cm\<close>
\<close>

(*<*)
subsection*[bib::bibliography]\<open>References\<close>

close_monitor*[this]

check_doc_global

end


(*>*) 
