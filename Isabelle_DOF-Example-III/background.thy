(*<*)
theory "background"
  imports   "Isabelle_DOF.scholarly_paper"
            (* "Isabelle_DOF-Ontologies.document_templates" *)
            "HOL-CSP_OpSem.Conclusion"
            "intro"
begin
(*>*)

section*["pre"::background,main_author="Some(@{author ''bu''}::author)"]\<open>Background\<close>
subsection\<open>Classic CSP Syntax\<close>
text\<open>
\<^noindent> At a glance, the syntax of the classical CSP core language reads as follows: \<^vs>\<open>-0.1cm\<close> 

   \<^descr>  \<^hs>\<open>0.7cm\<close> \<open> P ::= \<close> \<^term>\<open>SKIP\<close> | \<^term>\<open>STOP\<close> | \<^term>\<open>P\<box>P'\<close> | \<^term>\<open>P\<sqinter>P'\<close> | \<^term>\<open>P \<lbrakk>A\<rbrakk> P'\<close> | \<^term>\<open>P \<^bold>; P'\<close> | \<^term>\<open>P \ A\<close> 
   \<^descr>  \<^hs>\<open>1.45cm\<close> | \<^term>\<open>a\<rightarrow>P\<close> | @{term [source] \<open>\<box>a \<in> A \<rightarrow> P(a)\<close>} | @{term [source]\<open>\<sqinter>a \<in> A \<rightarrow> P(a)\<close>} | \<^term>\<open>Renaming P g\<close> | @{term [source] \<open>\<mu> X. f(X)\<close>} 

\<^vs>\<open>-0.1cm\<close> \<^noindent> \<^term>\<open>SKIP\<close> signals termination, \<^term>\<open>STOP\<close> denotes a deadlock.
Two choice operators are distinguished:
  \<^enum>  \<^vs>\<open>-0.3cm\<close> the \<^emph>\<open>external choice\<close> \<open>_\<box>_\<close>, which forces a process ``to follow'' whatever
    its context requires,
  \<^enum> the \<^emph>\<open>internal choice\<close> \<open>_\<sqinter>_\<close>, which imposes on the context of a process
    ``to follow'' the non-deterministic choices made. \<^vs>\<open>-0.2cm\<close>

\<^noindent> With the prefix operator \<^term>\<open>a\<rightarrow>P\<close> which signals \<^term>\<open>a\<close> and continues with \<^term>\<open>P\<close> (where \<open>a\<close> is an 
element of a set \<open>\<Sigma>\<close> of \<^emph>\<open>events\<close>), generalized choices of the form @{term [source] \<open>\<box>a\<in>A \<rightarrow> P(a)\<close>} 
resp. @{term [source]\<open>\<sqinter>a\<in>A \<rightarrow> P(a)\<close>} are constructed (\<^term>\<open>A\<close> is originally a finite set). When events 
are tagged with \<^emph>\<open>channels\<close>, \<^ie> \<^term>\<open>\<Sigma> = CHANNELS \<times> DATA\<close>, syntactic sugar like
 @{term [source]\<open>c\<^bold>?x\<in>A\<rightarrow>P(x)\<close>} or @{term [source]\<open>c\<^bold>!\<^bold>!x\<in>A\<rightarrow>P(x)\<close>} is added; the former reads 
intuitively as ``\<open>x\<close> is read from channel \<open>c\<close>'' while the latter means 
``\<open>x\<close> is arbitrarily chosen from \<open>A\<close> and sent into \<open>c\<close>''
(where \<^term>\<open>c\<in>CHANNELS\<close> and \<^term>\<open>x\<in>DATA\<close>).

The sequential composition \<^term>\<open>P \<^bold>; P'\<close> behaves first like \<^term>\<open>P\<close> and, once it has successfully terminated,
like \<^term>\<open>P'\<close>. \<^term>\<open>P \ A\<close> consists in hiding the events of the set \<^term>\<open>A\<close>.
\<^term>\<open>Renaming P g\<close> results in a process in which each event \<^term>\<open>e\<close> of \<^term>\<open>P\<close> is renamed in @{term [source] \<open>g(e)\<close>}.
The @{const [source] Sliding} operator \<^term>\<open>P \<rhd> P'\<close> is defined as @{thm (rhs) Sliding_def[of P P']}.
The fixed point @{term [source] \<open>\<mu> X. f(X)\<close>} operator satisfies @{term [source] \<open>(\<mu> X. f(X)) = f (\<mu> X. f(X))\<close>}
(but requires precautions, see @{technical (unchecked) holcspsemantics}). 

CSP describes all communication with one single primitive: the synchronized product written
\<^term>\<open>P\<lbrakk>A\<rbrakk>P'\<close>. Note that interleaving @{term [source] \<open>P ||| P'\<close>} stands for @{term [source]\<open>P \<lbrakk>{}\<rbrakk> P'\<close>}, 
whereas  the parallel operator @{term [source] \<open>P || P'\<close>} is a shortcut for @{term [source] \<open>P \<lbrakk>UNIV\<rbrakk> P'\<close>} 
(\<^const>\<open>UNIV\<close> is the universal set).
\<close>


subsection*[cspsemantics::technical, main_author="Some(@{author ''bu''})"]\<open>Classic CSP Semantics\<close>

text\<open>\<^noindent> The denotational semantics (following \<^cite>\<open>"roscoe:csp:1998"\<close>) comes in three layers: 
the \<^emph>\<open>trace model\<close>, the \<^emph>\<open>(stable) failures model\<close> and the \<^emph>\<open>failure-divergence model\<close>.

In the trace semantics model, the behaviour of a process \<open>P\<close> is denoted by a prefix-closed set of 
traces, denoted \<^term>\<open>\<T> P\<close>, similar to the well-known concept of a ``language of an automata''.
Since traces are finite lists and infinite behaviour is therefore represented via the set of approximations,
an additional element @{term [source] \<open>tick\<close>} (written \<^term>\<open>\<checkmark>\<close>) is used to represent explicit termination
signalized by \<^const>\<open>SKIP\<close>. Note that, obviously, @{term [source] \<open>tick\<close>} should only appear at the
end of a trace (traces should be @{term [source] \<open>front_tickFree\<close>}).

It is impossible to distinguish external and internal non-determinism in the trace model since
the traces of both operators are just the union of their argument traces. To be more discriminant,
\<^cite>\<open>"BrookesHR84"\<close> proposed the failure semantics model, where traces were annotated 
with a set of \<^emph>\<open>refusals\<close>, \<^ie> sets of events a process can \<^emph>\<open>not\<close> engage in. This leads to the
notion of a  \<^emph>\<open>failure\<close> \<^term>\<open>(t, X) \<in> \<F> P\<close> which is a pair of a trace \<open>t\<close> and a set of refusals \<open>X\<close>.
Consider for example the process \<^term>\<open>P = (a \<rightarrow> Skip) \<box> (a \<rightarrow> STOP)\<close>. The traces \<^term>\<open>\<T>(P)\<close> will 
non-deterministically lead to a situation where the process accepts termination (but refuses 
everything else) or just refuses everything. So, if we assume \<^term>\<open>\<Sigma> = {a,\<checkmark>}\<close>, then the traces 
\<^term>\<open>\<T>(P)\<close> will be \<^term>\<open>{[],[a]}\<close>. The failures \<^term>\<open>\<F>(P)\<close> are then \<^term>\<open>{([],{{\<checkmark>}}), ([a],{\<Sigma>,{a}})}\<close> 
(plus all subsets of the respective refusal sets, which is required for the recursion ordering 
discussed in @{technical (unchecked) holcspsemantics}).

Finally, \<^cite>\<open>"BrookesHR84"\<close> enriched the semantic domain of CSP with one more element,
the set of \<^emph>\<open>divergences\<close> (written \<^term>\<open>\<D> P\<close>), in order to distinguish deadlocks from
livelocks\<^footnote>\<open>also called \<^emph>\<open>infinite internal chatter\<close> as occurring in processes like \<^term>\<open>\<mu> X.(a \<rightarrow> X) \ {a}\<close>\<close>.
In the failure divergence model, the semantic domain consists of a pair of failures and divergences,
where the latter are traces to situations where livelocks may occur.

In contrast to Hoare Logics and its Hoare Triples, which is a framework to reason over 
terminating calculations, CSP and process refinement are designed to reason over 
non-terminating calculations. Three classic refinement notions are considered:
   \<^enum> \<^vs>\<open>-0.3cm\<close>the trace refinement: @{term [source] \<open>P \<sqsubseteq>\<^sub>T Q \<equiv> \<T> P \<supseteq> \<T> Q\<close>},
   \<^enum> the failure refinement: @{term [source] \<open>P \<sqsubseteq>\<^sub>F Q \<equiv> \<F> P \<supseteq> \<F> Q\<close>}, and
   \<^enum> the failure-divergence refinement @{term [source] \<open>P \<sqsubseteq>\<^sub>F\<^sub>D Q \<equiv> \<F> P \<supseteq> \<F> Q \<and> \<D> P \<supseteq> \<D> Q\<close>} \<^vs>\<open>-0.2cm\<close>.

\<^noindent> It turns out that beyond common protocol refinement proofs and test-problems, many properties such  
as deadlock or livelock freeness can be expressed via a refinement statement.
\<close>

subsection*["locales"::technical]\<open>Theories and Locales in Isabelle and HOL\<close>
text\<open>\<^noindent> Isabelle is a major interactive proof assistant implementing higher-order logic (HOL).
As an LCF style theorem prover, it is based on a small logical core (kernel) to increase the 
trustworthiness of proofs without requiring --- yet supporting --- explicit proof objects. 

The Isabelle distribution comes with a number of library theories constructed solely from
definitional axioms; among them basic data-types for sets, lists, arithmetics, a substantial part
of analysis, and --- particularly relevant here --- Scott domain theory (\<^session>\<open>HOLCF\<close>)
\<^cite>\<open>"muller.ea:holcf:1999"\<close> providing a particular type class \<open>'\<alpha>::pcpo\<close>, i.e. the class of
types \<^typ>\<open>'\<alpha>\<close> for which a least element \<^term>\<open>\<bottom>\<close> and a complete partial order \<open>_\<sqsubseteq>_\<close> is defined.

\<^session>\<open>HOLCF\<close> provides the concept of \<^emph>\<open>continuity\<close>, the concept of \<^emph>\<open>admissibility\<close>, the fixed 
point operator \<^term>\<open>\<mu> X. f X\<close> as well as the fixed point induction for admissible predicates.
Isabelle's type inference can automatically infer, for example, that if \<open>'\<alpha>::pcpo\<close>, 
then \<open>('\<beta> \<Rightarrow> '\<alpha>)::pcpo\<close>.

A distinguishing feature of Isabelle is the \<^theory_text>\<open>locale\<close> mechanism, \<^ie> theories that may be
parameterized by types, constant-symbols and local hypotheses over them. Since  \<^theory_text>\<open>locale\<close>s may 
inherit from other \<^theory_text>\<open>locale\<close>s, they represent a powerful structuring mechanism for orders and 
algebraic structures very similar to dependent types available in other systems. \<close>


subsection*[holcspsemantics::technical, main_author="Some(@{author ''bu''})"]\<open>Isabelle/HOL-CSP\<close>

text\<open>\<^noindent> \<^verbatim>\<open>Isabelle/HOL-CSP\<close> is a shallow embedding of CSP in HOL based on the traditional semantic 
domain described by 9 ``axioms'' over the three semantic functions
\<^term>\<open>\<T>\<close> :: \<^typ>\<open>'\<alpha> process \<Rightarrow> '\<alpha> trace set\<close>,
\<^term>\<open>\<F>\<close> :: \<^typ>\<open>'\<alpha> process \<Rightarrow> '\<alpha> failure set\<close> and \<^term>\<open>\<D>\<close> :: \<^typ>\<open>'\<alpha> process \<Rightarrow> '\<alpha> trace set\<close>:
   \<^item> \<^vs>\<open>-0.2cm\<close>the empty trace is always the initial trace and any trace is \<^const>\<open>front_tickFree\<close>; 
   \<^item> traces of a process are  \<^emph>\<open>prefix-closed\<close> and a process can refuse all subsets of refusals; 
   \<^item> any event refused by a process after a trace \<open>s\<close> must be in a refusal set associated to \<open>s\<close>;
   \<^item> the @{const [source] tick} accepted after a trace \<open>s\<close> implies that all other events are refused; 
   \<^item> a divergence trace with any suffix is itself a divergence one
   \<^item> once a process has diverged, it can engage in or refuse any sequence of events.
   \<^item> a @{const [source] tick}-ending divergence trace has a \<^const>\<open>tickFree\<close> divergence trace prefix 
     of  maximal length. \<^vs>\<open>-0.2cm\<close> 

\<^noindent> More formally, a process \<open>P\<close> of the type \<open>\<Sigma> process\<close> should have the following properties: \<^vs>\<open>-0.1cm\<close> 

@{cartouche [display,indent=5,margin=77]
\<open>([] \<in> \<T> P \<and> (\<forall>s X. (s, X) \<in> \<F> P \<longrightarrow> front_tickFree s) \<and>
 (\<forall>s t. s @ t \<in> \<T> P \<longrightarrow> s \<in> \<T> P) \<and> (\<forall>s X Y. (s, Y) \<in> \<F> P \<and> X \<subseteq> Y \<longrightarrow> (s, X) \<in> \<F> P) \<and>
 (\<forall>s X Y. (s, X) \<in> \<F> P \<and> (\<forall>c. c \<in> Y \<longrightarrow> s @ [c] \<notin> \<T> P) \<longrightarrow> (s, X \<union> Y) \<in> \<F> P) \<and>
 (\<forall>s X. s @ [\<checkmark>] \<in> \<T> P \<longrightarrow> (s, X - {\<checkmark>}) \<in> \<F> P) \<and>
 (\<forall>s t. s \<in> \<D> P \<and> tickFree s \<and> front_tickFree t \<longrightarrow> s @ t \<in> \<D> P) \<and>
 (\<forall>s X. s \<in> \<D> P \<longrightarrow> (s, X) \<in> \<F> P) \<and> (\<forall>s. s @ [\<checkmark>] \<in> \<D> P \<longrightarrow> s \<in> \<D> P))\<close>}

\<^vs>\<open>-0.1cm\<close> \<^noindent> The core of \<^session>\<open>HOL-CSP\<close> 
is to encapsulate this wishlist into a type definition. This is achieved by 
1) defining the pair of failures and divergences \<open>\<Sigma> process\<^sub>0\<close> via 
\<open>(\<Sigma>\<^sup>\<checkmark> list \<times> \<Sigma>\<^sup>\<checkmark> set) set \<times> (\<Sigma>\<^sup>\<checkmark> list) set\<close> (where \<open>\<Sigma>\<^sup>\<checkmark> = \<Sigma> \<uplus> {\<checkmark>}\<close>), 2) by turning the 
above  wishlist into a data-constraint \<^term>\<open>is_process\<close> of type \<open>\<Sigma> process\<^sub>0 \<Rightarrow> bool\<close>, and 3) 
by establishing an isomorphism between the subset of \<open>\<Sigma> process\<^sub>0\<close>'es satisfying \<open>is_process\<close> 
via the-specification construct: \<^vs>\<open>-0.1cm\<close>
  
  @{theory_text [display, indent=10, margin=70] \<open>typedef '\<alpha> process = "{P :: '\<alpha> process\<^sub>0 . is_process P}"\<close>}

\<^vs>\<open>-0.1cm\<close> \<^noindent> Subsequently, we provide definitions for each CSP operator in terms of
 \<open>\<Sigma> process\<^sub>0\<close>; these definitions formalize directly the textbook \<^cite>\<open>"roscoe:csp:1998"\<close>.  
Finally, we prove that each operator preserves the \<open>is_process\<close>-invariant. The preservation 
even holds for arbitrary (possibly infinite) sets \<open>A\<close> in the generalisations @{term [source] \<open>\<box>x\<in>A \<rightarrow> P(x)\<close>} 
resp. @{term [source] \<open>\<sqinter>x\<in>A \<rightarrow> P(x)\<close>}. Note that both use higher-order 
abstract syntax and have the type \<^typ>\<open>'\<alpha> set \<Rightarrow> ('\<alpha> \<Rightarrow> '\<alpha> process) \<Rightarrow> '\<alpha> process\<close>.

A major problem prevails: how to give semantics to the fixed point operator?

\<^noindent> This is achieved by turning the denotational domain of CSP into a Scott complete partial order (cpo)
\<^cite>\<open>"scott:cpo:1972"\<close>, which provides semantics for the fixed point operator
@{term [source] \<open>\<mu> x. f(x)\<close>} under the condition that \<^term>\<open>f\<close> is continuous wrt. this partial ordering.
Since the natural ordering \<open>_ \<sqsubseteq>\<^sub>F\<^sub>D _\<close> is too weak for this purpose,
Roscoe and Brookes \<^cite>\<open>Roscoe1992AnAO\<close> proposed a complete
\<^emph>\<open>process ordering\<close> \<open>P \<sqsubseteq> Q\<close> which is stronger, \<^ie> \<open>P \<sqsubseteq> Q \<Longrightarrow> P \<sqsubseteq>\<^sub>F\<^sub>D Q\<close>,
and yet ensures completeness at least for general read and write operations. 

\<^noindent> It is based on the concept \<^emph>\<open>refusals after\<close> a trace \<open>s\<close>
(@{thm [eta_contract = false] Refusals_after_def[no_vars]}):
 \<^hs>\<open>0.6cm\<close> @{thm [display] le_approx_def[no_vars]}\<close>

text\<open> \<^vs>\<open>-0.5cm\<close>\<close>

Theorem*[T0::"theorem", short_name="\<open>Continuity\<close>"]\<open>Almost all HOL-CSP operators \<open>\<otimes>\<close> are continuous wrt. \<^term>\<open>(\<sqsubseteq>)\<close>, \<^ie>:
   @{cartouche [indent=5,margin=75,display] \<open>cont f \<Longrightarrow> cont g \<Longrightarrow> cont(\<lambda>x. (f x) \<otimes> (g x))\<close>}
 \<close>

(* text\<open> \<^vs>\<open>-0.7cm\<close>\<close>
 *)

Theorem*[T1::"theorem", short_name="\<open>Fixed-point Inductions\<close>"] \<open>Since \<^term>\<open>(\<sqsubseteq>\<^sub>F\<^sub>D)\<close> is admissible,
when \<^term>\<open>f\<close> is continuous we have an induction rule of the following form:
   @{term [source, indent=5,margin=75,display] 
       \<open>C (\<bottom>) \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> (\<And>x. C (x) \<sqsubseteq>\<^sub>F\<^sub>D Q \<Longrightarrow> C(f x) \<sqsubseteq>\<^sub>F\<^sub>D Q)  \<Longrightarrow> C (\<mu> X. f X) \<sqsubseteq>\<^sub>F\<^sub>D Q \<close>}\<close>

text\<open> \<^vs>\<open>-0.5cm\<close>\<close>

(* this should be rewritten with term (or event better: thm), \<open>\<^bold>?\<close> is sometimes written \<open>?\<close>, ... *)
Proposition*[T2::"proposition", short_name="\<open>CSP-Algebra\<close>"] \<open>
HOL-CSP provides about 200 rules derived from the denotational semantics, be it monotonicities or
equalities, which were called the ``axioms'' in the literature. We show here only the 
small collection used in the subsequent example proof:
  @{cartouche [indent= 5,margin=75,display] 
    \<open>    (\<forall>y. c y \<in> S) \<Longrightarrow> c\<^bold>?x \<rightarrow> P x \<lbrakk>S\<rbrakk> c\<^bold>?x \<rightarrow> Q x = c\<^bold>?x \<rightarrow> (P x \<lbrakk>S\<rbrakk> Q x)
    (\<forall>y. c y \<in> S) \<Longrightarrow> inj c \<Longrightarrow> c\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> c\<^bold>?x \<rightarrow> Q x = c\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> Q a)
     d a \<notin> S \<Longrightarrow> (\<And>y. c y \<in> S) \<Longrightarrow> d\<^bold>!a \<rightarrow> P \<lbrakk>S\<rbrakk> c\<^bold>?x \<rightarrow> Q x = d\<^bold>!a \<rightarrow> (P \<lbrakk>S\<rbrakk> c\<^bold>?x \<rightarrow> Q x)
     d \<in> S \<Longrightarrow> (\<And>y. c y \<notin> S) \<Longrightarrow> d \<rightarrow> P \<lbrakk>S\<rbrakk> c\<^bold>?x \<rightarrow> Q x= c\<^bold>?x \<rightarrow> (d \<rightarrow> P \<lbrakk>S\<rbrakk> Q x)
     d a \<notin> C \<Longrightarrow> c \<in> C \<Longrightarrow> c \<rightarrow> Q \<lbrakk>C\<rbrakk> d\<^bold>!a \<rightarrow> P = d\<^bold>!a \<rightarrow> (c \<rightarrow> Q \<lbrakk>C\<rbrakk> P)
     \<forall>y. c y \<notin> B \<Longrightarrow>  c\<^bold>?x \<rightarrow> P x \ B = c\<^bold>?x \<rightarrow> (P x \ B)
     \<forall>y. c y \<notin> B \<Longrightarrow> c\<^bold>!a \<rightarrow> P \ B = c\<^bold>!a \<rightarrow> (P \ B)
     c a \<in> B \<Longrightarrow> c\<^bold>!a \<rightarrow> P \ B = P \ B                                  etc.\<close>}
\<close>
text\<open> \<^vs>\<open>-0.6cm\<close>\<close>
text\<open> The theories \<^session>\<open>HOL-CSP\<close> and \<^session>\<open>HOL-CSPM\<close> \<^cite>\<open>"HOL-CSPM-AFP"\<close> also add a number 
of extensions of the original language. This includes for the binary operators \<^term>\<open>P \<lbrakk>A\<rbrakk> P'\<close>,
 \<^term>\<open>P \<^bold>; P'\<close>,  \<^term>\<open>P \<box> P'\<close>,  \<^term>\<open>P \<sqinter> P'\<close>, the generalizations  @{term [source] \<open>\<^bold>\<lbrakk>S\<^bold>\<rbrakk>i \<in># M. P(i)\<close>},
@{term [source]\<open>\<^bold>|\<^bold>|\<^bold>| i \<in># M. P(i)\<close>}, etc. Roscoe's operators @{const [source] Interrupt} \<^term>\<open>P \<triangle> P'\<close> and 
\<^const>\<open>Throw\<close>  (exception handler) @{term [source] \<open>P \<Theta> a \<in> A. P'(a)\<close>} have also been included
since they come in handy in some of the more general constructions. Finally, \<^cite>\<open>TahaWY20\<close> 
proposed another refinement ordering, the trace-divergence ordering 
@{term [source] \<open>P \<sqsubseteq>\<^sub>D\<^sub>T Q \<equiv>  P \<sqsubseteq>\<^sub>T Q \<and> \<D> Q \<subseteq> \<D> P\<close>}, which has surprisingly benign properties wrt. 
operational semantics and which is relevant for applications \<^cite>\<open>CrisafulliTW23\<close>.\<close>

subsection*["proofs"::technical]\<open>A Model and Sample Proof in HOL-CSP\<close>
(*<*)
datatype '\<alpha> channel = left '\<alpha> | right '\<alpha> | mid '\<alpha> | ack
definition SYN  :: "('\<alpha> channel) set"
where     "SYN  \<equiv> (range mid) \<union> {ack}"

definition COPY :: "('\<alpha> channel) process"
where     "COPY \<equiv> (\<mu> COPY. left\<^bold>?x \<rightarrow> (right\<^bold>!x \<rightarrow> COPY))"

definition SEND :: "('a channel) process"
where     "SEND \<equiv> (\<mu> SEND. left\<^bold>?x \<rightarrow> (mid\<^bold>!x \<rightarrow>( ack \<rightarrow> SEND)))"
definition REC  :: "('a channel) process"
where     "REC  \<equiv> (\<mu> REC. mid\<^bold>?x \<rightarrow> (right\<^bold>!x \<rightarrow> (ack \<rightarrow> REC)))"
definition SYS where \<open>SYS \<equiv> (SEND \<lbrakk> SYN \<rbrakk> REC) \ SYN\<close>
(*>*)
text\<open>Of course, proving refinements is not done by unfolding the definitions in the
denotational semantics. Instead, the predominant proof technique is merely fixed point induction via
 @{theorem \<open>T1\<close>}, application of the algebraic rules of @{proposition \<open>T2\<close>} as well as 
the monotonicity rules which are a consequence of @{theorem \<open>T0\<close>}. We demonstrate this with the
paradigmatic \<^verbatim>\<open>CopyBuffer\<close> example, where we model a protocol \<^term>\<open>COPY\<close> (``received data on channel
 \<^term>\<open>left\<close> will eventually be copied into channel  \<^term>\<open>right\<close>'') and an implementing \<^term>\<open>SYS\<close> 
which transfers the data from some  \<^term>\<open>SEND\<close>-component into some \<^term>\<open>REC\<close>-component using
an internal channel \<^term>\<open>mid\<close> where \<^term>\<open>REC\<close> acknowledges each data-package via a signal on the
internal \<^term>\<open>ack\<close>-channel.\<close>


text\<open>The formalisation of these model-elements proceeds as follows. The events were defined by 
the inductive data-type introducing the channels: \<^vs>\<open>-0.1cm\<close>

@{theory_text[indent= 10,margin=75,display] \<open>datatype '\<alpha> channel = left '\<alpha> | right '\<alpha> | mid '\<alpha> | ack\<close>}

\<^vs>\<open>-0.1cm\<close> \<^noindent> Note that this definition leaves open what data is actually transmitted. A 
synchronisation set  \<^term>\<open>SYN:: ('\<alpha> channel) set\<close> is defined via \<^term>\<open>{e. \<exists>x. e=mid x} \<union> {ack}\<close>. The
 process \<^term>\<open>COPY\<close> of type \<^typ>\<open>('\<alpha> channel) process\<close> is defined by
 \<^term>\<open>\<mu> COPY. left\<^bold>?x \<rightarrow> (right\<^bold>!x \<rightarrow> COPY)\<close>, the process \<^term>\<open>SEND\<close> by
 \<^term>\<open>\<mu> SEND. left\<^bold>?x \<rightarrow> (mid\<^bold>!x \<rightarrow>( ack \<rightarrow> SEND))\<close> and the process \<^term>\<open>REC\<close> by
 \<^term>\<open>\<mu> REC. mid\<^bold>?x \<rightarrow> (right\<^bold>!x \<rightarrow> (ack \<rightarrow> REC))\<close>. The latter two are wired together
 to the process \<^term>\<open>SYS\<close> via \<^term>\<open>SYS \<equiv> (SEND \<lbrakk> SYN \<rbrakk> REC) \ SYN\<close>.

Now we ask the question: \<^emph>\<open>does\<close> \<^term>\<open>SYS\<close> \<^emph>\<open>implement the\<close> \<^emph>\<open>protocol\<close> \<^term>\<open>COPY\<close>? This can be
rewritten as the following refinement problem : \<^term>\<open>COPY \<sqsubseteq>\<^sub>F\<^sub>D SYS\<close>.

 \<^noindent> Unfolding \<^term>\<open>COPY\<close> and applying @{theorem T1} yields the two subgoals:
   \<^enum> \<^vs>\<open>-0.3cm\<close> \<^term>\<open> \<bottom> \<sqsubseteq>\<^sub>F\<^sub>D (SEND\<lbrakk>SYN\<rbrakk>REC \ SYN)\<close>
   \<^enum> @{term [indent=0,margin=77,display] 
     \<open>\<And>x. x \<sqsubseteq>\<^sub>F\<^sub>D (SEND\<lbrakk>SYN\<rbrakk>REC \ SYN)
                \<Longrightarrow> left\<^bold>?a \<rightarrow> (right\<^bold>!a \<rightarrow> x) \<sqsubseteq>\<^sub>F\<^sub>D ((SEND \<lbrakk>SYN\<rbrakk> REC) \ SYN)\<close>} \<^vs>\<open>-0.2cm\<close>

\<^noindent> where the former is trivial and the latter represents the induction step. If we unfold once
\<^term>\<open>SEND\<close> and \<^term>\<open>REC\<close> and apply the reduction rules of @{proposition T2}, this results in:  \<^vs>\<open>-0.1cm\<close>

@{term [indent=5,margin=77,display] 
       \<open>left\<^bold>?a \<rightarrow> (right\<^bold>!a \<rightarrow> x) \<sqsubseteq>\<^sub>F\<^sub>D left\<^bold>?a \<rightarrow> (right\<^bold>!a \<rightarrow> ((SEND \<lbrakk>SYN\<rbrakk> REC) \ SYN))\<close>}

\<^vs>\<open>-0.1cm\<close> \<^noindent>  Applying the monotonicity rules resulting from @{theorem T0} we can reduce this goal to the
induction hypothesis \<^term>\<open>x \<sqsubseteq>\<^sub>F\<^sub>D (SEND\<lbrakk>SYN\<rbrakk>REC \ SYN)\<close>.

Furthermore this proof can be highly automated (reduces to a few lines in Isabelle/Isar).
No assumption is made over \<^typ>\<open>'\<alpha>\<close>, this construction is therefore truly
parametric over data, which is in stark contrast to model-checkers for CSP such as 
\<^cite>\<open>"fdr4" and "SunLDP09"\<close>. Using the fact that functions over processes are continuous, we can 
specify and analyse, \<^eg>, global variables by @{term [indent=5,margin=77, eta_contract = false] 
    \<open>VAR \<sigma>\<^sub>i\<^sub>n\<^sub>i\<^sub>t \<equiv> (\<mu> X.(\<lambda>\<sigma>. (Read\<^bold>!\<sigma> \<rightarrow> X \<sigma>) \<box> (Update\<^bold>?\<sigma>' \<rightarrow> X \<sigma>')))\<sigma>\<^sub>i\<^sub>n\<^sub>i\<^sub>t\<close>}
and other building blocks of concurrent programs like buffers, semaphores and monitors.\<close>

(*<*)
end
(*>*) 
