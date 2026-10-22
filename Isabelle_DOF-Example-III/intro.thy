(*<*)
theory "intro"
  imports   "Isabelle_DOF.scholarly_paper"
            (* "Isabelle_DOF-Ontologies.document_templates" *)
            "HOL-CSP_OpSem.Conclusion"
            "front"
begin


declare_reference*[pre::background]
declare_reference*[smallSteps::technical]
declare_reference*[laws::technical]
declare_reference*[relatedwork::technical]
declare_reference*[variants::technical]
declare_reference*[holcspsemantics::technical]
declare_reference*[bigSteps::technical]

(*>*)
section*[introheader::introduction,main_author="Some(@{author ''bu''}::author)"]\<open> Introduction \<close> 
text*[introtext::introduction]\<open>
\<^noindent> Communicating Sequential Processes (CSP) is a language 
to specify and verify patterns of interaction of concurrent systems.
Together with CCS and LOTOS, it belongs to the family of \<^emph>\<open>process algebras\<close>. 
CSP's rich theory comprises denotational, operational and algebraic semantic facets 
and has influenced programming languages such as Limbo, Crystal, Clojure and
most notably Golang \<^cite>\<open>"donovan2015go"\<close>. CSP has been applied in 
industry as a tool for specifying and verifying the concurrent aspects of hardware 
systems, such as the T9000 transputer \<^cite>\<open>"Barret95"\<close>. 

The theory of CSP was first described in 1978 by Tony Hoare \<^cite>\<open>"Hoare:1985:CSP:3921"\<close>, 
but has since evolved substantially \<^cite>\<open>"BrookesHR84" and "brookes-roscoe85" and "roscoe:csp:1998"\<close>.
The denotational semantics of CSP is described by a fully abstract model of behaviour designed to 
be \<^emph>\<open>compositional\<close>:  a process \<open>P\<close> encompasses all possible behaviours, \<^ie> sets of \<open>traces\<close> annotated 
by additional information that allow to reason over
   \<^item> deadlocks (the resulting semantic domain is called \<^emph>\<open>failure semantics F\<close>)
   \<^item> and additionally livelocks (the \<^emph>\<open>failure-divergence semantics FD\<close>).

\<^noindent> Several attempts have been undertaken to formalize this fairly complex theory, notably 
 \<^cite>\<open>"Camilleri91" and "tej.ea:corrected:1997" and  "IsobeRoggenbach2010"
and "DBLP:journals/afp/Noce16" and "CSP-Agda"\<close>. The arguably (see @{technical (unchecked) relatedwork})
  most comprehensive one is \<^session>\<open>HOL-CSP\<close>  \<^cite>\<open>"tej.ea:corrected:1997" and "HOL-CSP-AFP" and "TahaWY20" 
   and "HOL-CSPM-AFP" and "HOL-CSP_OpSem-AFP"\<close>, which is
in several ways not only a formalization in a proof assistant, but a generalization of
the original setting:
   \<^item> \<^vs>\<open>-0.3cm\<close> the set of traces \<^typ>\<open>'\<alpha> trace\<close> is constructed over an arbitrary type \<^typ>\<open>'\<alpha>\<close> in \<^session>\<open>HOL\<close>, 
     paving the way for dense time, vector spaces, etc,
     \<^footnote>\<open>or even differential equations as in cyber-physical system models \<^cite>\<open>CrisafulliTW23\<close>\<close>,
   \<^item> more generally speaking, \<^session>\<open>HOL-CSP\<close> attempts to remove finiteness-restrictions, and
   \<^item> the semantic domain is encapsulated in the type \<^typ>\<open>'\<alpha> process\<close> belonging to the cpo type 
     class (see @{technical (unchecked) holcspsemantics}). Thus, process patterns 
     can be expressed and analyzed.

In this paper, we present the formal theory of the operational semantics of \<^session>\<open>HOL-CSP\<close> which
is consistent with the denotational one by construction. To this end, we proceed by defining
the operational transition operator \<open>P \<leadsto>\<^sub>e P’\<close> in terms of the \<open>After\<close> operator and the 
classical failure-divergence refinement. In the literature on process algebras like CSP 
(\<^cite>\<open>"Hoare:1985:CSP:3921" and "BrookesHR84" and "brookes-roscoe85" and "roscoe:csp:1998"\<close>) or
 Circus (\<^cite>\<open>"WoodcockC02" and "birthday000100OSZ23"\<close>), several versions of operational semantics 
have been presented, but a formal proof of equivalence for a substantial part
of the language has never been undertaken. Our proof architecture foresees an Isabelle locale 
(a parameterized theory) whose instances represent several of these versions, thus shedding
some light on their relationships. The operational rules for small-step and big-steps pave the way
for symbolic execution of processes and the combination of model-checking with theorem proving.

We proceed as follows: after an introduction to ``classic'' CSP and our extensions \<^session>\<open>HOL-CSP\<close>
and \<^session>\<open>HOL-CSPM\<close> as an Isabelle framework in @{background (unchecked) \<open>pre\<close>}, we present in 
@{technical (unchecked) \<open>smallSteps\<close>} the core construction of this paper,
the \<^emph>\<open>bridge\<close>-definition linking the denotational semantics to operational one(s), resulting
in the formally proven laws written in @{technical (unchecked) \<open>laws\<close>}. This is
generalized to big steps semantics in @{technical (unchecked) bigSteps} and possible variants
are discussed in @{technical (unchecked) variants}.
Note that \<^session>\<open>HOL-CSP\<close>\<^cite>\<open>"HOL-CSP-AFP"\<close>, \<^session>\<open>HOL-CSPM\<close>\<^cite>\<open>"HOL-CSPM-AFP"\<close> as well as the novel contribution  \<^verbatim>\<open>HOL-CSP_OpSem\<close> \<^cite>\<open>"HOL-CSP_OpSem-AFP"\<close> 
containing the proofs discussed here are published in the Archive of Formal Proofs AFP\<^footnote>\<open>For the developer 
version, see \<^url>\<open>https://gitlab.lisn.upsaclay.fr/burkhart.wolff/hol-csp2.0/\<close>.\<close>.  
\<close>


(*<*)
end
(*>*) 
