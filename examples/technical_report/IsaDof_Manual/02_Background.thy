(*<*)
theory "02_Background"
  imports "01_Introduction"
begin
(*>*)

chapter*[bgrnd::text_section,main_author="Some(@{docitem ''adb''}::author)"]
        \<open> Background: The Isabelle System \<close>
text*[background::introduction]\<open>
While Isabelle is widely perceived as an interactive theorem prover
for HOL (Higher-order Logic)~@{cite "nipkow.ea:isabelle:2002"}, we
would like to emphasize the view that Isabelle is far more than that:
it is the \<^emph>\<open>Eclipse of Formal Methods Tools\<close>.  This refers to the
``\textsl{generic system framework of Isabelle/Isar underlying recent
  versions of Isabelle.  Among other things, Isar provides an
  infrastructure for Isabelle plug-ins, comprising extensible state
  components and extensible syntax that can be bound to ML
  programs. Thus, the Isabelle/Isar architecture may be understood as
  an extension and refinement of the traditional `LCF approach', with
  explicit infrastructure for building derivative
  \<^emph>\<open>systems\<close>.}''~@{cite "wenzel.ea:building:2007"} 

The current system framework offers moreover the following features:

\<^item> a build management grouping components into to pre-compiled sessions,
\<^item> a prover IDE (PIDE) framework~@{cite "wenzel:asynchronous:2014"} with various front-ends 
\<^item> documentation - and code generators,
\<^item> an extensible front-end language Isabelle/Isar, and,
\<^item> last but not least, an LCF style, generic theorem prover kernel as 
  the most prominent and deeply integrated system component.
\<close>  

figure*[architecture::figure,relative_width="100",src="''figures/isabelle-architecture''"]\<open> 
     The system architecture of Isabelle (left-hand side) and the 
     asynchronous communication between the Isabelle system and 
     the IDE (right-hand side). \<close>

text*[blug::introduction]\<open> The Isabelle system architecture shown in @{docitem_ref \<open>architecture\<close>}
 comes with many layers, with Standard ML (SML) at the bottom layer as implementation 
language. The architecture actually foresees a \<^emph>\<open>Nano-Kernel\<close> (our terminology) which 
resides in the SML structure \texttt{Context}. This structure provides a kind of container called 
\<^emph>\<open>context\<close> providing an identity, an ancestor-list as well as typed, user-defined state 
for components (plugins) such as \isadof. On top of the latter, the LCF-Kernel, tactics, 
automated proof procedures as well as specific support for higher specification constructs
were built. \<close>
    
text\<open> We would like to detail the documentation generation of the architecture,
which is based on literate specification commands such as \inlineisar+section+ \ldots, 
\inlineisar+subsection+ \ldots, \inlineisar+text+ \ldots, etc.
Thus, a user can add a simple text:
\begin{isar}
  text\<Open>This is a description.\<Close>
\end{isar}
These text-commands can be arbitrarily mixed with other commands stating definitions, proofs, code, etc.,
and will result in the corresponding output in generated \LaTeX{} or HTML documents. 
Now, \<^emph>\<open>inside\<close> the textual content, it is possible to embed a \<^emph>\<open>text-antiquotation\<close>:
\begin{isar}
  text\<Open>According to the reflexivity axiom \at{thm refl}, we obtain in \<Gamma> 
           for \at{term "fac 5"} the result \at{value "fac 5"}.\<Close>
\end{isar}
which is represented in the generated output by:
\begin{out}
  According to the reflexivity axiom $x = x$, we obtain in $\Gamma$ for $\operatorname{fac} 5$ the result $120$.
\end{out}
where \inlineisar+refl+ is actually the reference to the axiom of reflexivity in HOL. 
For the antiquotation \inlineisar+\at{value "fac 5"}+  we assume the usual definition for 
\inlineisar+fac+ in HOL.
\<close>

text*[anti]\<open> Thus, antiquotations can refer to formal content, can be type-checked before being 
displayed and can be used for calculations before actually being typeset. When editing, 
Isabelle's PIDE offers auto-completion and error-messages while typing the above 
\<^emph>\<open>semi-formal\<close> content.  \<close>


(*<*) 
end
(*>*) 
  
