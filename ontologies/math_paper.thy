chapter \<open>The Document Ontology Common Library for the Isabelle Ontology Framework\<close>

text\<open> Offering support for common Isabelle Elements like definitions, lemma- and theorem
statements, proofs, etc. Isabelle is a lot of things, but it is an interactive theorem
proving environment after all ! So this ontology provides:
\<^item> declarations for textual descriptions of definitions, lemmas, theorems, assertions, ...
  and the usual means for typed referencing on them,
\<^item> monitors allowing for filtering content; this means (typed) brackets that can be 
  put around formal content that is more or less relevant for different types of users,  
  \fixme{find nicer formulation}
\<^item> LaTeX support. \<close> 
  
  
theory math_paper
  imports  "../Isa_DOF"  
begin
  
   
section\<open>Some attempt to model standardized links to Standard Isabelle Formal Content\<close>

text\<open> These document classes are intended to present a number of key-elements
in mathematical papers and generate LaTeX in the style of, for example:
\begin{verbatim}
\begin{definition}[Dilating function]
A dilating function for a run \(\rho'\) is a function \(\mathbb{N} \longrightarrow \mathbb{N}\)
that satisfies:
\begin{enumerate}
  \item \(f\) is strictly monotonic, so that the order of the instants in not changed in \(\rho'\);
  \item \(\forall n.~f(n) \geq n\), so that instants are inserted into \(\rho\);
  \item \(f(0) = 0\), so that no instant is inserted before the first one;
  \item \(\forall n.~(\not\exists n_0.~f(n_0) = n) \Longrightarrow 
  			 (\forall c.~\neg\mathsf{ticks}(\rho'_{n}(c))\), 
  			 there is no tick in stuttering instants;
  \item \(\forall n.~(\not\exists n_0.~f(n_0) = n+1) \Longrightarrow 
  			 (\forall c.~\mathsf{time}(\rho'_{n+1}(c)) = \mathsf{time}(\rho'_{n}(c)))\), 
  			 time does not elapse during stuttering instants;
\end{enumerate}
\end{definition}
\end{verbatim}
which are intended to \<^emph>\<open>complement\<close> Isabelle's formal content elements such as definitions, 
lemmas and formal proofs.

We are aware that there is a certain tension between the interest to have more formal checking in
a definition as the above one and the interest in a notationally more liberal presentation that hides
technical details imposed by strict formality (even at the price that a chosen notation may be 
intuitive, but an abstraction that is, fi donc, technically incorrect). 

We argue that it should be up to the user to decide in each individual case how to draw this line ... \<close>

doc_class formal_stmt = 
    property :: "term list"

datatype relevance = key | vital | working | auxilliary | alternative  

doc_class "definition" = formal_stmt +
    relevance :: "relevance option"
    property :: "term list" <= "[]"

text\<open>Which gives rise to a presentation like:\<close>
(*<*) 
type_notation nat ("\<nat>")
(*>*)
text*[dil_fun :: "definition"]\<open>A dilating function for a run @{term "\<rho>"} is a function 
@{typ "\<nat> \<Rightarrow> \<nat>"} that satisfies:
\<^enum> @{term "f"} is strictly monotonic ...
\<^enum> ...
\<^enum> ...
\<close>


doc_class assertion = formal_stmt +
    relevance :: "relevance option"
    property  :: "term list" <= "[]"

doc_class "lemma" = formal_stmt +
    relevance :: "relevance"
    property  :: "term list" <= "[]"

doc_class "theorem" = formal_stmt +
    relevance :: "relevance"
    property  :: "term list" <= "[]"


doc_class "corrollary" = formal_stmt +
    relevance :: "relevance"
    property  :: "term list" <= "[]"

text\<open>This monitor is used to group formal content in a way to classify the
relevance. On the presentation level, this gives the possibility to adapt or omit
Isabelle/Isar lemma and theorem commands according to their relevance level.
By using inheritance, the document class @{text \<open>formal_content\<close>} can also be used
to introduce organisational information (for example: developer or tester or validator )
as a systematic means to produce documents oriented to specific needs of user (sub-)groups.\<close>

doc_class formal_content =
    relevance :: "relevance"
    accepts "\<lbrace>definition || assertion || lemma || theorem || corrollary \<rbrace>\<^sup>+"





end
