(*<*)
theory
  "C3_DocumentStructure"
imports  
  "C2_Basics"
begin

declare_reference*[lex::technical]
define_macro* it \<rightleftharpoons> \<open>\textit{\<close> _ \<open>}\<close>

(*>*)

chapter*[doc::text_section,level= "Some 0" ]\<open>Document's Structure\<close>

section*[typstr::technical]\<open>General Ideas\<close>
text\<open>When using \<^isadof>, it is vital to note the use of antiquotations. Antiquotations are a "semantic macro"
or a machine-checked comment. It has two commonly used syntactic forms:
  \<^item> a long one :
\<^isarbox>\<open>
\begin{isabelle}
\ {\isacharat}{\kern0pt}\isakeywordONE{{\isacharbraceleft}{\kern0pt}}antiquotation{\isacharunderscore}
{\kern0pt}name\ {\isacharparenleft}{\kern0pt}args{\isacharparenright}{\kern0pt}\ {\isacharbrackleft}
{\kern0pt}more{\isacharunderscore}{\kern0pt}args{\isacharbrackright}{\kern0pt}\ {\isacartoucheopen}
sub{\isacharminus}{\kern0pt}context{\isacartoucheclose}\ \isakeywordONE{{\isacharbraceright}{\kern0pt}}
\end{isabelle}
\<close>
  \<^item> a short one : 
\<^isarbox>\<open>
\textbf{ \textit{antiquotation} } <sub\_context> 
\<close>

The short form allows a single cartouche argument, improving readability, but it's not always ideal
—hence, both forms remain used.

\<^isadof> provides its own set of antiquotations to simplify the process of writing documents.
Some of these  help define our document's structure (\<^eg> chapter, paragraph), some are document
related elements (\<^eg> author, title,...) and finally, there is a whole set of antiquotations that facilitate
the presentation of scholarly elements (\<^eg> Definition, Theorem, Hypothesis, Example). @{technical (unchecked) lex}
compiles a list of all antiquotations contained in the \<^isadof> lexicon.
\<close>

paragraph\<open>Common Isabelle Antiquotations and Options\<close>
text\<open>Here are some commonly used antiquoations and options:
  \<^item> \<^verbatim>\<open>@{term t}\<close>: prints a well-typed term t 
  \<^item> \<^verbatim>\<open>@{typeof t}\<close>: prints the type of a well-typed term t
  \<^item> \<^verbatim>\<open>@{theory A}\<close>: prints the session-checked theory named A 
  \<^item> \<^verbatim>\<open>@{prop f}\<close>: prints a well-typed proposition f
  \<^item> \<^verbatim>\<open>@{value t}\<close>: evaluates a term t and prints its result
  \<^item> \<^verbatim>\<open>@{typ a}\<close>: prints a well-formed type a


Options allow you to be more precise with the printed output of antiquotations.
  \<^item> \<^verbatim>\<open>source=bool\<close>: prints the original source text of the antiquotations argument rather than it's 
internal representation 
  \<^item> \<^verbatim>\<open>names_short=bool\<close>: forces names of types and constants to be printed unqualified
  \<^item> \<^verbatim>\<open>names_long=bool\<close>: forces names of types and constants to be printed in their fully qualified form
  \<^item> \<^verbatim>\<open>display=bool\<close>: if true the text will be printed in "display mode". Similarly to \<^LaTeX>, this mode
includes line breaks and centering, which the default printing doesn't do.
Now this is a list of options which will affect how you want something to be displayed:
  \<^item> \<^verbatim>\<open>cartouche=bool\<close>: if true the output is delimited by cartouches
  \<^item> \<^verbatim>\<open>quotes=bool\<close>: if true the output is delimited by double quotes


You may check the fourth chapter of the Isabelle/Isar Reference Manual \<^cite>\<open>"mwenzel:isaref:2025"\<close>,
 which has more exhaustive list of antiquotations and options, and goes into more depth explaining the
subtleties of antiquotations.
\<close>


paragraph\<open>Level\<close>
text\<open>What is important to note is that all the \<^isadof> antiquotations are assigned a \<^emph>\<open>level\<close> of depth,
 very similarly to \<^LaTeX>. Here a level is of type \<^emph>\<open>int option\<close>.
So for structure elements of our document we follow much of \<^LaTeX> use:
  \<^item> A title or subtitle would be of level None
  \<^item> A chapter of level Some 0
  \<^item> A section of level Some 1
  \<^item> A subsection of level Some 2
  \<^item> ....

All scholarly antiquotations have to be above or equal to a level Some 1.
These can also be manually changed, although a few antiquotations have restrictionsdue to invariants
 when it comes to what levels they may be.
\<close>
section*[lex::technical]\<open>Lexical Conventions\<close>
text\<open>This manual main objective is to help to correctly use \<^isadof> to it's full potential when writing
papers and documents. As such, here is a quick overview of what antiquotations are defined in \<^isadof>.
These are not detailed explanations on how each of these antiquotations work but allows you an overview
on each of their utilities. Certain antiquotations have more of a developmental use to them so those 
will not be included within this section (\<^eg> \<^verbatim>\<open>doc_class\<close>, \<^verbatim>\<open>onto_class\<close>, \<^verbatim>\<open>onto_morphism\<close>,).
\<close>
subsection\<open>Antiquotation generated by the scholarly\_paper ontology\<close>
text\<open>In this section of our manual we will look into the different antiquotations generated by 
scholarly\_paper. These are all free-form math content, with a default level of Some 2. They also all
 have a 'referentiable' attribute that is true. 

Most of the definitions found in the table below came from the scholarly\_paper ontology file.

\<close>
text\<open>
\begin{tabular}{|p{0.25\textwidth}|p{0.75\textwidth}|}
\hline
\textbf{Antiquotation Name} & \textbf{Description}\\
\hline\hline
\<^verbatim>\<open>Definition*\<close> & A defintion gives a precise meaning to a new term  \\
\hline
\<^verbatim>\<open>Theorem*\<close> & A theorem is a "non evident" proposition \\
\hline
\<^verbatim>\<open>Proposition*\<close> & A proposition is also called a "sentence", is often characterized as the primary bearer of truth and
falsity, \ie a True or False statement  \\
\hline
\<^verbatim>\<open>Lemma*\<close> & A lemma is a generally minor, proven proposition which is used as 
a stepping stone to a larger result.  \\
\hline
\<^verbatim>\<open>Premise*\<close> & A premise is a proposition used in an argument to prove the truth of another
 proposition called the conclusion. \\
\hline
\<^verbatim>\<open>Corollary*\<close> & A corollary is a theorem of less importance which can be readily deduced from a previous, 
more notable lemma or theorem.\\
\hline
\<^verbatim>\<open>Consequence*\<close> & A consequence describes the relationship between statements that hold true when one statement 
logically follows from one or more statements. A valid logical argument is one in which the 
conclusion is entailed by the premises, because the conclusion is the consequence of the premises. \\
\hline
\<^verbatim>\<open>Conclusion*\<close> & A conclusion is a consequence of the premise \\
\hline
\<^verbatim>\<open>Assumption*\<close> & An assumption is an explicit or a tacit proposition about the world or a background belief 
relating to an proposition. \\
\hline
\<^verbatim>\<open>Hypothesis*\<close> &A working hypothesis is a provisionally accepted hypothesis proposed for further research
 in a process beginning with an educated guess or thought.  \\
\hline
\<^verbatim>\<open>Assertion*\<close> & An assertion is a statement that asserts that a certain premise is true. \\
\hline
\<^verbatim>\<open>Proof*\<close> & Proof statement is a deductive argument, that shows the assumptions logically entail the
conclusion \\
\hline
\<^verbatim>\<open>Example*\<close> & An example statement illustrates a point\\
\hline
\end{tabular}
\<close>
subsection\<open>Document Structure Antiquotations\<close>
text\<open>
\begin{tabular}{|l|l|}
\hline
\textbf{Antiquotation} & \textbf{Default Level} \\
\hline\hline
\<^verbatim>\<open>chapter*\<close> & Some 0 \\
\hline
\<^verbatim>\<open>section*\<close> & Some 1 \\
\hline
\<^verbatim>\<open>subsection*\<close> & Some 2 \\
\hline
\<^verbatim>\<open>subsubsection*\<close> & Some 3 \\
\hline
\<^verbatim>\<open>paragraph*\<close> & Some 4 \\
\hline
\end{tabular}
\<close>
subsection\<open>Document Elements Antiquotations\<close>
text\<open>
\resizebox{\textwidth}{!}{
\begin{tabular}{|p{0.21\textwidth}|p{0.3\textwidth}|p{0.35\textwidth}|p{0.2\textwidth}|}
\hline
\textbf{Antiquotation} & \textbf{Description} & \textbf{Attributes} & \textbf{Cartouche content} \\
\hline\hline
\<^verbatim>\<open>author*\<close> & Allows you to define one or more author to the document & \begin{itemize} 
                                                                        \item email (\<^it>\<open>string\<close>), default ""
                                                                        \item http\_site (\<^it>\<open>string\<close>), default ""
                                                                        \item orcid (\<^it>\<open>string\<close>), default ""
                                                                        \item affiliation (\<^it>\<open>string\<close>)
                                                                        \end{itemize} 
                                                                      & author's name \\
\hline
\<^verbatim>\<open>title*\<close> & Main title of the document & \begin{itemize}
                                         \item short\_title (\<^it>\<open>string option\<close>), default "None"
                                         \end{itemize}
                                        & title \\
\hline
\<^verbatim>\<open>subtitle*\<close> & Subtitle of the document & \begin{itemize}
                                         \item abbrev (\<^it>\<open>string option\<close>), default "None"
                                         \end{itemize}
                                        & subtitle \\
\hline
\<^verbatim>\<open>abstract*\<close> & Quick overview of the content of the paper before the index  & \begin{itemize}
                                                                              \item keywordlist (\<^it>\<open>string list\<close>), default []
                                                                              \item principal\_theorems (\<^it>\<open>thm list\<close>)
                                                                              \end{itemize}
                                                                            & content of the abstract \\
\hline
\<^verbatim>\<open>figure*\<close> & Allows you to add images in your document (more in @{technical fig}) & \begin{itemize} 
                                                                                    \item kind (\<^it>\<open>float\_kind\<close>), default graphics
                                                                                    \item file\_src (\<^it>\<open>string\<close>)
                                                                                    \item relative\_width (\<^it>\<open>int\<close>)
                                                                                    \item relative\_height (\<^it>\<open>int\<close>)
                                                                                    \end{itemize} 
                                                                                  \textbf{invariant} : all figures.kind = graphics
                                                                                  & figure's caption \\
\hline
\<^verbatim>\<open>frame*\<close> & Allows you to make presentations (example in the add-on) & \begin{itemize}
                                                                       \item options (\<^it>\<open>string\<close>)
                                                                       \item frametitle (\<^it>\<open>string\<close>)
                                                                       \item framesubtitle (\<^it>\<open>string\<close>)
                                                                       \end{itemize}
                                                                     & content of the frame \\
\hline
\end{tabular}}
\<close>
(*<*)
end
(*>*)