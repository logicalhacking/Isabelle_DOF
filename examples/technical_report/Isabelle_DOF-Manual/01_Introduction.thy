(*<*)
theory "01_Introduction"
  imports "00_Frontmatter"
begin
(*>*)

chapter*[intro::introduction]\<open> Introduction \<close>  
text*[introtext::introduction]\<open> 
The linking of the \<^emph>\<open>formal\<close> to the \<^emph>\<open>informal\<close> is perhaps the most pervasive challenge in the
digitization of knowledge and its propagation. This challenge incites numerous research efforts
summarized under the labels ``semantic web,'' ``data mining,'' or any form of advanced ``semantic''
text processing.  A key role in structuring this linking play \<^emph>\<open>document ontologies\<close> (also called
\<^emph>\<open>vocabulary\<close> in the semantic web community~@{cite "w3c:ontologies:2015"}),  \ie, a machine-readable
form of the structure of documents as well as the document discourse.

Such ontologies can be used for the scientific discourse within scholarly articles, mathematical 
libraries, and in the engineering discourse of standardized software certification 
documents~@{cite "boulanger:cenelec-50128:2015" and "cc:cc-part3:2006"}: certification documents 
have to follow a structure.  In practice, large groups of developers have to produce a substantial
set of documents where the consistency is notoriously difficult to maintain. In particular, 
certifications are centered around the \emph{traceability} of requirements throughout the entire 
set of documents. While technical solutions for the traceability problem exists (most notably:
DOORS~\cite{doors}), they are weak in the treatment of formal entities (such as formulas and their 
logical contexts).

Further applications are the domain-specific discourse in juridical texts or medical reports.  
In general, an ontology is a formal explicit description of \<^emph>\<open>concepts\<close> in a domain of discourse
(called \<^emph>\<open>classes\<close>), properties of each concept describing \<^emph>\<open>attributes\<close> of the concept, as well 
as \<^emph>\<open>links\<close> between them. A particular link between concepts is the \<^emph>\<open>is-a\<close> relation declaring 
the instances of a subclass to be instances of the super-class.

\isadof is a novel framework, extending of Isabelle/HOL, to \<^emph>\<open>model\<close> typed ontologies and to 
\<^emph>\<open>enforce\<close> them during document evolution. Based on Isabelle infrastructures, ontologies may refer
to types, terms, proven theorems, code, or established assertions. Based on a novel adaption of the 
Isabelle IDE, a document is checked to be \<^emph>\<open>conform\<close> to a particular ontology---\isadof is designed 
to give fast user-feedback \<^emph>\<open>during the capture of content\<close>. This is particularly valuable in case 
of document evolution, where the \<^emph>\<open>coherence\<close> between the formal and the informal parts of the
content can be mechanically checked.

To avoid any misunderstanding: \isadof  is \<^emph>\<open>not a theory in HOL\<close> on ontologies and operations to 
track and trace links in texts, it is an \<^emph>\<open>environment to write structured text\<close> which 
\<^emph>\<open>may contain\<close> Isabelle/HOL definitions and proofs like mathematical articles, tech-reports and
scientific papers---as the present one, which is written in \isadof itself. \isadof is a plugin 
into the Isabelle/Isar framework in the style of~@{cite "wenzel.ea:building:2007"}.\<close>

subsubsection\<open>How to Read This Manual\<close>
(*<*)
declare_reference*[background::text_section]
declare_reference*[isadof_tour::text_section]
declare_reference*[isadof_ontologies::text_section]
declare_reference*[isadof_developers::text_section]
(*>*)
text\<open>
This manual can be read in different ways, depending on what you want to accomplish. We see three
different main user groups: 
\<^enum> \<^emph>\<open>\isadof users\<close>, \ie, users that just want to edit a core document, be it for a paper or a 
  technical report, using a given ontology. These users should focus on 
  @{docitem_ref (unchecked) \<open>isadof_tour\<close>} and, depending on their knowledge of Isabelle/HOL, also
  @{docitem_ref (unchecked) \<open>background\<close>}. 
\<^enum> \<^emph>\<open>Ontology developers\<close>, \ie,  users that want to develop new ontologies or modify existing 
  document ontologies. These users should, after having gained a acquaintance as a user, focus 
  on @{docitem_ref (unchecked) \<open>isadof_ontologies\<close>}. 
\<^enum> \<^emph>\<open>\isadof developers\<close>, \ie, users that want to extend or modify \isadof, \eg, by adding new 
  text-elements. These users should read @{docitem_ref (unchecked) \<open>isadof_developers\<close>}
\<close>

subsubsection\<open>Typographical Conventions\<close>
text\<open>
  We acknowledge that understanding \isadof and its implementation in all details requires
  to separate multiple technological layers or languages. To help the reader with this, we 
  will type-set the different languages in different styles. In particular, we will use 
  \<^item> a light-blue background for input written in Isabelle's Isar language, \eg:
    \begin{isar}
    lemma refl: "x = x" 
      by simp
    \end{isar}
  \<^item> For small examples of generated document, we use a green background:
    \begin{out}
    The axiom refl
    \end{out}
  \<^item> For (S)ML-code, we use a red background:
    \begin{sml}
    fun id x = x
    \end{sml}
  \<^item> \LaTeX-code, we use a yellow background:
    \begin{ltx}
    \newcommand{\refl}{$x = x$}
    \end{ltx}
  \<^item> For shell scripts and interative shell sessions, we use a grey background:
    \begin{bash}
    achim@logicalhacking:~/Isabelle_DOF$ ls
    CHANGELOG.md  CITATION  examples  install  LICENSE  README.md  ROOTS  src
   \end{bash}

\<close>

(*<*) 
end
(*>*) 
  
