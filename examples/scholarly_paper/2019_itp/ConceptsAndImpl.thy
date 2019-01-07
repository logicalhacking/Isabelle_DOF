(*<*)
theory ConceptsAndImpl
  imports "../../../ontologies/scholarly_paper"
begin

open_monitor*[this::article] 
 

(*>*)


declare[[strict_monitor_checking=false]]
title*[tit::title]\<open>A Document Ontology Framework in Isabelle\<close> 
subtitle*[stit::subtitle]\<open>Design and Implementation\<close>
text*[adb:: author,
      email="''a.brucker@sheffield.ac.uk''",
      orcid="''0000-0002-6355-1200''",
      affiliation="''The University of Sheffield, Sheffield, UK''"]\<open>Achim D. Brucker\<close>
text*[bu::author,
      email       = "''wolff@lri.fr''",
      affiliation = "''Universit\\'e Paris-Sud, Paris, France''"]\<open>Burkhart Wolff\<close>
    

text*[abs::abstract,
      keywordlist="[''Semantic Web'',''Document Ontology'',''Formal Document Development'',''Isabelle/DOF'']"]\<open>
  We present an extension of the Isabelle/Isar framework allowing both the 
  \<^emph>\<open>modeling\<close> of document ontologies as well as the their *\<open>enforcement\<close> inside theory documents
  by a smooth integration into Isabelle's IDE. The resulting extension \<^verbatim>\<open>Isa_DOF\<close> provides a
  strongly typed ontology definition language allowing to annotate a document element (or ``corpus'')
  with meta-information that is validated during document development and maintenance. 
  Ontology definitions provide \<^emph>\<open>concepts\<close>, \<^emph>\<open>is-a\<close> relations and \<^emph>\<open>links\<close> between them,
  as well as \<^emph>\<open>F-links\<close> from concepts to formal content such as types, terms and theorems. 

  Documents referring to an ontology are edited, validated and proof-checked within
  Isabelle/HOL. Particular emphasis is put on a deep integration
  into the Isabelle IDE to give immediate ontological feedback to the
  developer of documents containing entities such as text, models,
  formal proofs, and code. 
  The IDE animates \<^emph>\<open>links\<close> and \<^emph>\<open>F-links\<close> via hyper-references, and
  controls the document structure by checking a kind of behavioural specification.
 
  Sufficiently annotated, large documents are easier to be developed collaboratively 
  by continuously validating the \<^emph>\<open>coherence\<close> between formal and informal parts, and
  the impact of changes can be better tracked automatically.

\<close>

(*   Support of document ontologies is provided for immediate
  user-feedback when editing large documents with formal and
  semi-formal content, be it for mathematical articles, exercises, or,
  \eg, deliverables in a certified software engineering
  process.  *)


section*[intro::introduction]\<open> Introduction \<close> 
text*[introtext::introduction]\<open>

Given the body of formalized mathematics in 

, for example the Isabelle/AFP

One of the main use of ontologies is annotation. Let us consider a set of entities available in
a given corpus. These entities may be sentences or paragraphs in a document, figures, tables,
definitions or lemmas in a document, etc. By annotation, we denote the link that may exist between an ontology concept 
and a document element of the considered corpus.

The annotation process consists in defining and running a set of rules leading to the production of annotations.
This process may be completely automated, semi-automatic with user validation or completely 
interactive. 

IDEA: a table with conceptual properties 
Feature       | Ontolingua  | DAML+OIL | RDFS | OWL | PLIB | XML | Isa_ODL
------------------------------------------------------------------------
granularity   | Word        |          |      |     |      | Character    | sentence (word)
relationships |                                                  | sentence - concept, is_A, (class-class)
strong typing |                                                  | on attributes and classes
links         |                                                  | links , F-links
algebraic operators |                                            | sets, lists, relations, HOL.
Constraints   |                                                  | ML, executable HOL
CWA vs OWA    |                                                  | OWA
Context Modeling |                                               | Context import
Inheritance   | 
Instantiation |  
\<close>

text*[intro_old::introduction]\<open> 
The linking of the \<^emph>\<open>formal\<close> to the \<^emph>\<open>informal\<close> is perhaps the
most pervasive challenge in the digitization of knowledge and its
propagation. This challenge incites numerous research efforts
summarized under the labels ``semantic web'', ``data mining'', or any
form of advanced ``semantic'' text processing.  A key role in
structuring this linking play \<^emph>\<open>document ontologies\<close> (also called
\<^emph>\<open>vocabulary\<close> in the semantic web community~@{cite "w3c:ontologies:2015"}), 
\ie, a machine-readable form of the structure of documents as well as 
the document discourse.

Such ontologies can be used for the scientific discourse within scholarly
articles, mathematical libraries, and in the engineering discourse  
of standardized software certification 
documents~@{cite "boulanger:cenelec-50128:2015" and "cc:cc-part3:2006"}. 
Further applications are the domain-specific discourse in juridical texts or medical reports.  
In general, an ontology is a formal explicit description of \<^emph>\<open>concepts\<close> 
in a domain of discourse (called \<^emph>\<open>classes\<close>), properties of each concept 
describing \<^emph>\<open>attributes\<close> of the concept, as well as \<^emph>\<open>links\<close> between 
them. A particular link between concepts is the \<^emph>\<open>is-a\<close> relation declaring 
the instances of a subclass to be instances of the super-class.

The main objective of this paper is to present \isadof, a novel
framework to \<^emph>\<open>model\<close> typed ontologies and to \<^emph>\<open>enforce\<close> them during
document evolution. Based on Isabelle infrastructures, ontologies may refer to
types, terms, proven theorems, code, or established assertions.
Based on a novel adaption of the Isabelle IDE, a document is checked to be 
\<^emph>\<open>conform\<close> to a particular ontology---\isadof is designed to give fast user-feedback 
\<^emph>\<open>during the capture of content\<close>. This is particularly valuable in case of document 
changes, where the \<^emph>\<open>coherence\<close> between the formal and the informal parts of the
content can be mechanically checked.

To avoid any misunderstanding: \isadof  is \<^emph>\<open>not a theory in HOL\<close>   
on ontologies and operations to track and trace links in texts,
it is an \<^emph>\<open>environment to write structured text\<close> which \<^emph>\<open>may contain\<close>  
Isabelle/HOL definitions and proofs like mathematical articles, tech-reports and
scientific papers---as the present one, which is written in \isadof 
itself. \isadof is a plugin into the Isabelle/Isar
framework in the style of~@{cite "wenzel.ea:building:2007"}.
\<close>

(* declaring the forward references used in the subsequent section *)  
(*<*)
declare_reference*[bgrnd::text_section]
declare_reference*[isadof::text_section]
declare_reference*[ontomod::text_section]
declare_reference*[ontopide::text_section]
declare_reference*[conclusion::text_section]
(*>*)
text*[plan::introduction]\<open> The plan of the paper is follows: we start by introducing  the underlying 
Isabelel sytem (@{docitem (unchecked) \<open>bgrnd\<close>}) followed by presenting the 
essentials of  \isadof and its ontology language (@{docitem (unchecked) \<open>isadof\<close>}). 
It follows @{docitem (unchecked) \<open>ontomod\<close>}, where we present three application 
scenarios from the point of view of the ontology modeling. In @{docitem_ref (unchecked) \<open>ontopide\<close>}
we discuss the user-interaction generated from the ontological definitions.  Finally, we draw 
conclusions  and discuss related work in @{docitem_ref (unchecked) \<open>conclusion\<close>}. \<close>  

section*[bgrnd::text_section,main_author="Some(@{docitem ''adb''}::author)"]
        \<open> Background: The Isabelle System \<close>