(*<*)
theory "01_Introduction"
  imports "00_Frontmatter"
begin
(*>*)

chapter*[intro::introduction]\<open> Introduction \<close>  
text*[introtext::introduction]\<open> 
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
evolution, where the \<^emph>\<open>coherence\<close> between the formal and the informal parts of the
content can be mechanically checked.

To avoid any misunderstanding: \isadof  is \<^emph>\<open>not a theory in HOL\<close>   
on ontologies and operations to track and trace links in texts,
it is an \<^emph>\<open>environment to write structured text\<close> which \<^emph>\<open>may contain\<close>  
Isabelle/HOL definitions and proofs like mathematical articles, tech-reports and
scientific papers---as the present one, which is written in \isadof 
itself. \isadof is a plugin into the Isabelle/Isar
framework in the style of~@{cite "wenzel.ea:building:2007"}.\<close>


text\<open>This manual adresses at three different types of users:
\<^enum> users that just want to edit a core document, be it for a paper or a technical report,
  using a given ontology,
\<^enum> users that want to develop ontologies and/or modify the generated PDF-presentations,
\<^enum> users that want to add text-elements or new features to \isadof.

This manual gives priority to the former two groups; users with an interest in \isadof implementation
might find complementary information in  @{cite "brucker.wolff19:isadof-design-impl:2019"}.

\<close>

(* declaring the forward references used in the subsequent section *)  
(*<*)
declare_reference*[bgrnd::text_section]
declare_reference*[isadof::text_section]
declare_reference*[casestudies::text_section]
declare_reference*[ontopide::text_section]
declare_reference*[conclusion::text_section]
(*>*)
text*[plan::introduction]\<open> The plan of the paper is follows: we start by introducing  the underlying 
Isabelle system (@{docitem_ref (unchecked) \<open>bgrnd\<close>}) followed guided tour or tutorial
adressing the needs of the first intended user group. 
It follows the chapter @{docitem_ref (unchecked) \<open>isadof\<close>} for the second user group 
with essentials of  \isadof and its ontology language (@{docitem_ref (unchecked) \<open>isadof\<close>}). 

XXX

It follows @{docitem_ref (unchecked) \<open>casestudies\<close>}, where we present three application
scenarios from the point of view of the ontology modeling. In @{docitem_ref (unchecked) \<open>ontopide\<close>}
we discuss the user-interaction generated from the ontological definitions.  Finally, we draw 
conclusions  and discuss related work in @{docitem_ref (unchecked) \<open>conclusion\<close>}. \<close>  

(*<*) 
end
(*>*) 
  
