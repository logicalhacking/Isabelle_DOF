chapter\<open>Inner Syntax Antiquotations (ISA)'s\<close>

theory 
  InnerSyntaxAntiquotations
imports 
  "../ontologies/Conceptual"
begin

text\<open>Since the syntax chosen for values of doc-class attributes is HOL-syntax --- requiring
a fast read on the ``What's in Main''-documentation, but not additional knowledge on, say, SML --- 
an own syntax for references to types, terms, theorems, etc. are necessary. These are the
``Inner Syntax Antiquotations'' since they make only sense \emph{inside} the Inner-Syntax
of Isabelle/Isar, so inside the \verb+" ... "+ parenthesis.

They are the key-mechanism to denote 
\<^item> Ontological Links, i.e. attributes refering to document classes defined by the ontology
\<^item> Ontological F-Links, i.e. attributes referring to formal entities inside Isabelle (such as thm's)

This file contains a number of examples resulting from the @{theory "Isabelle_DOF-tests.Conceptual"} - ontology;
the emphasis of this presentation is to present the expressivity of ODL on a paradigmatical example.
\<close>


text\<open>Voila the content of the Isabelle_DOF environment so far:\<close>
ML\<open> 
val {docobj_tab={tab = x, ...},docclass_tab, ISA_transformer_tab,...} = DOF_core.get_data @{context}; 
     Symtab.dest ISA_transformer_tab; 
\<close>

text\<open>Some sample lemma:\<close>
lemma murks : "Example=Example" by simp

text\<open>Example for a meta-attribute of ODL-type @{typ "file"} with an appropriate ISA for the
     file @{file "InnerSyntaxAntiquotations.thy"}\<close>
(* not working: 
text*[xcv::F, u="@{file ''InnerSyntaxAntiquotations.thy''}"]\<open>Lorem ipsum ...\<close>
*)

text*[xcv1::A, x=5]\<open>Lorem ipsum ...\<close>
text*[xcv3::A, x=7]\<open>Lorem ipsum ...\<close>

text\<open>Example for a meta-attribute of ODL-type @{typ "typ"} with an appropriate ISA for the
     theorem @{thm "refl"}}\<close>
text*[xcv2::C, g="@{thm ''HOL.refl''}"]\<open>Lorem ipsum ...\<close>

text\<open>Major sample: test-item of doc-class \verb+F+ with a relational link, and links to formal 
     Isabelle items. \<close>
text*[xcv4::F, r="[@{thm ''HOL.refl''}, 
                   @{thm ''InnerSyntaxAntiquotations.murks''}]", 
               b="{(@{docitem ''xcv1''},@{docitem ''xcv2''})}",  
               s="[@{typ ''int list''}]",
               property = "[@{term ''H --> H''}]"
]\<open>Lorem ipsum ...\<close>

text*[xcv5::G, g="@{thm ''HOL.sym''}"]\<open>Lorem ipsum ...\<close>

text\<open>... and here we add a relation between @{docitem \<open>xcv3\<close>} and @{docitem \<open>xcv2\<close>} 
into the relation \verb+b+ of @{docitem \<open>xcv5\<close>}. Note that in the link-relation,
a @{typ "C"}-type is required, but a  @{typ "G"}-type is offered which is leagal in
\verb+Isa_DOF+ because of the sub-class relation between those classes: \<close>
update_instance*[xcv4::F, b+="{(@{docitem ''xcv3''},@{docitem ''xcv5''})}"]

text\<open>And here is the result on term level:\<close>
ML\<open> @{docitem_attribute b::xcv4} \<close>

end
