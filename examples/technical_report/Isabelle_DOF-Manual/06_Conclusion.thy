(*<*)
theory "06_Conclusion"
  imports "05_IsaDofLaTeX"
begin
(*>*)

chapter*[conclusion::conclusion]\<open> Conclusion and Related Work\<close>    
text\<open> We have demonstrated the use of \isadof, a novel ontology modeling and enforcement
IDE deeply integrated into the Isabelle/Isar Framework. The two most distinguishing features are
\<^item> \isadof and its ontology language  are a strongly typed language that allows
  for referring (albeit not reasoning) to entities of Isabelle/HOL, most notably types, terms,
  and (formally proven) theorems, and
\<^item> \isadof is supported by the Isabelle/PIDE framework; thus, the advantages of an IDE for 
  text-exploration (which is the type of this link? To which text element does this link refer?
  Which are the syntactic alternatives here?) were available during editing
  instead of a post-hoc validation process.
\<close>

text\<open> Of course, a conventional batch-process  also exists which can be used
for the validation of large document bases in a conventional continuous build process.
This combination of formal and semi-informal elements, as well as a systematic enforcement
of the coherence to a document ontology of the latter, is, as we believe, novel and offers 
a unique potential for the semantic treatment of scientific texts and technical documentations. \<close>

text\<open>
To our knowledge, this is the first ontology-driven framework for editing mathematical and technical 
documents that focuses particularly on documents mixing formal and informal content---a type of 
documents that is very common in technical certification processes. We see mainly one area of 
related works: IDEs and text editors that support editing and checking of documents based on an 
ontology.  There is a large group of ontology editors (\eg, Prot{\'e}g{\'e}~@{cite "protege"},
Fluent Editor~@{cite "cognitum"}, NeOn~@{cite "neon"}, or OWLGrEd~@{cite "owlgred"}). With them, 
we share the support for defining ontologies as well as auto-completion when editing documents 
based on an ontology. While our ontology definitions are currently based on a textual definition, 
widely used ontology editors (\eg, OWLGrEd~@{cite "owlgred"}) also support graphical notations. 
This could be added to \isadof in the future. A unique feature of \isadof is the deep integration 
of formal and informal text parts. The only other work in this area we are aware of is 
rOntorium~@{cite "rontorium"}, a plugin for Prot{\'e}g{\'e} that integrates 
R~@{cite "adler:r:2010"} into an ontology environment. Here, the main motivation behind this
integration is to allow for statistically analyze ontological documents. Thus, this is 
complementary to our work. \<close>

text\<open> \isadof in its present form has a number of technical short-comings as well 
  as potentials not yet explored. On the long list of the short-comings is the 
  fact that strings inside HOL-terms do not support, for example, Unicode. 
  For the moment, \isadof is conceived as an 
  add-on for Isabelle/HOL; a much deeper integration of \isadof into Isabelle 
  could increase both performance and uniformity. Finally, different target 
  presentation (such as HTML) would be highly desirable in particular for the 
  math exam scenarios. And last but not least, it would be desirable that PIDE 
  itself is ``ontology-aware'' and can, for example, use meta-information
  to control read- and write accesses of \<^emph>\<open>parts\<close> of documents.
\<close>

(*<*) 
end
(*>*) 
  
