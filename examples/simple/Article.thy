(* << *)  
theory Article 
  imports "../../ontologies/scholarly_paper"
begin
(* >> *) 
  
open_monitor*[onto::article]  

text*[tit::title]{* Using The Isabelle Ontology Framework*} 
  
text*[stit::subtitle] \<open>Linking the Formal with the Informal\<close>
  
text*[auth1::author, affiliation="''Universit\\'e Paris-Sud''"]\<open>Burkhart Wolff\<close>
term "\<lparr>author.tag_attribute=undefined,affiliation=undefined\<rparr>"
  
ML{* !AnnoTextelemParser.SPY *}
definition HURX where "HURX = affiliation((undefined::author)\<lparr>affiliation:='' ''\<rparr>)"
thm HURX_def[simplified]
ML{* 
val x = @{code "HURX"}
*}
  
definition HORX where "HORX = affiliation(\<lparr>author.tag_attribute=0,affiliation=undefined\<rparr>\<lparr>affiliation:='' ''\<rparr>) "  
ML{* 
val x = @{code "HORX"}
*}
  
text*[abs::abstract, keyword_list="[]"] {* Isabelle/Isar is a system 
framework with many similarities to Eclipse; it is mostly known as part of 
Isabelle/HOL, an interactive theorem proving and code generation environment. 
Recently, an Document Ontology Framework has been developed as a plugin in 
Isabelle/Isar, allowing to do both conventional typesetting \emph{as well} 
as formal development. A particular asset is the possibility to control the links 
between the formal and informal aspects of a document
via (a novel use of) Isabelle's antiquotation mechanism. *}
  
section*[intro::introduction, comment="''This is a comment''"]{* Introduction *} 
text{* Lorem ipsum dolor sit amet, suspendisse non arcu malesuada mollis, nibh morbi, 
phasellus amet id massa nunc, pede suscipit repellendus, in ut tortor eleifend augue 
pretium consectetuer. Lectus accumsan velit ultrices, mauris amet, id elit aliquam aptent id, 
felis duis. Mattis molestie semper gravida in ullamcorper ut, id accumsan, fusce id 
sed nibh ut lorem integer, maecenas sed mi purus non nunc, morbi pretium tortor.*}

section*[bgrnd::text_section]{* Background: Isabelle and Isabelle_DOF *}  
text{* As mentioned in @{introduction \<open>intro\<close>} ... *} 

term "a + b = b + a"

(*
@{term ''a + b = b + a''}
@{typ ''a list''}
@{thm ''refl''}
@{thms ''[refl,sym]''}
*)    
    
update_instance*[bgrnd, main_author = "Some(''bu'')", formula="@{term ''a + b = b + a''}"] 

section*[ontomod::technical]{* Modeling Ontologies in Isabelle_DOF *} 
text{* Lorem ipsum dolor sit amet, suspendisse non arcu malesuada mollis, nibh morbi,*}
  
subsection*[scholar_onto::example]{* A Scholar Paper: Eating one's own dogfood. *}  
  
subsection*[mathex_onto::example]{* Math-Exercise *}  
  
section*[con::conclusion]{* Future Work: Monitoring Classes *}    
text{* Lorem ipsum dolor sit amet, suspendisse non arcu malesuada mollis, nibh morbi, ... *}

subsection*[related::related_work]{* Related Work *}
text{* 
\<bullet> @{bold  \<open>XML\<close>} and dtd's, 
\<bullet> OWL and Protege, 
\<bullet> LaTeX setups such as ... 
  @{url "https://pdi.fbk.eu/technologies/tex-owl-latex-style-syntax-authoring-owl-2-ontologies"} 
\<bullet> Structured Assurance Case Metamodel Specification. 
  @{url "https://www.omg.org/spec/SACM/1.0/About-SACM/"}} 
\<bullet> AADL Alisa, 
\<bullet> RATP Ovado
*}  
  
subsection{* Discussion *}  
text{* Lorem ipsum dolor sit amet, suspendisse non arcu malesuada mollis, nibh morbi, ... *}

close_monitor*[onto]  

(* << *)    
end
(* >> *)    
  
