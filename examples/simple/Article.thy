(* << *)  
theory Article 
  imports "../../ontologies/scholarly_paper"
begin
(* >> *) 
  
ML{*           val keywords = Thy_Header.get_keywords' @{context};
*}  
  
open_monitor*[onto::article]  

text*[tit::title]{* Using The Isabelle Ontology Framework*} 
  
text*[stit::subtitle] \<open>Linking the Formal with the Informal\<close>
  
text*[auth1::author, affiliation = "''University of Sheffield''"]\<open>Achim Brucker\<close>
  
text*[auth2::author, affiliation = "''Centrale-Supelec''"]       \<open>Idir Ait-Sadoune\<close>
text*[auth3::author, affiliation = "''IRT-SystemX''"]            \<open>Paolo Crisafulli\<close>
text*[auth4::author, affiliation="''Universit\\'e Paris-Sud''"]\<open>Burkhart Wolff\<close>  

term "affiliation_update (\<lambda> _ . '''') S"  
  
text*[abs::abstract, keywordlist="[]::string list"] {* Isabelle/Isar is a system 
framework with many similarities to Eclipse; it is mostly known as part of 
Isabelle/HOL, an interactive theorem proving and code generation environment. 
Recently, an Document Ontology Framework has been developed as a plugin in 
Isabelle/Isar, allowing to do both conventional typesetting \emph{as well} 
as formal development. A particular asset is the possibility to control the links 
between the formal and informal aspects of a document
via a modeling language for document ontologies and a (novel use of) 
Isabelle's antiquotation mechanism. *}
  
  
section*[intro::introduction, comment="''This is a comment''"]{* Introduction *} 
text{* Lorem ipsum dolor sit amet, suspendisse non arcu malesuada mollis, nibh morbi, 
phasellus amet id massa nunc, pede suscipit repellendus, in ut tortor eleifend augue 
pretium consectetuer. Lectus accumsan velit ultrices, mauris amet, id elit aliquam aptent id, 
felis duis. Mattis molestie semper gravida in ullamcorper ut, id accumsan, fusce id 
sed nibh ut lorem integer, maecenas sed mi purus non nunc, morbi pretium tortor.*}

section* [bgrnd :: introduction] {* Background: Isabelle and Isabelle_DOF *}  
text{* As mentioned in @{introduction \<open>intro\<close>} ... *} 

    
(*update_instance*[bgrnd, main_author = "Some(''bu'')", formula="@{term ''a + b = b + a''}"] *)
update_instance*[bgrnd, comment := "''bu''"] 

ML{* 
val term'' = @{docitem_value \<open>bgrnd\<close>};
val xxx = type_of term'';
val yyy = HOLogic.mk_Trueprop(Const(@{const_name "HOL.eq"}, xxx --> xxx --> HOLogic.boolT) 
                              $ term'' $ Free("XXXX", xxx));
val hhh = Thm.varifyT_global;
val zzz = Thm.assume(Thm.cterm_of @{context} yyy);
val zzzz = simplify @{context} zzz;
val a $ b $ c = @{term "X\<lparr>affiliation:='' ''\<rparr>"};
 *}  
  
term "scholarly_paper.author.affiliation_update"
term "scholarly_paper.abstract.keywordlist_update"
term "scholarly_paper.introduction.comment2_update"
ML{* val a $ b $ c = @{term "X\<lparr>affiliation:='' ''\<rparr>"}; fold;
*}
ML{* !AnnoTextelemParser.SPY;
fun convert((Const(s,_),_), t) X = Const(s^"_update", dummyT) 
                               $ Abs("uuu_", type_of t, t)
                               $ X
val base = @{term "undefined"}
val converts = fold convert (!AnnoTextelemParser.SPY) base
ML{*   open Thm; varifyT_global ; 
*}  
  



  
term "scholarly_paper.author.affiliation_update"
term "scholarly_paper.abstract.keyword_list_update"
term "scholarly_paper.introduction.comment_update"
  
term "\<lparr>author.tag_attribute=undefined,email=''dfg'',orcid='''',affiliation=undefined\<rparr>"
  
definition HORX 
  where "HORX = affiliation(\<lparr>author.tag_attribute=undefined,email=''dfg'',orcid=None,affiliation=undefined\<rparr>\<lparr>affiliation:=''e''\<rparr>) "  
(* ML{* 
val x = @{code "HORX"}
*}
*)  
  

section*[ontomod::technical]{* Modeling Ontologies in Isabelle_DOF *} 
text{* Lorem ipsum dolor sit amet, suspendisse non arcu malesuada mollis, nibh morbi,*}
  
text*[x]{* @{technical \<open>ontomod\<close>} @{introduction \<open>bgrnd\<close>}*}
  
subsection*[scholar_onto::example]{* A Scholar Paper: Eating one's own dogfood. @{technical \<open>ontomod\<close>} *}  
text{* @{technical \<open>ontomod\<close>}*}                                                
  
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
  
