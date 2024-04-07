(*************************************************************************
 * Copyright (C) 
 *               2019-2022 University of Exeter 
 *               2018-2022 University of Paris-Saclay
 *               2018      The University of Sheffield
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

(*<*)
theory 
  "M_05_Proofs_Ontologies"
  imports 
    "M_04_Document_Ontology" 
  keywords "onto_morphism"  :: thy_decl
  and      "to"
begin

(*>*)

chapter*[onto_proofs::technical]\<open>Proofs on Ontologies\<close>

text\<open>It is a distinguishing feature of \<^dof> that it does not directly generate meta-data rather
than generating a \<^emph>\<open>theory of meta-data\<close> that can be used in HOL-terms on various levels
of the Isabelle-system and its document generation technology. Meta-data theories can be 
converted into executable code and efficiently used in validations, but also used for theoretic
reasoning over given ontologies. While the full potential of this latter possibility still
needs to be explored, we present in the following sections two applications:

  \<^enum> Verified ontological morphisms, also called \<^emph>\<open>ontological mappings\<close> in the literature
    \<^cite>\<open>"books/daglib/0032976" and "atl" and "BGPP95"\<close>, \<^ie> proofs of invariant preservation
    along translations of \<^verbatim>\<open>doc_class\<close>-instances.
  \<^enum> Verified refinement relations between the structural descriptions of theory documents,
    \<^ie> proofs of language inclusions of monitors of global ontology classes.   
\<close>

section*["morphisms"::scholarly_paper.text_section] \<open>Proving Properties over Ontologies\<close>

subsection\<open>Proving the Preservation of Ontological Mappings : A Document-Ontology Morphism\<close>

text\<open>\<^dof> as a system is currently particularly geared towards \<^emph>\<open>document\<close>-ontologies, in 
particular for documentations generated from Isabelle theories. We used it meanwhile for the
generation of various conference and journal papers, notably using the
 \<^theory>\<open>Isabelle_DOF.scholarly_paper\<close> and  \<^theory>\<open>Isabelle_DOF.technical_report\<close>-ontologies, 
targeting a (small) variety of \<^LaTeX> style-files. A particular aspect of these ontologies,
especially when targeting journals from publishers such as ACM, Springer or Elsevier, is the
description of publication meta-data. Publishers tend to have their own styles on what kind 
meta-data should be associated with a journal publication; thus, the depth and 
precise format of affiliations, institution, their relation to authors, and author descriptions
(with photos or without, hair left-combed or right-combed, etcpp...)  varies.

In the following, we present an attempt to generalized ontology with several ontology mappings 
to more specialized ones such as concrete journals and/or the  \<^theory>\<open>Isabelle_DOF.scholarly_paper\<close>-
ontology which we mostly used for our own publications. 
\<close>

doc_class "title"  = short_title :: "string option" <= "None"

(*doc_class '\<alpha> affiliation =
  journal_style :: '\<alpha>
*)

doc_class elsevier =
  organization :: string
  address_line :: string
  postcode :: int
  city :: string
  
(*doc_class elsevier_affiliation = affiliation +*) 

doc_class acm =
  position :: string
  institution :: string
  department :: int
  street_address :: string
  city :: string
  state :: int
  country :: string
  postcode :: int

(*doc_class acm_affiliation = affiliation +*)

doc_class lncs =
  institution :: string

(*doc_class lncs_affiliation = affiliation +*)


doc_class author =
    firstname   :: string
    surname     :: string
    email       :: "string"   <= "''''"
    invariant ne_fsnames :: "firstname \<sigma> \<noteq> '''' \<and> surname \<sigma> \<noteq> ''''"

doc_class elsevier_author = "author" +
  affiliations :: "elsevier list"
  short_author :: string
  url :: string
  footnote :: string

text*[el1:: "elsevier"]\<open>\<close>
(*text*[el_aff1:: "affiliation", journal_style = "@{elsevier \<open>el1\<close>}"]\<open>\<close>*)
term*\<open>@{elsevier \<open>el1\<close>}\<close>
text*[el_auth1:: "elsevier_author", affiliations = "[@{elsevier \<open>el1\<close>}]"]\<open>\<close>

doc_class acm_author = "author" +
  affiliations :: "acm list"
  orcid :: int
  footnote :: string

text*[acm1:: "acm"]\<open>\<close>
(*text*[acm_aff1:: "acm affiliation", journal_style = "@{acm \<open>acm1\<close>}"]\<open>\<close>*)
text*[acm_auth1:: "acm_author", affiliations = "[@{acm \<open>acm1\<close>}]"]\<open>\<close>

doc_class lncs_author = "author" +
  affiliations :: "lncs list"
  orcid :: int
  short_author :: string
  footnote :: string

text*[lncs1:: "lncs"]\<open>\<close>
(*text*[lncs_aff1:: "lncs affiliation", journal_style = "@{lncs \<open>lncs1\<close>}"]\<open>\<close>*)
text*[lncs_auth1:: "lncs_author", affiliations = "[@{lncs \<open>lncs1\<close>}]"]\<open>\<close>


doc_class  "text_element" =
    authored_by :: "author set"  <= "{}"
    level       :: "int  option"  <= "None"
    invariant authors_req :: "authored_by \<sigma> \<noteq> {}" 
    and       level_req   :: "the (level \<sigma>) > 1"

doc_class "introduction" = "text_element" +
    authored_by :: "(author) set"  <= "UNIV"

doc_class  "technical" = "text_element" +
    formal_results  :: "thm list"

doc_class "definition" = "technical" +
    is_formal   :: "bool"

doc_class "theorem" = "technical" +
    is_formal   :: "bool"
    assumptions :: "term list"        <= "[]"
    statement   :: "term option"      <= "None"

doc_class "conclusion" = "text_element" +
    resumee     :: "(definition set \<times> theorem set)"
    invariant is_form :: "(\<exists>x\<in>(fst (resumee \<sigma>)). definition.is_formal x) \<longrightarrow> 
                  (\<exists>y\<in>(snd (resumee \<sigma>)). is_formal y)"

text*[def::"definition", is_formal = "True"]\<open>\<close>
text*[theo::"theorem", is_formal = "False"]\<open>\<close>
text*[conc::"conclusion", resumee="({@{definition \<open>def\<close>}}, {@{theorem \<open>theo\<close>}})"]\<open>\<close>

value*\<open>resumee @{conclusion \<open>conc\<close>} |> fst\<close>
value*\<open>resumee @{conclusion \<open>conc\<close>} |> snd\<close>

doc_class "article" =
    style_id    :: string   <= "''LNCS''"
    accepts "(title ~~ \<lbrace>author\<rbrace>\<^sup>+ ~~ \<lbrace>introduction\<rbrace>\<^sup>+  
             ~~ \<lbrace>\<lbrace>definition ~~ example\<rbrace>\<^sup>+ || theorem\<rbrace>\<^sup>+ ~~ \<lbrace>conclusion\<rbrace>\<^sup>+)"


definition elsevier_to_acm_morphism :: "elsevier \<Rightarrow> M_04_Document_Ontology.acm"
          ("_ \<langle>acm\<rangle>\<^sub>e\<^sub>l\<^sub>s\<^sub>e\<^sub>v\<^sub>i\<^sub>e\<^sub>r" [1000]999)
          where "\<sigma> \<langle>acm\<rangle>\<^sub>e\<^sub>l\<^sub>s\<^sub>e\<^sub>v\<^sub>i\<^sub>e\<^sub>r = 
                                   \<lparr> M_04_Document_Ontology.acm.tag_attribute = 1::int,
                                     M_04_Document_Ontology.acm.position = ''no position'',
                                     M_04_Document_Ontology.acm.institution = organization \<sigma>,
                                     M_04_Document_Ontology.acm.department = 0,
                                     M_04_Document_Ontology.acm.street_address = address_line \<sigma>,
                                     M_04_Document_Ontology.acm.city = elsevier.city \<sigma>,
                                     M_04_Document_Ontology.acm.state = 0,
                                     M_04_Document_Ontology.acm.country = ''no country'',
                                     M_04_Document_Ontology.acm.postcode = elsevier.postcode \<sigma>  \<rparr>"

(*definition elsevier_aff_to_acm_aff_morphism :: "elsevier affiliation \<Rightarrow> Introduction.acm Introduction.affiliation"
          ("_ \<langle>acm'_aff\<rangle>\<^sub>e\<^sub>l\<^sub>s\<^sub>e\<^sub>v\<^sub>i\<^sub>e\<^sub>r'_\<^sub>a\<^sub>f\<^sub>f" [1000]999)
          where "\<sigma> \<langle>acm_aff\<rangle>\<^sub>e\<^sub>l\<^sub>s\<^sub>e\<^sub>v\<^sub>i\<^sub>e\<^sub>r_\<^sub>a\<^sub>f\<^sub>f = 
                                   \<lparr> Introduction.affiliation.tag_attribute = 1::int,
                                     Introduction.affiliation.journal_style = (affiliation.journal_style \<sigma>)
                                                                              |> (\<lambda>x. x \<langle>acm\<rangle>\<^sub>e\<^sub>l\<^sub>s\<^sub>e\<^sub>v\<^sub>i\<^sub>e\<^sub>r) \<rparr>"*)

definition acm_name where "acm_name f s = f @ '' '' @ s"

definition elsevier_author_to_acm_author_morphism :: "elsevier_author \<Rightarrow> M_04_Document_Ontology.acm_author"
          ("_ \<langle>acm'_auth\<rangle>\<^sub>e\<^sub>l\<^sub>s\<^sub>e\<^sub>v\<^sub>i\<^sub>e\<^sub>r'_\<^sub>a\<^sub>u\<^sub>t\<^sub>h" [1000]999)
          where "\<sigma> \<langle>acm_auth\<rangle>\<^sub>e\<^sub>l\<^sub>s\<^sub>e\<^sub>v\<^sub>i\<^sub>e\<^sub>r_\<^sub>a\<^sub>u\<^sub>t\<^sub>h = 
                                   \<lparr> M_04_Document_Ontology.author.tag_attribute = 1::int,
                                     M_04_Document_Ontology.author.name = acm_name (firstname \<sigma>) (surname \<sigma>),
                                     M_04_Document_Ontology.author.email = author.email \<sigma>,
                                     M_04_Document_Ontology.acm_author.affiliations = (elsevier_author.affiliations \<sigma>)
                                                                        |> map (\<lambda>x. x \<langle>acm\<rangle>\<^sub>e\<^sub>l\<^sub>s\<^sub>e\<^sub>v\<^sub>i\<^sub>e\<^sub>r) ,
                                     
                                     M_04_Document_Ontology.acm_author.orcid = 0,
                                     M_04_Document_Ontology.acm_author.footnote = elsevier_author.footnote \<sigma>  \<rparr>"


lemma elsevier_inv_preserved :
  "ne_fsnames_inv \<sigma> \<Longrightarrow> M_04_Document_Ontology.ne_name_inv (\<sigma> \<langle>acm_auth\<rangle>\<^sub>e\<^sub>l\<^sub>s\<^sub>e\<^sub>v\<^sub>i\<^sub>e\<^sub>r_\<^sub>a\<^sub>u\<^sub>t\<^sub>h)"
  unfolding ne_fsnames_inv_def M_04_Document_Ontology.ne_name_inv_def
            elsevier_author_to_acm_author_morphism_def
  by (simp add: combinator1_def acm_name_def)

lemma elsevier_author_to_acm_author_morphism_total :
  "elsevier_author_to_acm_author_morphism ` ({X::elsevier_author. ne_fsnames_inv X}) \<subseteq> ({X::M_04_Document_Ontology.acm_author. M_04_Document_Ontology.ne_name_inv X})"
  using elsevier_inv_preserved
  by auto

ML\<open>
fun add_onto_morphism classes_mappings eqs thy =
  if (length classes_mappings = length eqs) then
    let 
      val specs = map (fn x => (Binding.empty_atts, x)) eqs
      val converts =
        map (fn (oclasses, dclass) =>
               let
                 val oclasses_string = map YXML.content_of oclasses
                 val dclass_string = YXML.content_of dclass
                 val const_sub_name = dclass_string
                                      |> (oclasses_string |> fold_rev (fn x => fn y => x ^ "_" ^ y))
                                      |> String.explode |> map (fn x => "\<^sub>" ^ (String.str x)) |> String.concat
                 val convert_typ = oclasses_string |> rev |> hd
                                    |> (oclasses_string |> rev |> tl |> fold (fn x => fn y => x ^ " \<times> " ^ y))
                 val convert_typ' = convert_typ ^ " \<Rightarrow> " ^ dclass_string
                 val oclasses_sub_string = oclasses_string
                                          |> map (fn x => x |> String.explode |> map (fn y => "\<^sub>" ^ (String.str y)) |> String.concat)
                 val mixfix = oclasses_sub_string |> rev |> hd
                               |> (oclasses_sub_string |> rev |> tl |> fold (fn x => fn y => x ^ "\<^sub>\<times>" ^ y))
                 val mixfix' = "convert" ^ mixfix ^ "\<^sub>\<Rightarrow>"
                                ^ (dclass_string |> String.explode
                                   |> map (fn x => "\<^sub>" ^ (String.str x)) |> String.concat)
               in SOME (Binding.name ("convert" ^ const_sub_name), SOME convert_typ', Mixfix.mixfix mixfix') end)
            classes_mappings
      val args = map (fn (x, y) => (x, y, [], [])) (converts ~~ specs)
      val lthy = Named_Target.theory_init thy
      val updated_lthy = fold (fn (decl, spec, prems, params) => fn lthy => 
                        let
                          val (_, lthy') = Specification.definition_cmd decl params prems spec true lthy
                        in lthy' end) args lthy
    in Local_Theory.exit_global updated_lthy end
    (* alternative way to update the theory using the Theory.join_theory function *)
      (*val lthys = map (fn (decl, spec, prems, params) => 
                        let
                          val (_, lthy') = Specification.definition_cmd decl params prems spec true lthy
                        in lthy' end) args
      val thys = map (Local_Theory.exit_global) lthys

    in Theory.join_theory thys end*)
  else error("The number of morphisms declarations does not match the number of definitions")

fun add_onto_morphism' (classes_mappings, eqs) = add_onto_morphism classes_mappings eqs

val parse_onto_morphism = Parse.and_list
                            ((Parse.$$$ "(" |-- Parse.enum1 "," Parse.typ --| Parse.$$$ ")" --| \<^keyword>\<open>to\<close>)
                              -- Parse.typ)
                          --  (\<^keyword>\<open>where\<close> |-- Parse.and_list Parse.prop)

(* The name of the definitions must follow this rule:
   for the declaration "onto_morphism (AA, BB) to CC",
   the name of the constant must be "convert\<^sub>A\<^sub>A\<^sub>\<times>\<^sub>B\<^sub>B\<^sub>\<Rightarrow>\<^sub>C\<^sub>C".
   See the examples below.
   *)
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>onto_morphism\<close> "define ontology morpism"
                       (parse_onto_morphism >> (Toplevel.theory o add_onto_morphism'));

\<close>

find_consts name:"convert"

doc_class AA =
aa :: int
doc_class BB =
bb :: int
doc_class CC =
cc :: int
doc_class DD =
dd :: int
doc_class EE =
ee :: int
doc_class FF =
ff :: int

onto_morphism (AA, BB) to CC 
          and (DD, EE) to FF
  where "convert\<^sub>A\<^sub>A\<^sub>\<times>\<^sub>B\<^sub>B\<^sub>\<Rightarrow>\<^sub>C\<^sub>C \<sigma> = \<lparr> CC.tag_attribute = 1::int, CC.cc = aa (fst \<sigma>) + bb (snd \<sigma>)\<rparr>"
  and   "convert\<^sub>D\<^sub>D\<^sub>\<times>\<^sub>E\<^sub>E\<^sub>\<Rightarrow>\<^sub>F\<^sub>F \<sigma> = \<lparr> FF.tag_attribute = 1::int, FF.ff = dd (fst \<sigma>) + ee (snd \<sigma>) \<rparr>"

onto_morphism (AA, BB, CC, DD, EE) to FF
  where "convert\<^sub>A\<^sub>A\<^sub>\<times>\<^sub>B\<^sub>B\<^sub>\<times>\<^sub>C\<^sub>C\<^sub>\<times>\<^sub>D\<^sub>D\<^sub>\<times>\<^sub>E\<^sub>E\<^sub>\<Rightarrow>\<^sub>F\<^sub>F \<sigma> = \<lparr> FF.tag_attribute = 1::int, FF.ff = aa (fst \<sigma>) + bb (fst (snd \<sigma>))\<rparr>"

find_consts name:"convert"
find_theorems name:"convert"


subsection\<open>Proving the Preservation of Ontological Mappings : A Domain-Ontology Morphism\<close>

(* rethink examples: should we "morph" providence too ? ? ? Why not ? bu *)

(*<*)
(* Mapped_PILIB_Ontology example *)
term\<open>fold (+) S 0\<close>  

definition sum 
  where "sum S = (fold (+) S 0)"
(*>*)
datatype Hardware_Type = 
  Motherboard | 
  Expansion_Card | 
  Storage_Device | 
  Fixed_Media | 
  Removable_Media |
  Input_Device |
  Output_Device

datatype Software_Type =
  Operating_system |
  Text_editor |
  Web_Navigator |
  Development_Environment

(* Reference Ontology *)
onto_class Resource =
  name :: string

onto_class Electronic = Resource +
  provider :: string
  manufacturer :: string

onto_class Component = Electronic +
  mass :: int

onto_class Simulation_Model = Electronic +
  simulate :: Component
  composed_of :: "Component list" 
  version :: int

onto_class Informatic = Resource +
  description :: string

onto_class Hardware = Informatic +
  type :: Hardware_Type
  mass :: int
  composed_of :: "Component list" 
  invariant c1 :: "mass \<sigma> = sum(map Component.mass (composed_of \<sigma>))"

onto_class Software = Informatic +
  type ::  Software_Type
  version :: int

(* Local Ontology *)
onto_class Item =
  name :: string

onto_class Product = Item +
  serial_number :: int
  provider :: string
  mass :: int

onto_class Electronic_Component = Product +
  serial_number :: int

onto_class Monitor = Product +
  composed_of :: "Electronic_Component list" 
  invariant c2 :: "Product.mass \<sigma> = sum(map Product.mass (composed_of \<sigma>))"

term\<open>Product.mass \<sigma> = sum(map Product.mass (composed_of \<sigma>))\<close>

onto_class Computer_Software = Item +
  type ::  Software_Type
  version :: int

(* Mapping or Morphism *)
definition Item_to_Resource_morphism :: "Item \<Rightarrow> Resource"
          ("_ \<langle>Resource\<rangle>\<^sub>I\<^sub>t\<^sub>e\<^sub>m" [1000]999)
          where "  \<sigma> \<langle>Resource\<rangle>\<^sub>I\<^sub>t\<^sub>e\<^sub>m = 
                                   \<lparr> Resource.tag_attribute = 1::int ,
                                    Resource.name = name \<sigma> \<rparr>" 

definition Product_to_Resource_morphism :: "Product \<Rightarrow> Resource"
           ("_ \<langle>Resource\<rangle>\<^sub>P\<^sub>r\<^sub>o\<^sub>d\<^sub>u\<^sub>c\<^sub>t" [1000]999)
           where "  \<sigma> \<langle>Resource\<rangle>\<^sub>P\<^sub>r\<^sub>o\<^sub>d\<^sub>u\<^sub>c\<^sub>t = 
                                \<lparr> Resource.tag_attribute = 2::int ,
                                  Resource.name = name \<sigma> \<rparr>" 

definition Computer_Software_to_Software_morphism :: "Computer_Software \<Rightarrow> Software" 
             ("_ \<langle>Software\<rangle>\<^sub>S\<^sub>o\<^sub>f\<^sub>t\<^sub>C\<^sub>m\<^sub>p" [1000]999)
             where "\<sigma> \<langle>Software\<rangle>\<^sub>S\<^sub>o\<^sub>f\<^sub>t\<^sub>C\<^sub>m\<^sub>p = 
                                \<lparr> Resource.tag_attribute = 3::int ,
                                  Resource.name = name \<sigma> ,
                                  Informatic.description = ''no description'', 
                                  Software.type  = type  \<sigma> ,
                                  Software.version = version \<sigma> \<rparr>"

definition Electronic_Component_to_Component_morphism :: "Electronic_Component \<Rightarrow> Component" 
             ("_ \<langle>Component\<rangle>\<^sub>E\<^sub>l\<^sub>e\<^sub>c\<^sub>C\<^sub>m\<^sub>p" [1000]999)
             where "\<sigma> \<langle>Component\<rangle>\<^sub>E\<^sub>l\<^sub>e\<^sub>c\<^sub>C\<^sub>m\<^sub>p = 
                                \<lparr> Resource.tag_attribute = 4::int ,
                                  Resource.name = name \<sigma> ,
                                  Electronic.provider = provider  \<sigma>  ,
                                  Electronic.manufacturer = ''no manufacturer'' ,
                                  Component.mass = mass  \<sigma> \<rparr>"

definition Monitor_to_Hardware_morphism :: "Monitor \<Rightarrow> Hardware"
           ("_ \<langle>Hardware\<rangle>\<^sub>C\<^sub>o\<^sub>m\<^sub>p\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>H\<^sub>a\<^sub>r\<^sub>d\<^sub>w\<^sub>a\<^sub>r\<^sub>e" [1000]999)
           where "\<sigma> \<langle>Hardware\<rangle>\<^sub>C\<^sub>o\<^sub>m\<^sub>p\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>H\<^sub>a\<^sub>r\<^sub>d\<^sub>w\<^sub>a\<^sub>r\<^sub>e =
                  \<lparr>  Resource.tag_attribute = 5::int ,
                     Resource.name = name \<sigma> ,
                     Informatic.description = ''no description'', 
                     Hardware.type = Output_Device,
                     Hardware.mass = mass \<sigma> ,
                     Hardware.composed_of = map  Electronic_Component_to_Component_morphism (composed_of \<sigma>)
                   \<rparr>" 

text\<open>On this basis, we can state the following invariant preservation theorems:\<close>

lemma inv_c2_preserved :
  "c2_inv \<sigma> \<Longrightarrow> c1_inv (\<sigma> \<langle>Hardware\<rangle>\<^sub>C\<^sub>o\<^sub>m\<^sub>p\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>H\<^sub>a\<^sub>r\<^sub>d\<^sub>w\<^sub>a\<^sub>r\<^sub>e)"
  unfolding c1_inv_def c2_inv_def 
            Monitor_to_Hardware_morphism_def Electronic_Component_to_Component_morphism_def
  by (auto simp: comp_def)

lemma Monitor_to_Hardware_morphism_total :
  "Monitor_to_Hardware_morphism ` ({X::Monitor. c2_inv X}) \<subseteq> ({X::Hardware. c1_inv X})"
  using inv_c2_preserved 
  by auto

type_synonym local_ontology = "Item * Electronic_Component * Monitor"
type_synonym reference_ontology = "Resource * Component * Hardware"

fun ontology_mapping :: "local_ontology \<Rightarrow> reference_ontology" 
  where "ontology_mapping (x, y, z) = (x\<langle>Resource\<rangle>\<^sub>I\<^sub>t\<^sub>e\<^sub>m, y\<langle>Component\<rangle>\<^sub>E\<^sub>l\<^sub>e\<^sub>c\<^sub>C\<^sub>m\<^sub>p, z\<langle>Hardware\<rangle>\<^sub>C\<^sub>o\<^sub>m\<^sub>p\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>H\<^sub>a\<^sub>r\<^sub>d\<^sub>w\<^sub>a\<^sub>r\<^sub>e)" 

lemma ontology_mapping_total :
        "ontology_mapping ` {X.  c2_inv (snd (snd X))} \<subseteq> {X.  c1_inv (snd (snd X))}"
  using  inv_c2_preserved 
  by auto


(*<*)
(* switch on regexp syntax *)
notation Star  ("\<lbrace>(_)\<rbrace>\<^sup>*" [0]100)
notation Plus  (infixr "||" 55)
notation Times (infixr "~~" 60)
notation Atom  ("\<lfloor>_\<rfloor>" 65)
(*>*)


subsection\<open>Proving Monitor-Refinements\<close>

text\<open>Monitors are regular-expressions that allow for specifying instances of classes to appear in 
a particular order in a document. They are used to specify some structural aspects of a document.
Based on an AFP theory by Tobias Nipkow on Functional Automata
(\<^ie> a characterization of regular automata using functional polymorphic descriptions of transition
functions avoiding any of the ad-hoc finitizations commonly used in automata theory), which 
comprises also functions to generate executable deterministic and non-deterministic automata,
this theory is compiled to SML-code that was integrated in the \<^dof> system. The necessary
adaptions of this integration can be found in the theory \<^theory>\<open>Isabelle_DOF.RegExpInterface\<close>,
which also contains the basic definitions and theorems for the concepts used here.

Recall that the monitor of \<^term>\<open>scholarly_paper.article\<close> is defined by:  \<^vs>\<open>0.5cm\<close>

@{thm [indent=20, margin=70, names_short] scholarly_paper.article_monitor_def}

 \<^vs>\<open>0.5cm\<close> However, it is possible to reason over the language of monitors and prove classical 
refinement notions such as trace-refinement on the monitor-level, so once-and-for-all for all 
instances of validated documents conforming to a particular ontology. The primitive recursive 
operators\<^term>\<open>RegExpInterface.Lang\<close> and \<^term>\<open>RegExpInterface.L\<^sub>s\<^sub>u\<^sub>b\<close> generate the languages of the
regular expression language, where \<^term>\<open>L\<^sub>s\<^sub>u\<^sub>b\<close> takes the sub-ordering relation of classes into 
account. 

The proof of : \<^vs>\<open>0.5cm\<close>

  @{thm [indent=20,margin=70,names_short] articles_sub_reports}

 \<^vs>\<open>0.5cm\<close> can be found in theory  \<^theory>\<open>Isabelle_DOF.technical_report\<close>; 
it is, "as simple as it should be" (to cite Tony Hoare). 

The proof of: \<^vs>\<open>0.5cm\<close>

  @{thm [indent=20,margin=70,names_short] articles_Lsub_reports}

 \<^vs>\<open>0.5cm\<close> is slightly more evolved; this is due to the fact that \<^dof> does not generate a proof of the
acyclicity of the graph of the class-hierarchy @{term doc_class_rel} automatically. For a given 
hierarchy, this proof will always succeed (since  \<^dof> checks this on the meta-level, of course), 
which permits to deduce the anti-symmetry of the transitive closure of @{term doc_class_rel} 
and therefore to establish that the doc-classes can be organized in an order (\<^ie> the
type \<^typ>\<open>doc_class\<close> is an instance of the type-class \<^class>\<open>order\<close>). On this basis, the proof
of the above language refinement is quasi automatic. This proof is also part of 
 \<^theory>\<open>Isabelle_DOF.technical_report\<close>.
\<close>

(*<*)

(* switch on regexp syntax *)
no_notation Star  ("\<lbrace>(_)\<rbrace>\<^sup>*" [0]100)
no_notation Plus  (infixr "||" 55)
no_notation Times (infixr "~~" 60)
no_notation Atom  ("\<lfloor>_\<rfloor>" 65)

end
(*>*) 
  
