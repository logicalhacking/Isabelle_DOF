(*************************************************************************
 * Copyright (C) 
 *               2019-2022 The University of Exeter 
 *               2018-2022 The University of Paris-Saclay
 *               2018      The University of Sheffield
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

chapter \<open>The Document Ontology Framework: Ontological Antiquotations\<close>

text\<open> The antiquotations that refer to instances of document classes and access their attributes. \<close>

theory Isa_DOF_Onto_Text_Antiquotations   (* Ontological antiquotations *)
  imports Isa_DOF_Instances
begin

section\<open> Syntax for Ontological Antiquotations (the '' View'' Part II) \<close>

ML\<open>
structure OntoLinkParser = 
struct

val basic_entity = Document_Output.antiquotation_pretty_source
    : binding -> 'a context_parser -> (Proof.context -> 'a -> Pretty.T) -> theory -> theory;

fun check_and_mark ctxt cid_decl ({strict_checking = strict}) {inline=inline_req} pos name  =
  let
    val thy = Proof_Context.theory_of ctxt;
    val DOF_core.Instance {cid,inline, defined, ...} = DOF_core.get_instance_global name thy
    val _ = if not strict
            then if defined
                 then ISA_core.warn ("Instance defined, unchecked option useless") pos
                 else ()
            else if defined
                 then ()
                 else ISA_core.err ("Instance declared but not defined, try option unchecked") pos
    val _ = if not inline_req 
            then if inline then () else error("referred text-element is macro! (try option display)")
            else if not inline then () else error("referred text-element is no macro!")
    val instances = DOF_core.get_instances ctxt
    val name' = DOF_core.get_instance_name_global name thy
    val markups = name' |> Name_Space.markups (Name_Space.space_of_table instances)
    (* this sends a report for a ref application to the PIDE interface ... *)
    val _ = Context_Position.reports ctxt (map (pair pos) markups);
    val cid' = if cid = DOF_core.default_cid
               then cid
               else DOF_core.get_onto_class_cid thy cid |> (fst o fst)
    val _ = if not(DOF_core.is_subclass ctxt cid' cid_decl)
            then error("reference ontologically inconsistent: "
                       ^ name ^ " is an instance of " ^ cid
                       ^ " and " ^ cid
                       ^ " is not a subclass of " ^ cid_decl ^ Position.here pos)
            else ()
  in () end

val _ =  check_and_mark : Proof.context ->  string ->  
                          {strict_checking: bool} -> {inline:bool} ->
                          Position.T -> Symtab.key -> unit

(* generic syntax for doc_class links. *) 

val defineN    = "define"
val uncheckedN = "unchecked" 

val docitem_modes = Scan.optional (Args.parens (Args.$$$ defineN || Args.$$$ uncheckedN) 
                                   >> (fn str => if str = defineN 
                                                 then {unchecked = false, define= true}  
                                                 else {unchecked = true,  define= false})) 
                                   {unchecked = false, define= false} (* default *);


val docitem_antiquotation_parser = (Scan.lift (docitem_modes -- Parse.embedded_input))
                                   : ({define:bool,unchecked:bool} * Input.source) context_parser;


fun pretty_docitem_antiquotation_generic cid_decl ctxt ({unchecked, define}, src ) = 
    let val (str,pos) = Input.source_content src
                        |> apfst (fn str => (Proof_Context.theory_of ctxt)
                                            |> DOF_core.get_instance_name_global str)
        val inline = Config.get ctxt Document_Antiquotation.thy_output_display
        val _ = check_and_mark ctxt cid_decl {strict_checking = not unchecked} 
                                             {inline = inline} pos str
        val cid_decl' = DOF_core.output_name cid_decl
    in  
        (case (define,inline) of
            (true,false) => XML.enclose("{\\isaDofDOTlabel[type={"^cid_decl'^"}]   {")"}}" 
           |(false,false)=> XML.enclose("{\\isaDofDOTref[type={"^cid_decl'^"}]     {")"}}"
           |(true,true)  => XML.enclose("{\\isaDofDOTmacroDef[type={"^cid_decl'^"}]{")"}}" 
           |(false,true) => XML.enclose("{\\isaDofDOTmacroExp[type={"^cid_decl'^"}]{")"}}"
        )
        (Latex.text (DOF_core.output_name str, pos))
    end      


fun docitem_antiquotation bind cid =
  Document_Output.antiquotation_raw bind  docitem_antiquotation_parser
                                       (pretty_docitem_antiquotation_generic cid)

fun check_and_mark_term ctxt oid  =
  let
    val ctxt' = Context.proof_of ctxt
    val thy = Proof_Context.theory_of ctxt';
    val oid' = DOF_core.get_instance_name_global oid thy
    val DOF_core.Instance {cid,termNvalue,...} = DOF_core.get_instance_global oid' thy
    val instances = DOF_core.get_instances ctxt'
    val ns = instances |> Name_Space.space_of_table 
    val pos = Name_Space.the_entry_pos ns oid'
    val markups = oid' |> Name_Space.markups (Name_Space.space_of_table instances)
    val _ = Context_Position.reports ctxt' (map (pair pos) markups);
    (* this sends a report for a ref application to the PIDE interface ... *) 
    val _ = if cid = DOF_core.default_cid
            then error("anonymous "^ DOF_core.default_cid ^ " class has no value" )
            else ()
  in snd (Future.join termNvalue) end

fun ML_antiquotation_docitem_value (ctxt, toks) = 
    (Scan.lift (Args.cartouche_input) 
     >> (fn inp => (ML_Syntax.atomic o ML_Syntax.print_term) 
                   ((check_and_mark_term ctxt o fst o Input.source_content) inp)))
     (ctxt, toks)

(* Setup for general docitems of the global DOF_core.default_cid - class ("text")*)
val _ = Theory.setup
           (docitem_antiquotation   \<^binding>\<open>docitem\<close>  DOF_core.default_cid #>
            
            ML_Antiquotation.inline \<^binding>\<open>docitem_value\<close> ML_antiquotation_docitem_value)

end (* struct *)
\<close>


ML\<open> 
structure AttributeAccess = 
struct

val basic_entity = Document_Output.antiquotation_pretty_source 
    : binding -> 'a context_parser -> (Proof.context -> 'a -> Pretty.T) -> theory -> theory;

fun compute_trace_ML ctxt oid pos_opt pos' =
    (* grabs attribute, and converts its HOL-term into (textual) ML representation *)
  let val term = ISA_core.compute_attr_access ctxt traceN oid pos_opt pos'
      fun conv (\<^Const>\<open>Pair \<^typ>\<open>doc_class rexp\<close> \<^typ>\<open>string\<close>\<close>
                  $ (\<^Const>\<open>Atom \<^typ>\<open>doc_class\<close>\<close> $ (\<^Const>\<open>mk\<close> $ s)) $ S) =
        let val s' =  DOF_core.get_onto_class_name_global (HOLogic.dest_string s) (Context.theory_of ctxt)
        in (s', HOLogic.dest_string S) end
  in  map conv (HOLogic.dest_list term) end


val parse_oid  = Scan.lift(Parse.position Args.name) 
val parse_cid  = Scan.lift(Parse.position Args.name) 
val parse_oid' = Term_Style.parse -- parse_oid
val parse_oid'' = Scan.lift(Parse.embedded_position)
val parse_cid' = Term_Style.parse -- parse_cid



val parse_attribute_access = (parse_oid
                              --| (Scan.lift @{keyword "::"}) 
                              -- Scan.lift (Parse.position Args.name))
                              : ((string *Position.T) * (string * Position.T)) context_parser 

val parse_attribute_access' = Term_Style.parse -- parse_attribute_access
                              : ((term -> term) *
                                 ((string * Position.T) * (string * Position.T))) context_parser

fun attr_2_ML ctxt ((attr:string,pos),(oid:string,pos')) = (ML_Syntax.atomic o ML_Syntax.print_term) 
                                                           (ISA_core.compute_attr_access ctxt attr oid (SOME pos) pos') 


fun get_instance_value_2_ML ctxt (oid:string,pos) =
    let val ctxt' = Context.the_proof ctxt
        val thy = Proof_Context.theory_of ctxt'
        val value = DOF_core.value_of oid thy
        val instances = DOF_core.get_instances ctxt'
        val markups = DOF_core.get_instance_name_global oid thy
                     |> Name_Space.markups (Name_Space.space_of_table instances)
        val _ = Context_Position.reports ctxt' (map (pair pos) markups);
    in  ML_Syntax.print_term value end

fun get_instance_name_2_ML ctxt (oid:string,pos) =
    let val ctxt' = Context.the_proof ctxt
        val instances = DOF_core.get_instances ctxt'
        val markups = DOF_core.get_instance_name_global oid (Proof_Context.theory_of ctxt')
                     |> Name_Space.markups (Name_Space.space_of_table instances)
        val _ = Context_Position.reports ctxt' (map (pair pos) markups);
    in "\"" ^ oid ^ "\"" end

fun trace_attr_2_ML ctxt (oid:string,pos) =
    let val print_string_pair = ML_Syntax.print_pair  ML_Syntax.print_string ML_Syntax.print_string
        val toML = (ML_Syntax.atomic o (ML_Syntax.print_list print_string_pair))
    in  toML (compute_trace_ML ctxt oid NONE pos) end 

fun compute_cid_repr ctxt cid _ = 
  let val _ = DOF_core.get_onto_class_name_global cid (Proof_Context.theory_of ctxt)
  in Const(cid,dummyT) end

local

fun pretty_attr_access_style ctxt (style, ((attr,pos),(oid,pos'))) = 
           Document_Output.pretty_term ctxt (style (ISA_core.compute_attr_access (Context.Proof ctxt) 
                                                                    attr oid (SOME pos) pos'));
fun pretty_trace_style ctxt (style, (oid,pos)) = 
          Document_Output.pretty_term ctxt (style (ISA_core.compute_attr_access  (Context.Proof ctxt) 
                                                                   traceN oid NONE pos));

fun pretty_name_style ctxt (oid,pos) =
let
  val instances = DOF_core.get_instances ctxt
  val ns = Name_Space.space_of_table instances
  val name  = DOF_core.get_instance_name_global oid (Proof_Context.theory_of ctxt)
  val ctxt' = Config.put Name_Space.names_unique true ctxt
  val markups = Name_Space.markups ns name
  val _ = Context_Position.reports ctxt (map (pair pos) markups)
in Name_Space.pretty ctxt' ns name end

fun pretty_cid_style ctxt (style, (cid,pos)) = 
          Document_Output.pretty_term ctxt (style (compute_cid_repr ctxt cid pos));

(* NEW VERSION: PLEASE INTEGRATE ALL OVER : *)
fun context_position_parser parse_con (ctxt, toks) = 
     let val pos = case toks of 
                    a :: _ => Token.pos_of a 
                  | _ => @{here}             \<comment> \<open>a real hack !\<close>
         val (res, (ctxt', toks')) = parse_con (ctxt, toks)
     in  ((res,pos),(ctxt', toks')) end

val parse_cid0 = parse_cid
val parse_cid = (context_position_parser Args.typ_abbrev)
          >> (fn (Type(ss,_),pos) =>  (pos,ss)
                |( _,pos) => ISA_core.err "Undefined Class Id" pos);


val parse_cid' = Term_Style.parse -- parse_cid

fun pretty_cid_style ctxt (_,(pos,cid)) = 
    (*reconversion to term in order to have access to term print options like: names_short etc...) *)
          Document_Output.pretty_term ctxt ((compute_cid_repr ctxt cid pos));

fun get_class_2_ML ctxt (str,_) =
        let val thy = Context.theory_of ctxt
            val DOF_core.Onto_Class S = (DOF_core.get_onto_class_global' str thy) 
         in @{make_string} S end

in
val _ = Theory.setup 
           (ML_Antiquotation.inline  \<^binding>\<open>docitem\<close> 
               (fn (ctxt,toks) => (parse_oid >> get_instance_value_2_ML ctxt) (ctxt, toks))  #>
            ML_Antiquotation.inline  \<^binding>\<open>docitem_attribute\<close> 
               (fn (ctxt,toks) => (parse_attribute_access >>  attr_2_ML ctxt) (ctxt, toks))  #>
            ML_Antiquotation.inline  \<^binding>\<open>trace_attribute\<close>  
               (fn (ctxt,toks) => (parse_oid >> trace_attr_2_ML ctxt) (ctxt, toks)) #>
            ML_Antiquotation.inline  \<^binding>\<open>docitem_name\<close>  
               (fn (ctxt,toks) => (parse_oid >> get_instance_name_2_ML ctxt) (ctxt, toks)) #>
            ML_Antiquotation.inline  \<^binding>\<open>doc_class\<close>  
               (fn (ctxt,toks) => (parse_cid0 >> get_class_2_ML ctxt) (ctxt, toks)) #>
            basic_entity  \<^binding>\<open>trace_attribute\<close>  parse_oid'  pretty_trace_style #>
            basic_entity  \<^binding>\<open>doc_class\<close>  parse_cid'  pretty_cid_style #>
            basic_entity  \<^binding>\<open>onto_class\<close> parse_cid'  pretty_cid_style #>
            basic_entity  \<^binding>\<open>docitem_attribute\<close>  parse_attribute_access' pretty_attr_access_style #>
            basic_entity  \<^binding>\<open>docitem_name\<close>  parse_oid'' pretty_name_style
           )
end
end
\<close>

text\<open> Note that the functions \<^verbatim>\<open>basic_entities\<close> and \<^verbatim>\<open>basic_entity\<close> in 
      @{ML_structure AttributeAccess} are copied from 
      @{file "$ISABELLE_HOME/src/Pure/Thy/document_output.ML"} \<close>

end
