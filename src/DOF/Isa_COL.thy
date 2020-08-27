(*************************************************************************
 * Copyright (C) 
 *               2019      The University of Exeter 
 *               2018-2019 The University of Paris-Saclay
 *               2018      The University of Sheffield
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

chapter \<open>The Document Ontology Common Library for the Isabelle Ontology Framework\<close>

text\<open> Building a fundamental infrastructure for common document elements such as
      Structuring Text-Elements (the top classes), Figures, (Tables yet todo)

      The COL provides a number of ontological "macros" like "section*" which 
      automatically set a number of class-attributes in particular ways without 
      user-interference. 
    \<close> 

theory Isa_COL   
  imports  Isa_DOF  
  keywords "title*"     "subtitle*"     "chapter*" 
           "section*"   "subsection*"   "subsubsection*" 
           "paragraph*" "subparagraph*"       :: document_body 
  and      "figure*" "side_by_side_figure*"   :: document_body 
  and      "assert*" :: thy_decl
          

begin
  
section\<open>Basic Text and Text-Structuring Elements\<close>

text\<open> The attribute @{term "level"} in the subsequent enables doc-notation support section* etc.
we follow LaTeX terminology on levels 
\<^enum>             part          = Some -1
\<^enum>             chapter       = Some 0
\<^enum>             section       = Some 1
\<^enum>             subsection    = Some 2
\<^enum>             subsubsection = Some 3
\<^enum>             ... 

for scholarly paper: invariant level > 0. \<close>

doc_class text_element =     
   level         :: "int  option"    <=  "None" 
   referentiable :: bool <= "False"
   variants      :: "String.literal set" <= "{STR ''outline'', STR ''document''}" 

doc_class "chapter" = text_element +
   level         :: "int  option"    <=  "Some 0" 
doc_class "section" = text_element +
   level         :: "int  option"    <=  "Some 1" 
doc_class "subsection" = text_element +
   level         :: "int  option"    <=  "Some 2" 
doc_class "subsubsection" = text_element +
   level         :: "int  option"    <=  "Some 3" 


subsection\<open>Ontological Macros\<close>

ML\<open> 

structure Onto_Macros =
struct
local open ODL_Command_Parser in
(* *********************************************************************** *)
(* Ontological Macro Command Support                                       *)
(* *********************************************************************** *)

(* {markdown = true} sets the parsing process such that in the text-core markdown elements are
   accepted. *)

 
fun enriched_document_command level =
   let fun transform doc_attrs = case level of 
                  NONE => doc_attrs 
                | SOME(NONE)   => (("level",@{here}),"None")::doc_attrs
                | SOME(SOME x) => (("level",@{here}),"Some("^ Int.toString x ^"::int)")::doc_attrs
   in  gen_enriched_document_command {inline=true} I transform end; 

val enriched_document_command_macro = enriched_document_command (* TODO ... *)


fun enriched_formal_statement_command ncid (S: (string * string) list) =
   let val transform_cid = case ncid of  NONE => I
                                       | SOME(ncid) => 
                                            (fn X => case X of NONE => (SOME(ncid,@{here}))
                                                             | _ => X)  
       fun transform_attr doc_attrs = (map (fn(cat,tag) => ((cat,@{here}),tag)) S) @ 
                                 (("formal_results",@{here}),"([]::thm list)")::doc_attrs
   in  gen_enriched_document_command {inline=true} transform_cid transform_attr end;


fun assertion_cmd'((((((oid,pos),cid_pos),doc_attrs),name_opt:string option),modes : string list),
                prop) =
    let fun conv_2_holstring thy =  (bstring_to_holstring (Proof_Context.init_global thy))
        fun conv_attrs thy = (("properties",pos),"[@{termrepr ''"^conv_2_holstring thy prop ^" ''}]")
                             ::doc_attrs  
        fun conv_attrs' thy = map (fn ((lhs,pos),rhs) => (((lhs,pos),"+="),rhs)) (conv_attrs thy)
        fun mks thy = case DOF_core.get_object_global_opt oid thy of
                   SOME NONE => (error("update of declared but not created doc_item:" ^ oid))
                 | SOME _ => (update_instance_command (((oid,pos),cid_pos),conv_attrs' thy) thy)
                 | NONE   => (create_and_check_docitem 
                                 {is_monitor = false} {is_inline = false} 
                                 oid pos cid_pos (conv_attrs thy) thy)
        val check = (assert_cmd name_opt modes prop) o Proof_Context.init_global
    in 
        (* Toplevel.keep (check o Toplevel.context_of) *)
        Toplevel.theory (fn thy => (check thy; mks thy))
    end


val _ =
  Outer_Syntax.command @{command_keyword "assert*"} 
                       "evaluate and print term"
                       (attributes -- opt_evaluator -- opt_modes  -- Parse.term  >> assertion_cmd'); 


val _ =
  Outer_Syntax.command ("title*", @{here}) "section heading"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> (Toplevel.theory o (enriched_document_command NONE {markdown = false} ))) ;

val _ =
  Outer_Syntax.command ("subtitle*", @{here}) "section heading"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> (Toplevel.theory o (enriched_document_command NONE {markdown = false} )));

val _ =
  Outer_Syntax.command ("chapter*", @{here}) "section heading"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> (Toplevel.theory o (enriched_document_command (SOME(SOME 0)) {markdown = false} )));

val _ =
  Outer_Syntax.command ("section*", @{here}) "section heading"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> (Toplevel.theory o (enriched_document_command (SOME(SOME 1)) {markdown = false} )));


val _ =
  Outer_Syntax.command ("subsection*", @{here}) "subsection heading"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> (Toplevel.theory o (enriched_document_command (SOME(SOME 2)) {markdown = false} )));

val _ =
  Outer_Syntax.command ("subsubsection*", @{here}) "subsubsection heading"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> (Toplevel.theory o (enriched_document_command (SOME(SOME 3)) {markdown = false} )));

val _ =
  Outer_Syntax.command ("paragraph*", @{here}) "paragraph heading"
    (attributes --  Parse.opt_target -- Parse.document_source --| semi
      >> (Toplevel.theory o (enriched_document_command (SOME(SOME 4)) {markdown = false} )));

val _ =
  Outer_Syntax.command ("subparagraph*", @{here}) "subparagraph heading"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> (Toplevel.theory o (enriched_document_command (SOME(SOME 5)) {markdown = false} )));

end 
end
\<close>

section\<open> Library of Standard Text Ontology \<close>

datatype placement = pl_h  | (*here*) 
                     pl_t  | (*top*)
                     pl_b  | (*bottom*)
                     pl_ht | (*here ->  top*) 
                     pl_hb   (*here ->  bottom*)

ML\<open>(Symtab.defined (#docclass_tab(DOF_core.get_data_global @{theory}))) "side_by_side_figure"\<close>

print_doc_classes


doc_class figure   = 
   relative_width   :: "int"  (* percent of textwidth *)    
   src              :: "string"
   placement        :: placement  
   spawn_columns    :: bool <= True 


doc_class side_by_side_figure = figure +
   anchor           :: "string"
   caption          :: "string"
   relative_width2  :: "int"  (* percent of textwidth *)    
   src2             :: "string"
   anchor2          :: "string"
   caption2         :: "string"

print_doc_classes

doc_class figure_group = 
   (*  trace :: "doc_class rexp list" <= "[]" automatically generated since monitor clause *)
   caption          :: "string"
   rejects             figure_group   (* this forbids recursive figure-groups not supported
                                        by the current LaTeX style-file. *)
   accepts             "\<lbrace>figure\<rbrace>\<^sup>+"

print_doc_classes

subsection\<open>Ontological Macros\<close>

ML\<open> local open ODL_Command_Parser in
(* *********************************************************************** *)
(* Ontological Macro Command Support                                       *)
(* *********************************************************************** *)

val _ =
  Outer_Syntax.command ("figure*", @{here}) "figure"
    (attributes --  Parse.opt_target -- Parse.document_source --| semi
      >> (Toplevel.theory o (Onto_Macros.enriched_document_command NONE {markdown = false} )));

val _ =
  Outer_Syntax.command ("side_by_side_figure*", @{here}) "multiple figures"
    (attributes --  Parse.opt_target -- Parse.document_source --| semi
      >> (Toplevel.theory o (Onto_Macros.enriched_document_command NONE {markdown = false} )));



end 
\<close>

section\<open>Shortcuts, Macros, Environments\<close>
text\<open>The features described in this section are actually \<^emph>\<open>not\<close> real ISADOF features, rather a 
slightly more abstract layer over somewhat buried standard features of the Isabelle document 
generator ... (Thanks to Makarius) Conceptually, they are \<^emph>\<open>sub-text-elements\<close>. \<close>

text\<open>This module provides mechanisms to define front-end checked:
\<^enum> \<^emph>\<open>shortcuts\<close>, i.e. machine-checked abbreviations without arguments 
  that were mapped to user-defined LaTeX code (Example: \<^verbatim>\<open>\ie\<close>)
\<^enum> \<^emph>\<open>macros\<close>  with one argument that were mapped to user-defined code. Example: \<^verbatim>\<open>\myurl{bla}\<close>.
  The argument can be potentially checked and reports can be sent to PIDE;
  if no such checking is desired, this can be expressed by setting the
  \<^theory_text>\<open>reportNtest\<close>-parameter to \<^theory_text>\<open>K(K())\<close>.
\<^enum> \<^emph>\<open>macros\<close> with two arguments, potentially independently checked. See above. 
  Example: \<^verbatim>\<open>\myurl[ding]{dong}\<close>,
\<^enum> \<^emph>\<open>boxes\<close> which are more complex sub-text-elements in the line of the \<^verbatim>\<open>verbatim\<close> or 
  \<^verbatim>\<open>theory_text\<close> environments.

Note that we deliberately refrained from a code-template definition mechanism for simplicity,
so the patterns were just described by strings.  No additional ado with quoting/unquoting 
mechanisms ... 
\<close>

ML\<open>
structure DOF_lib =
struct
fun define_shortcut name latexshcut = 
       Thy_Output.antiquotation_raw name (Scan.succeed ())
          (fn _ => fn () => Latex.string latexshcut) 

(* This is a generalization of the Isabelle2020 function "control_antiquotation" from 
   document_antiquotations.ML. (Thanks Makarius!) *)
fun define_macro name s1 s2 reportNtest =
      Thy_Output.antiquotation_raw_embedded name (Scan.lift Args.cartouche_input)
         (fn ctxt => 
             fn src => let val () = reportNtest ctxt src 
                       in  src |>   Latex.enclose_block s1 s2 
                                  o Thy_Output.output_document ctxt {markdown = false}
                       end);

local (* hide away really strange local construction *)
fun enclose_body2 front body1 middle body2 post =
  (if front = "" then [] else [Latex.string front]) @ body1 @
  (if middle = "" then [] else [Latex.string middle]) @ body2 @
  (if post = "" then [] else [Latex.string post]);
in
fun define_macro2 name front middle post reportNtest1 reportNtest2 =
      Thy_Output.antiquotation_raw_embedded name (Scan.lift (   Args.cartouche_input 
                                                             -- Args.cartouche_input))
         (fn ctxt => 
             fn (src1,src2) => let val () = reportNtest1 ctxt src1 
                                   val () = reportNtest2 ctxt src2 
                                   val T1 = Thy_Output.output_document ctxt {markdown = false} src1
                                   val T2 = Thy_Output.output_document ctxt {markdown = false} src2
                               in  Latex.block(enclose_body2 front T1 middle T2 post)
                               end);
end

fun report_text ctxt text =
    let val pos = Input.pos_of text in
       Context_Position.reports ctxt
         [(pos, Markup.language_text (Input.is_delimited text)),
          (pos, Markup.raw_text)]
    end;

fun report_theory_text ctxt text =
    let val keywords = Thy_Header.get_keywords' ctxt;
        val _ = report_text ctxt text;
        val _ =
          Input.source_explode text
          |> Token.tokenize keywords {strict = true}
          |> maps (Token.reports keywords)
          |> Context_Position.reports_text ctxt;
    in () end

fun prepare_text ctxt =
  Input.source_content #> #1 #> Document_Antiquotation.prepare_lines ctxt;
(* This also produces indent-expansion and changes space to "\_" and the introduction of "\newline",
   I believe. Otherwise its in Thy_Output.output_source, the compiler from string to LaTeX.text. *)

fun string_2_text_antiquotation ctxt text = 
        prepare_text ctxt text
        |> Thy_Output.output_source ctxt
        |> Thy_Output.isabelle ctxt

fun string_2_theory_text_antiquotation ctxt text =
      let
        val keywords = Thy_Header.get_keywords' ctxt;
      in
        prepare_text ctxt text
        |> Token.explode0 keywords
        |> maps (Thy_Output.output_token ctxt)
        |> Thy_Output.isabelle ctxt
      end

fun gen_text_antiquotation name reportNcheck compile =
  Thy_Output.antiquotation_raw_embedded name (Scan.lift Args.text_input)
    (fn ctxt => fn text:Input.source =>
      let
        val _ = reportNcheck ctxt text;
      in
        compile ctxt text    
      end);

fun std_text_antiquotation name (* redefined in these more abstract terms *) =
    gen_text_antiquotation name report_text string_2_text_antiquotation

(* should be the same as (2020):
fun text_antiquotation name =
  Thy_Output.antiquotation_raw_embedded name (Scan.lift Args.text_input)
    (fn ctxt => fn text =>
      let
        val _ = report_text ctxt text;
      in
        prepare_text ctxt text
        |> Thy_Output.output_source ctxt
        |> Thy_Output.isabelle ctxt
      end);
*)

fun std_theory_text_antiquotation name (* redefined in these more abstract terms *) =
    gen_text_antiquotation name report_theory_text string_2_theory_text_antiquotation

(* should be the same as (2020):
fun theory_text_antiquotation name =
  Thy_Output.antiquotation_raw_embedded name (Scan.lift Args.text_input)
    (fn ctxt => fn text =>
      let
        val keywords = Thy_Header.get_keywords' ctxt;

        val _ = report_text ctxt text;
        val _ =
          Input.source_explode text
          |> Token.tokenize keywords {strict = true}
          |> maps (Token.reports keywords)
          |> Context_Position.reports_text ctxt;
      in
        prepare_text ctxt text
        |> Token.explode0 keywords
        |> maps (Thy_Output.output_token ctxt)
        |> Thy_Output.isabelle ctxt
        |> enclose_env ctxt "isarbox"
      end);
*)



fun enclose_env ctxt block_env body =
  if Config.get ctxt Document_Antiquotation.thy_output_display
  then Latex.environment_block block_env [body]
  else body;

end
\<close>


section\<open>Tables\<close>
(* TODO ! ! ! *)

(* dito the future monitor: table - block *)


section\<open>Tests\<close>
   
ML\<open>@{term "side_by_side_figure"};
@{typ "doc_class rexp"}; 
DOF_core.SPY;
\<close>



section\<open>DEPRECATED : An attempt to model Standard Isabelle Formal Content\<close>

doc_class assertions =
    properties :: "term list"
  
doc_class "thms" =
    properties :: "thm list"

doc_class formal_item = 
    item :: "(assertions + thms)"

doc_class definitions =
    requires    :: "formal_item list"
    establishes :: "thms list"

doc_class formal_content =
    style :: "string option"
    accepts "\<lbrace>formal_item\<rbrace>\<^sup>+"

doc_class concept = 
    tag        :: "string"   <= "''''"
    properties :: "thm list" <= "[]"


end
