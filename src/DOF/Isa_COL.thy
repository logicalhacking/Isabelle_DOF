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
  keywords "title*"        "subtitle*"      
           "chapter*"      "section*"   
           "subsection*"   "subsubsection*" 
           "paragraph*"    "subparagraph*"         
           "figure*"       "side_by_side_figure*" :: document_body 

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

 
fun enriched_text_element_cmd level =
   let fun transform doc_attrs = case level of 
                  NONE => doc_attrs 
                | SOME(NONE)   => (("level",@{here}),"None")::doc_attrs
                | SOME(SOME x) => (("level",@{here}),"Some("^ Int.toString x ^"::int)")::doc_attrs
   in  gen_enriched_document_cmd {inline=true} I transform end; 

(*
val enriched_document_command_macro = 
    let fun transform_cid X = (writeln (@{make_string} X); X)
    in  gen_enriched_document_command {inline=true} transform_cid I end;
*)


local 
fun transform_cid thy NONE X = X
   |transform_cid thy (SOME ncid) NONE =  (SOME(ncid,@{here}))
   |transform_cid thy (SOME cid) (SOME (sub_cid,pos)) =
                             let val cid_long  = DOF_core.read_cid_global thy cid
                                 val sub_cid_long =  DOF_core.read_cid_global thy sub_cid
                             in  if DOF_core.is_subclass_global thy  sub_cid_long cid_long
                                 then (SOME (sub_cid,pos))
                                 else (* (SOME (sub_cid,pos)) *)
                                      (*  BUG : check reveals problem of Definition* misuse.  *)
                                        error("class "^sub_cid_long^
                                              " must be sub-class of "^cid_long) 
                             end  
in

fun enriched_formal_statement_command ncid (S: (string * string) list) =
   let fun transform_attr doc_attrs = (map (fn(cat,tag) => ((cat,@{here}),tag)) S) @ 
                                      (("formal_results",@{here}),"([]::thm list)")::doc_attrs
   in  fn margs => fn thy =>
          gen_enriched_document_cmd {inline=true} 
                                    (transform_cid thy ncid) transform_attr margs thy 
   end;

fun enriched_document_cmd_exp ncid (S: (string * string) list) =
   (* expands ncid into supertype-check. *)
   let fun transform_attr attrs = (map (fn(cat,tag) => ((cat,@{here}),tag)) S) @ attrs
   in  fn margs => fn thy =>
         gen_enriched_document_cmd {inline=true} (transform_cid thy ncid) transform_attr margs thy
   end;
end (* local *)


fun heading_command (name, pos) descr level =
  ODL_Command_Parser.document_command (name, pos) descr
    {markdown = false, body = true} (enriched_text_element_cmd level);

val _ = heading_command ("title*", @{here}) "section heading" NONE;
val _ = heading_command ("subtitle*", @{here}) "section heading" NONE;
val _ = heading_command ("chapter*", @{here}) "section heading" (SOME (SOME 0));
val _ = heading_command ("section*", @{here}) "section heading" (SOME (SOME 1));
val _ = heading_command ("subsection*", @{here}) "subsection heading" (SOME (SOME 2));
val _ = heading_command ("subsubsection*", @{here}) "subsubsection heading" (SOME (SOME 3));
val _ = heading_command ("paragraph*", @{here}) "paragraph heading" (SOME (SOME 4));
val _ = heading_command ("subparagraph*", @{here}) "subparagraph heading" (SOME (SOME 5));

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

ML\<open>
(* *********************************************************************** *)
(* Ontological Macro Command Support                                       *)
(* *********************************************************************** *)

val _ = Onto_Macros.heading_command ("figure*", @{here}) "figure" NONE;
val _ = Onto_Macros.heading_command ("side_by_side_figure*", @{here}) "multiple figures" NONE;
\<close>

(*<*)
(*
ML\<open>ML_Context.expression\<close>
fun setup source =
  ML_Context.expression (Input.pos_of source)
    (ML_Lex.read "Theory.setup (" @ ML_Lex.read_source source @ ML_Lex.read ")")
  |> Context.theory_map;
setup\<open>\<close>

*)
(*>*)

section\<open>Tables\<close>
(* TODO ! ! ! *)
(* dito the future monitor: table - block *)
(* some studies *)


ML\<open>
local

fun mk_line st1 st2 [a] =  [a @ Latex.string st2]
   |mk_line st1 st2 (a::S) = [a @ Latex.string st1] @ mk_line st1 st2 S;

fun table_antiquotation name =
  Document_Output.antiquotation_raw_embedded name 
    (Scan.repeat1(Scan.repeat1(Scan.lift Args.cartouche_input)))
    (fn ctxt => 
      (fn content:Input.source list list =>
          let fun check _ = ()  (* ToDo *)
              val _  = check content
          in  content 
              |> (map(map (Document_Output.output_document ctxt {markdown = false})
                  #> mk_line "&" "\\\\"
                  #> List.concat )
                  #> List.concat)
              |> XML.enclose "\\table[allerhandquatsch]{" "}"
          end
      )
    );

in

val _ =
  Theory.setup (table_antiquotation \<^binding>\<open>table_inline\<close> );

end
\<close>

section\<open>Tests\<close>
(*<*)
text\<open> @{table_inline [display]
          \<open>\<open>\<open>dfg\<close>\<open>dfg\<close>\<open>dfg\<close>\<close>
           \<open>\<open>1\<close>  \<open>2\<close>  \<open>3\<close>\<close>
          \<close>}\<close>
(*>*)
ML\<open>@{term "side_by_side_figure"};
   @{typ "doc_class rexp"}; 
   DOF_core.SPY;\<close>

end
