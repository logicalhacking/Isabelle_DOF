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
  imports  Isa_DOF Isa_COL_Gridtbl Isa_COL_Figs
  keywords "title*"        "subtitle*"      
           "chapter*"      "section*"    "paragraph*"
           "subsection*"   "subsubsection*" 
           "frame*" :: document_body

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
doc_class "paragraph" = text_element +
   level         :: "int  option"    <=  "Some 4" 


subsection\<open>Ontological Macros\<close>

ML\<open> 

structure Onto_Macros =
struct
local open ODL_Meta_Args_Parser in
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
   in Document_Output_Commands.gen_enriched_document_cmd {inline=true} I transform end; 

local 
fun transform_cid _ NONE X = X
   |transform_cid _ (SOME ncid) NONE =  (SOME(ncid,@{here}))
   |transform_cid thy (SOME cid) (SOME (sub_cid,pos)) =
                             let val cid_long  = DOF_core.get_onto_class_name_global' cid thy
                                 val sub_cid_long =  DOF_core.get_onto_class_name_global' sub_cid thy
                             in  if DOF_core.is_subclass_global thy  sub_cid_long cid_long
                                 then (SOME (sub_cid,pos))
                                 else (*  BUG : check reveals problem of Definition* misuse.  *)
                                        error("class "^sub_cid_long^
                                              " must be sub-class of "^cid_long) 
                             end  
in

fun transform_attr S doc_attrs =
  let
    fun transform_attr' [] doc_attrs = doc_attrs
      | transform_attr' (s::S) (doc_attrs) =
          let val (name', value) = s
              val doc_attrs' = doc_attrs
                               |> map (fn (name, term) => if name = name'
                                                          then (name, value)
                                                          else (name, term))
          in if doc_attrs' = doc_attrs
             then transform_attr' S doc_attrs' |> cons (name', value) 
             else transform_attr' S doc_attrs' 
          end
  in transform_attr' S doc_attrs end

fun enriched_formal_statement_command ncid (S: (string * string) list) =
  let fun transform_attr doc_attrs = (map (fn(cat,tag) => ((cat,@{here}),tag)) S) @ 
                                      (("formal_results",@{here}),"([]::thm list)")::doc_attrs
  in  fn margs => fn thy =>
          Document_Output_Commands.gen_enriched_document_cmd {inline=true} 
                                    (transform_cid thy ncid) transform_attr margs thy
  end;

fun enriched_document_cmd_exp ncid (S: (string * string) list) =
   (* expands ncid into supertype-check. *)
   let fun transform_attr attrs = (map (fn(cat,tag) => ((cat,@{here}),tag)) S) @ attrs
   in  fn margs => fn thy =>
         Document_Output_Commands.gen_enriched_document_cmd {inline=true} (transform_cid thy ncid)
                                                                            transform_attr margs thy
   end;
end (* local *)


fun heading_command (name, pos) descr level =
  Document_Output_Commands.document_command (name, pos) descr
    {markdown = false, body = true} (enriched_text_element_cmd level) [] I;

val _ = heading_command \<^command_keyword>\<open>title*\<close> "section heading" NONE;
val _ = heading_command \<^command_keyword>\<open>subtitle*\<close> "section heading" NONE;
val _ = heading_command \<^command_keyword>\<open>chapter*\<close> "section heading" (SOME (SOME 0));
val _ = heading_command \<^command_keyword>\<open>section*\<close> "section heading" (SOME (SOME 1));
val _ = heading_command \<^command_keyword>\<open>subsection*\<close> "subsection heading" (SOME (SOME 2));
val _ = heading_command \<^command_keyword>\<open>subsubsection*\<close> "subsubsection heading" (SOME (SOME 3));
val _ = heading_command \<^command_keyword>\<open>paragraph*\<close> "paragraph" (SOME (SOME 4));


end 
end
\<close>


section\<open>Layout Trimming Commands (with syntactic checks)\<close>

ML\<open> 
local

val scan_cm = Scan.ahead (Basic_Symbol_Pos.$$$ "c" |-- Basic_Symbol_Pos.$$$ "m" ) ;
val scan_pt = Scan.ahead (Basic_Symbol_Pos.$$$ "p" |-- Basic_Symbol_Pos.$$$ "t" ) ;
val scan_blank = Scan.repeat (   Basic_Symbol_Pos.$$$ " "
                              || Basic_Symbol_Pos.$$$ "\t" 
                              || Basic_Symbol_Pos.$$$ "\n");

in

val scan_latex_measure = (scan_blank
                          |-- Scan.option (Basic_Symbol_Pos.$$$ "-")
                          |-- Symbol_Pos.scan_nat 
                          |-- (Scan.option ((Basic_Symbol_Pos.$$$ ".") |-- Symbol_Pos.scan_nat))
                          |-- scan_blank
                          |-- (scan_cm || scan_pt)
                          |-- scan_blank
                         ) ;
           
fun check_latex_measure _ src  = 
         let val _ = ((Scan.catch scan_latex_measure (Symbol_Pos.explode(Input.source_content src)))
                     handle Fail _ => error ("syntax error in LaTeX measure") )
         in () end

val parse_latex_measure = Parse.embedded_input >> (fn src => (check_latex_measure () (* dummy arg *) src; 
                                       (fst o Input.source_content) src )  )

end\<close>



setup\<open> DOF_lib.define_macro \<^binding>\<open>vs\<close>  "\\vspace{" "}" (check_latex_measure) \<close> 
setup\<open> DOF_lib.define_macro \<^binding>\<open>hs\<close>  "\\hspace{" "}" (check_latex_measure) \<close> 
define_shortcut* hfill \<rightleftharpoons> \<open>\hfill\<close>
(*<*)

text\<open>Tests: \<^vs>\<open>-0.14cm\<close>\<close>

ML\<open> check_latex_measure @{context} (Input.string "-0.14 cm") \<close>
define_macro* vs2 \<rightleftharpoons> \<open>\vspace{\<close> _ \<open>}\<close> (check_latex_measure) (* checkers NYI on Isar-level *)
define_macro* hs2 \<rightleftharpoons> \<open>\hspace{\<close> _ \<open>}\<close> (* works fine without checker.*)

(*>*)

define_shortcut* clearpage \<rightleftharpoons> \<open>\clearpage{}\<close>
                 hf \<rightleftharpoons> \<open>\hfill\<close> 
                 br \<rightleftharpoons> \<open>\break\<close> 

text\<open>Shortcuts and macros for the names of the system and for standard \LaTeX{}-macros. Their
LaTeX-macros are defined by the core style of the system (\<^verbatim>\<open>isadof\<close>), by the document build 
(\<^verbatim>\<open>dofurl\<close>, generated into the configuration style), by the \LaTeX{}-kernel (\<^verbatim>\<open>LaTeX\<close>, \<^verbatim>\<open>TeX\<close>) 
or by the package \<^verbatim>\<open>hyperref\<close>, which is loaded by all document templates (\<^verbatim>\<open>nolinkurl\<close>). 
They can therefore be used in all documents. Macros that need an own definition in the prelude of a 
document (such as \<^verbatim>\<open>index\<close>, \<^verbatim>\<open>bindex\<close>) belong to the theory of this document.\<close>

define_shortcut* isadof  \<rightleftharpoons> \<open>\isadof{}\<close>
                 dofurl  \<rightleftharpoons> \<open>\dofurl\<close>
                 LaTeX   \<rightleftharpoons> \<open>\LaTeX{}\<close>
                 TeX     \<rightleftharpoons> \<open>\TeX{}\<close>
                 pdf     \<rightleftharpoons> \<open>PDF\<close>
                 html    \<rightleftharpoons> \<open>HTML\<close>
                 http    \<rightleftharpoons> \<open>HTTP\<close>
                 HTTPS   \<rightleftharpoons> \<open>HTTPS\<close>
                 number  \<rightleftharpoons> \<open>no.\<close>


define_macro* nolinkurl \<rightleftharpoons> \<open>\nolinkurl{\<close> _ \<open>}\<close>


section\<open> Library of Standard Figure Ontology \<close>

datatype placement = here  |  top  |  bottom  

(*
ML\<open> "side_by_side_figure"  |> Name_Space.declared (DOF_core.get_onto_classes \<^context>
                           |> Name_Space.space_of_table)\<close>
*)

datatype float_kind = listing | table | graphics

doc_class float        = 
   placement           :: "placement list"
   kind                :: float_kind
   spawn_columns       :: bool <= False 
   main_caption        :: string <= "''''" 

doc_class figure       =  float +
   kind                :: float_kind <= graphics 
   file_src            :: string
   relative_width      :: int 
   relative_height     :: int 
   invariant fig_kind  :: "kind \<sigma> = graphics"


doc_class listing      =  float +
   kind                :: float_kind
   invariant fig_kind' :: "kind \<sigma> = float_kind.listing"


(*<*)

section\<open>Some Rudimentary Tests\<close>

text\<open> @{fig_content   [display] (height = 80, width=80, caption=\<open>this is \<^term>\<open>\<sigma>\<^sub>i+2\<close> \<dots>\<close>) 
                      \<open>figures/isabelle-architecture.pdf\<close>}\<close>
(*>*)

text\<open>beamer support\<close>
(* Under development *)

doc_class frame =
  "options" :: string
  frametitle :: string
  framesubtitle :: string

ML\<open>
type frame = {options: Input.source
              , frametitle: Input.source
              , framesubtitle: Input.source}

val empty_frame = {options = Input.empty
                   , frametitle = Input.empty
                   , framesubtitle = Input.empty}: frame

fun make_frame (options, frametitle, framesubtitle) =
  {options = options, frametitle = frametitle, framesubtitle = framesubtitle}

fun upd_frame f =
  fn {options, frametitle, framesubtitle} => make_frame (f (options, frametitle, framesubtitle))

fun upd_options f =
  upd_frame (fn (options, frametitle, framesubtitle) => (f options, frametitle, framesubtitle))

fun upd_frametitle f =
  upd_frame (fn (options, frametitle, framesubtitle) => (options, f frametitle, framesubtitle))

fun upd_framesubtitle f =
  upd_frame (fn (options, frametitle, framesubtitle) => (options, frametitle, f framesubtitle))

type block = {title: Input.source}

val empty_block = {title = Input.empty}

fun make_block title = {title = title}

fun upd_block f =
  fn {title} => make_block (f title)

fun upd_block_title f =
  upd_block (fn title => f title)

val unenclose_string = unenclose o unenclose

fun read_string s =
  let val s' = DOF_core.markup2string s
      val symbols = s' |> Symbol_Pos.explode0
  in if hd symbols |> fst |> equal Symbol.open_
     then Token.read_cartouche symbols |> Token.input_of
     else unenclose_string s' |> Syntax.read_input
  end

val block_titleN = "title"

fun block_modes (ctxt, toks) =
  let val (y, toks') = ((((Scan.optional
                (Args.parens
                   (Parse.list1
                     ((Args.$$$ block_titleN |-- Args.$$$ "=" -- Parse.document_source
                          >> (fn (_, k) => upd_block_title (K k)))
                      ))) [K empty_block])
                : (block -> block) list parser)
                >> (foldl1 (op #>)))
                : (block -> block) parser)
                (toks)
  in (y, (ctxt, toks')) end

fun process_args cfg_trans =
  let val {title} = cfg_trans empty_block
  in title end

fun block ctxt (cfg_trans,src) =
  let val title = process_args cfg_trans
  in Latex.string "{"
     @ (title |> Document_Output.output_document ctxt {markdown = false})
     @ Latex.string "}"
     @ (src |> Document_Output.output_document ctxt {markdown = false})
     |> (Latex.environment "block")
  end

fun block_antiquotation name scan =
  (Document_Output.antiquotation_raw_embedded name
    (scan : ((block -> block) * Input.source) context_parser)
    (block: Proof.context -> (block -> block) * Input.source -> Latex.text));

val _ = block_antiquotation \<^binding>\<open>block\<close> (block_modes -- Scan.lift Parse.document_source)
        |> Theory.setup

fun convert_meta_args ctxt (X, (((str,_),value) :: R)) =
    (case Protocol_Message.clean_output str of
         "frametitle" =>  upd_frametitle (K(Protocol_Message.clean_output value |> read_string))
                            o convert_meta_args ctxt (X, R)
       | "framesubtitle" => upd_framesubtitle (K(Protocol_Message.clean_output value |> read_string))
                              o convert_meta_args ctxt (X, R)
       | "options" => upd_options (K(Protocol_Message.clean_output value |> read_string))
                        o convert_meta_args ctxt (X, R)
       | s => error("!undefined attribute:"^s))
  | convert_meta_args _ (_,[]) = I

fun frame_command (name, pos) descr cid  =
  let fun set_default_class NONE = SOME(cid,pos)
         |set_default_class (SOME X) = SOME X
      fun create_instance  (((binding,cid_pos), doc_attrs) : ODL_Meta_Args_Parser.meta_args_t)  =
                DOF_Value_Cmd.Docitem_Parser.create_and_check_docitem
               {is_monitor = false}
               {is_inline = true}
               {define = true} binding (set_default_class cid_pos) doc_attrs
      fun titles_src ctxt frametitle framesubtitle src =
        Latex.string "{"
        @ Document_Output.output_document ctxt {markdown = false} frametitle
        @ Latex.string "}"
        @ Latex.string "{"
        @ (Document_Output.output_document ctxt {markdown = false} framesubtitle)
        @ Latex.string "}"
        @ Document_Output.output_document ctxt {markdown = true} src
      fun generate_src_ltx_ctxt ctxt src cfg_trans =
        let val {options, frametitle, framesubtitle} = cfg_trans empty_frame
        in
          let val options_str = Input.string_of options
          in if options_str = ""
             then titles_src ctxt frametitle framesubtitle src
             else (options_str
                   |> enclose "[" "]"
                   |> Latex.string)
                   @ titles_src ctxt frametitle framesubtitle src
          end
       end
      fun parse_and_tex (margs, src) ctxt =
        convert_meta_args ctxt margs
        |> generate_src_ltx_ctxt ctxt src
        |> Latex.environment ("frame")
        |> Latex.environment ("isamarkuptext")
  in Document_Output_Commands.onto_macro_cmd_command (name, pos) descr create_instance parse_and_tex
  end

val _ = frame_command \<^command_keyword>\<open>frame*\<close> "frame environment" "Isa_COL.frame" ;
\<close>

end
