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

chapter \<open>The Figure Technology of the Common Ontology Library\<close>

text\<open> This theory provides the figure-related text-antiquotations (\<open>fig_content\<close>, 
      \<open>figure_content\<close>) and the commands \<open>figure*\<close> and \<open>listing*\<close> of the COL. 
      The document classes \<open>float\<close>, \<open>figure\<close> and \<open>listing\<close> they instantiate are 
      declared in \<^verbatim>\<open>Isa_COL\<close> (their long names are used in the generated LaTeX); they are 
      referred to by name here. \<close>

theory Isa_COL_Figs
  imports Isa_DOF
  keywords "figure*" "listing*" :: document_body

begin

subsection\<open>Figures\<close>

(*<*)

ML\<open>
fun setup source =
  ML_Context.expression (Input.pos_of source)
    (ML_Lex.read "Theory.setup (" @ ML_Lex.read_source source @ ML_Lex.read ")")
  |> Context.theory_map;
\<close>

(*>*)

subsubsection\<open>The Figure Content Antiquotation\<close>
text\<open>The intermediate development goal is to separate the ontological, top-level construct 
\<open>figure*\<close>, which will remain a referentiable, ontological document unit, from the more versatile
\<^emph>\<open>import\<close> of a figure. This opens the way for more orthogonality and abstraction from the LaTeX 
engine.
\<close>
ML\<open>    

type fig_content =   {relative_width  : int, (* percent of textwidth, default 100 *)
                      relative_height : int, (* percent, default 100 *)
                      caption         : Input.source (* default empty *)}

val mt_fig_content = {relative_width  = 100,
                      relative_height = 100,    
                      caption         = Input.empty }: fig_content

fun make_fig_content (relative_width, relative_height, caption) =
   {relative_width = relative_width, relative_height = relative_height, caption = caption}

fun upd_fig_content f =
  fn {relative_width, relative_height, caption} =>
    make_fig_content (f (relative_width, relative_height, caption))

fun upd_relative_width f =
  upd_fig_content (fn (relative_width, relative_height, caption) =>
    (f relative_width, relative_height, caption))

fun upd_relative_height f =
  upd_fig_content (fn (relative_width, relative_height, caption) =>
    (relative_width, f relative_height, caption))

fun upd_caption f =
  upd_fig_content (fn (relative_width, relative_height, caption) =>
    (relative_width, relative_height, f caption))

val widthN     = "width"
val heightN    = "height" 
val captionN   = "caption";

fun fig_content_modes (ctxt, toks) = 
       let val (y, toks') = ((((Scan.optional 
                      (Args.parens 
                         (Parse.list1
                           (   (Args.$$$ widthN |-- Args.$$$ "=" -- Parse.int
                                >> (fn (_, k) => upd_relative_width (K k)))
                            || (Args.$$$ heightN |-- Args.$$$ "=" -- Parse.int
                                >> (fn (_, k) => upd_relative_height (K k)))
                            || (Args.$$$ captionN |-- Args.$$$ "=" -- Parse.document_source
                                >> (fn (_, k) => upd_caption (K k)))
                      ))) [K mt_fig_content]) 
                      : (fig_content -> fig_content) list parser)
                      >> (foldl1 (op #>)))
                      : (fig_content -> fig_content) parser)
                      (toks)
        in (y, (ctxt, toks')) end

fun get_session_dir ctxt path = 
         Resources.check_session_dir ctxt 
                                     (SOME (path))  
                                     (Syntax.read_input ".")
          handle ERROR s => (if String.isPrefix "Bad session root directory (missing ROOT or ROOTS): " s 
                             then get_session_dir ctxt (Path.dir path)
                             else error s)

fun get_document_dir ctxt =
      let val thy = Proof_Context.theory_of ctxt
          val sess_dir = get_session_dir ctxt  (Resources.master_directory thy)
      in  Path.append sess_dir  (Path.explode "document") end;

fun generate_caption ctxt caption = 
    let 
              val cap_txt= Document_Output.output_document ctxt {markdown = false} caption
              fun drop_latex_macro (XML.Elem (("latex_environment", [("name", "isabelle")]),xmlt)) = xmlt
                 |drop_latex_macro X = [X]
              val drop_latex_macros = List.concat o map drop_latex_macro;
    in
      drop_latex_macros cap_txt
    end

fun process_args cfg_trans =
  let val {relative_width,relative_height,caption} = cfg_trans mt_fig_content
      val _ = if relative_width < 0 orelse relative_height <0
              then error("negative parameter.")
               else ()
      val wdth_val_s = Real.toString((Real.fromInt relative_width)
                         / (Real.fromInt 100))^"\\textwidth"
      val ht_s= if relative_height = 100
                then ""
                else "height="
                     ^ Real.toString((Real.fromInt relative_height)
                         / (Real.fromInt 100))
                     ^ "\\textheight"
  in (wdth_val_s, ht_s, caption) end

fun fig_content ctxt (cfg_trans,file:Input.source) = 
       let val (wdth_val_s, ht_s, caption) = process_args cfg_trans
           val arg_single  = enclose "[" "]" (commas ["keepaspectratio","width="^wdth_val_s,ht_s])
           val arg    = enclose "[" "]" (commas ["keepaspectratio","width=\\textwidth",ht_s])
           val _   = Resources.check_file ctxt (SOME (get_document_dir ctxt)) file
           (* ToDo: must be declared source of type png or jpeg or pdf, ... *)
           
       in if Input.string_of(caption) = ""  then
                   file 
                   |> (Latex.string o Input.string_of) 
                   |> Latex.macro ("includegraphics"^arg_single)
          else
                   file 
                   |> (Latex.string o Input.string_of) 
                   |> (fn X => (Latex.string ("{"^wdth_val_s^"}")) 
                                @ (Latex.macro0 "centering")
                                @ (Latex.macro ("includegraphics"^arg) X)
                                @ (Latex.macro "caption" (generate_caption ctxt caption)))
                   |> (Latex.environment ("subcaptionblock") )
(* BUG: newline at the end of subcaptionlbock, making side-by-side a figure-below-figure setup *)
       end

fun fig_content_antiquotation name scan =
  (Document_Output.antiquotation_raw_embedded name 
    (scan : ((fig_content -> fig_content) * Input.source) context_parser)
    (fig_content : Proof.context -> (fig_content -> fig_content) * Input.source -> Latex.text));
          

fun figure_content ctxt (cfg_trans,file:Input.source) =
  let val _   = Resources.check_file ctxt (SOME (get_document_dir ctxt)) file
      (* ToDo: must be declared source of type png or jpeg or pdf, ... *)
      val (wdth_val_s, ht_s, caption) = process_args cfg_trans
      val args = ["keepaspectratio","width=" ^ wdth_val_s, ht_s]
                 |> commas
                 |> enclose "[" "]"
  in file
     |> (Latex.string o Input.string_of)
     |> Latex.macro ("includegraphics" ^ args)
     |> (fn X => X @ Latex.macro "caption" (generate_caption ctxt caption))
     |> Latex.environment ("figure")
  end

fun figure_antiquotation name scan =
  (Document_Output.antiquotation_raw_embedded name
    (scan : ((fig_content -> fig_content) * Input.source) context_parser)
    (figure_content : Proof.context -> (fig_content -> fig_content) * Input.source -> Latex.text));

val _ = Theory.setup 
           (   fig_content_antiquotation \<^binding>\<open>fig_content\<close> 
                                         (fig_content_modes -- Scan.lift(Parse.path_input))
               #> figure_antiquotation \<^binding>\<open>figure_content\<close>
                                         (fig_content_modes -- Scan.lift(Parse.path_input)))

\<close>


ML\<open>


fun convert_meta_args ctxt (X, (((str,_),value) :: R)) =
     let fun conv_int x = snd(HOLogic.dest_number(Syntax.read_term ctxt x))
                          handle TERM _ =>  error "Illegal int format."
     in
         (case Protocol_Message.clean_output str of 
             "relative_width" =>  upd_relative_width (K (conv_int value))
                                  o  convert_meta_args ctxt (X, R)
          |  "relative_height" => upd_relative_height (K (conv_int value))
                                  o  convert_meta_args ctxt (X, R )
          |  "file_src"        => convert_meta_args ctxt (X, R)
          |  s => error("!undefined attribute:"^s))
     end
   |convert_meta_args _ (_,[]) = I

fun convert_src_from_margs ctxt (X, (((str,_),value)::R)) = 
          (case Protocol_Message.clean_output str of 
             "file_src" => Input.string (HOLogic.dest_string (Syntax.read_term ctxt value))
           | _          => convert_src_from_margs ctxt (X,R))
   |convert_src_from_margs _ (_, [])     = error("No file_src provided.")

fun float_command (name, pos) descr cid  =
  let fun set_default_class NONE = SOME(cid,pos)
         |set_default_class (SOME X) = SOME X 
      fun create_instance  (((binding,cid_pos), doc_attrs) : ODL_Meta_Args_Parser.meta_args_t)  =
                DOF_Value_Cmd.Docitem_Parser.create_and_check_docitem 
               {is_monitor = false} 
               {is_inline = true}
               {define = true} binding (set_default_class cid_pos) doc_attrs
      fun generate_fig_ltx_ctxt ctxt cap_src oid body = 
        Latex.macro0 "centering" 
        @ body 
        @ Latex.macro "caption" (generate_caption ctxt cap_src)
        @ Latex.macro "label" (DOF_core.get_instance_name_global oid (Proof_Context.theory_of ctxt)
                               |> DOF_core.output_name
                               |> Latex.string)
      fun parse_and_tex (margs as ((binding,_), _), cap_src) ctxt =
        let val oid = Binding.name_of binding
        in
          (convert_src_from_margs ctxt margs)
          |> pair (upd_caption (K Input.empty) #> convert_meta_args ctxt margs)
          |> fig_content ctxt 
          |> generate_fig_ltx_ctxt ctxt cap_src oid
          |> (Latex.environment ("figure") )
        end
  in  Document_Output_Commands.onto_macro_cmd_command (name, pos) descr create_instance parse_and_tex
  end

fun listing_command (name, pos) descr cid  =
  let fun set_default_class NONE = SOME(cid,pos)
         |set_default_class (SOME X) = SOME X 
      fun create_instance  (((binding,cid_pos), doc_attrs) : ODL_Meta_Args_Parser.meta_args_t)  =
                DOF_Value_Cmd.Docitem_Parser.create_and_check_docitem 
               {is_monitor = false} 
               {is_inline = true}
               {define = true} binding (set_default_class cid_pos) doc_attrs
      fun parse_and_tex (margs as ((binding,_), _), _) _ =
        let val pos = Binding.pos_of binding
        in
          ISA_core.err ("Not yet implemented.\n Please use text*[oid::listing]\<open>\<close> instead.") pos
        end
  in  Document_Output_Commands.onto_macro_cmd_command (name, pos) descr create_instance parse_and_tex
  end
  

(* *********************************************************************** *)
(* Ontological Macro Command Support                                       *)
(* *********************************************************************** *)

val _ = float_command \<^command_keyword>\<open>figure*\<close> "figure" "Isa_COL.figure" ;
val _ = listing_command \<^command_keyword>\<open>listing*\<close> "listing" "Isa_COL.listing" ;  (* Hack ! *)
\<close>

end
