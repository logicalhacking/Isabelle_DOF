(*************************************************************************
 * Copyright (C) 
 *               2019-2023 The University of Exeter 
 *               2018-2023 The University of Paris-Saclay
 *               2018      The University of Sheffield
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

chapter\<open>The Isabelle/DOF TestKit\<close>

theory 
  TestKit
imports 
  "Isabelle_DOF_Unit_Tests_document"
  "Isabelle_DOF-Ontologies.Conceptual"
keywords "text-" "text-latex"             :: document_body
    and  "text-assert-error"              :: document_body
    and  "update_instance-assert-error"   :: document_body
    and  "declare_reference-assert-error" :: document_body
    and  "value-assert-error"             :: document_body
    and  "definition-assert-error"        :: document_body
    and  "doc_class-assert-error"        :: document_body

begin

section\<open>Testing Commands (exec-catch-verify - versions of DOF commands)\<close>

ML\<open> 

fun gen_enriched_document_command2 name {body} cid_transform attr_transform markdown
                                  ((meta_args,
                                     xstring_opt:(xstring * Position.T) option),
                                    toks_list:Input.source list) 
                                  : theory -> theory =
  let  val toplvl = Toplevel.make_state o SOME
       val ((binding,cid_pos), doc_attrs) = meta_args
       val oid = Binding.name_of binding
       val oid' = if meta_args = ODL_Meta_Args_Parser.empty_meta_args
                  then "output"
                  else oid
       (* as side-effect, generates markup *)
       fun check_n_tex_text thy toks = let val ctxt = Toplevel.presentation_context (toplvl thy)
                                      val pos = Input.pos_of toks;
                                      val _ =   Context_Position.reports ctxt
                                                [(pos, Markup.language_document (Input.is_delimited toks)),
                                                 (pos, Markup.plain_text)];
                                      fun markup xml = let val m = if body then Markup.latex_body 
                                                                   else Markup.latex_heading
                                                       in [XML.Elem (m (Latex.output_name name), 
                                                           xml)] end;

                                      val text = Document_Output.output_document 
                                                                 (Proof_Context.init_global thy) 
                                                                 markdown toks
(*   type file = {path: Path.T, pos: Position.T, content: string} *) 

                                      val strg = XML.string_of (hd (Latex.output text))
                                      val file = {path = Path.make [oid' ^ "_snippet.tex"],
                                                  pos = @{here}, 
                                                  content = Bytes.string strg}
                                      val dir = Path.append (Resources.master_directory thy) (Path.make ["latex_test"]) 
                                      val _ = Generated_Files.write_file dir file
                                      val _ = writeln (strg)
                                  in  () end \<comment> \<open>important observation: thy is not modified.
                                                  This implies that several text block can be 
                                                  processed in parallel in a future, as long
                                                  as they are associated to one meta arg.\<close>
       val handle_margs_opt = (if meta_args = ODL_Meta_Args_Parser.empty_meta_args
              then I
              else
          Value_Command.Docitem_Parser.create_and_check_docitem 
                              {is_monitor = false} {is_inline = false} {define = true}
                              binding (cid_transform cid_pos) (attr_transform doc_attrs))
       (* ... generating the level-attribute syntax *)
  in   handle_margs_opt  #> (fn thy => (app (check_n_tex_text thy) toks_list; thy))
  end;

val _ =
  Outer_Syntax.command ("text-", @{here}) "formal comment macro"
    (ODL_Meta_Args_Parser.attributes -- Parse.opt_target -- Scan.repeat1 Parse.document_source 
      >> (Toplevel.theory o (gen_enriched_document_command2 "TTT" {body=true} I I {markdown = true} )));

(* copied from Pure_syn for experiments *)

fun output_document2 state markdown txt =
  let
    val ctxt = Toplevel.presentation_context state;
    val pos = Input.pos_of txt;
    val _ =
      Context_Position.reports ctxt
        [(pos, Markup.language_document (Input.is_delimited txt)),
         (pos, Markup.plain_text)];
    val txt' = Document_Output.output_document ctxt markdown txt
    val strg = XML.string_of (hd (Latex.output txt'))

    val _ = writeln (strg)
  in Document_Output.output_document ctxt markdown txt end;

fun document_command2 markdown (loc, txt) =
  let fun doc2 state = (case loc of
                      NONE => ignore (output_document2 state markdown txt)
                    | SOME (_, pos) =>(ISA_core.err 
                                           "Illegal target specification -- not a theory context" 
                                           pos))
      fun out2 state = output_document2 state markdown txt
  in  Toplevel.keep doc2  o  Toplevel.present_local_theory loc out2
  end

fun gen_enriched_document_command3 assert name body trans at md (margs, src_list) thy
 = (gen_enriched_document_command2 name body trans at md  (margs, src_list)  thy)
   handle ERROR msg => (if assert src_list msg then (writeln ("Correct error: "^msg^": reported.");thy)
                                               else error"Wrong error reported")

fun error_match src msg = (String.isPrefix (Input.string_of src) msg)

fun  error_match2 [_, src] msg = error_match src msg
   | error_match2 _ _ = error "Wrong text-assertion-error. Argument format <arg><match> required."


val _ =
  Outer_Syntax.command ("text-assert-error", @{here}) "formal comment macro"
    (ODL_Meta_Args_Parser.opt_attributes -- Parse.opt_target -- Scan.repeat1 Parse.document_source 
      >> (Toplevel.theory o (gen_enriched_document_command3 error_match2 "TTT" {body=true}
                                                            I I {markdown = true} )));

fun update_instance_command (args,src) thy = 
    (Monitor_Command_Parser.update_instance_command args thy
     handle ERROR msg => (if error_match src msg 
                          then (writeln ("Correct error: "^msg^": reported.");thy)
                          else error"Wrong error reported"))
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>update_instance-assert-error\<close>
                       "update meta-attributes of an instance of a document class"
                        (ODL_Meta_Args_Parser.attributes_upd -- Parse.document_source
                         >> (Toplevel.theory o update_instance_command)); 

val _ = 
  let fun create_and_check_docitem (((binding,cid_pos),doc_attrs),src) thy =
                  (Value_Command.Docitem_Parser.create_and_check_docitem
                          {is_monitor = false} {is_inline=true}
                          {define = false} binding (cid_pos) (doc_attrs) thy)
                   handle ERROR msg => (if error_match src msg 
                          then (writeln ("Correct error: "^msg^": reported.");thy)
                          else error"Wrong error reported")
  in  Outer_Syntax.command \<^command_keyword>\<open>declare_reference-assert-error\<close>
                           "declare document reference"
                           (ODL_Meta_Args_Parser.attributes -- Parse.document_source
                            >> (Toplevel.theory o create_and_check_docitem))
  end;


val _ =
  let fun pass_trans_to_value_cmd (args, (((name, modes), t),src)) trans  =
      let val pos = Toplevel.pos_of trans
      in trans |> Toplevel.theory
                  (fn thy => Value_Command.value_cmd {assert=false} args name modes t pos thy
                   handle ERROR msg => (if error_match src msg 
                                        then (writeln ("Correct error: "^msg^": reported."); thy)
                                        else error"Wrong error reported"))
      end
  in  Outer_Syntax.command \<^command_keyword>\<open>value-assert-error\<close> "evaluate and print term"
       (ODL_Meta_Args_Parser.opt_attributes -- 
          (Value_Command.opt_evaluator 
           -- Value_Command.opt_modes 
           -- Parse.term 
           -- Parse.document_source) 
        >> (pass_trans_to_value_cmd))
  end;

val _ =
  let fun definition_cmd' meta_args_opt decl params prems spec src bool ctxt =
        Local_Theory.background_theory (Value_Command.meta_args_exec meta_args_opt) ctxt
        |> (fn ctxt => Definition_Star_Command.definition_cmd decl params prems spec bool ctxt
        handle ERROR msg => if error_match src msg 
                             then (writeln ("Correct error: "^msg^": reported.")
                                  ; pair "Bound 0" @{thm refl}
                                    |> pair (Bound 0)
                                    |> rpair ctxt)
                             else error"Wrong error reported")
  in
  Outer_Syntax.local_theory' \<^command_keyword>\<open>definition-assert-error\<close> "constant definition"
    (ODL_Meta_Args_Parser.opt_attributes --
      (Scan.option Parse_Spec.constdecl -- (Parse_Spec.opt_thm_name ":" -- Parse.prop) --
        Parse_Spec.if_assumes -- Parse.for_fixes -- Parse.document_source)
     >> (fn (meta_args_opt, ((((decl, spec), prems), params), src)) => 
                                    #2 oo definition_cmd' meta_args_opt decl params prems spec src))
  end;


val _ =
  let fun add_doc_class_cmd' ((((overloaded, hdr), (parent, attrs)),((rejects,accept_rex),invars)), src) =
        (fn thy => OntoParser.add_doc_class_cmd {overloaded = overloaded} hdr parent attrs rejects accept_rex invars thy
         handle ERROR msg => (if error_match src msg 
                                        then (writeln ("Correct error: "^msg^": reported."); thy)
                                        else error"Wrong error reported"))
  in
  Outer_Syntax.command \<^command_keyword>\<open>doc_class-assert-error\<close> 
                       "define document class"
                        ((OntoParser.parse_doc_class -- Parse.document_source)
                         >> (Toplevel.theory o add_doc_class_cmd'))
  end

val _ =
  Outer_Syntax.command ("text-latex", \<^here>) "formal comment (primary style)"
    (Parse.opt_target -- Parse.document_source >> document_command2 {markdown = true});

\<close>

(* a little auto-test *)
text-latex\<open>dfg\<close>

text-assert-error[aaaa::A]\<open> @{A \<open>sdf\<close>}\<close>\<open>reference ontologically inconsistent\<close>

end
