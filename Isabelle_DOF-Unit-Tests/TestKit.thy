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

theory 
  TestKit
imports 
  "Isabelle_DOF-Unit-Tests_document"
  "Isabelle_DOF-Ontologies.Conceptual"
keywords "text-" "text-latex"             :: document_body
    and  "text-assert-error"              :: document_body
    and  "update_instance-assert-error"   :: document_body
    and  "declare_reference-assert-error" :: document_body

begin

section\<open>Testing Commands (exec-catch-verify - versions of std commands)\<close>


ML\<open> 

fun gen_enriched_document_command2 name {body} cid_transform attr_transform markdown
                                  ((meta_args,
                                     xstring_opt:(xstring * Position.T) option),
                                    toks_list:Input.source list) 
                                  : theory -> theory =
  let  val toplvl = Toplevel.theory_toplevel
       val (((oid,pos),cid_pos), doc_attrs) = meta_args
       val oid' = if meta_args = ODL_Meta_Args_Parser.empty_meta_args
                  then "output"
                  else oid
       (* as side-effect, generates markup *)
       fun check_n_tex_text thy toks = let val ctxt = Toplevel.presentation_context (toplvl thy);
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
       
       (* ... generating the level-attribute syntax *)
  in   
      (if meta_args = ODL_Meta_Args_Parser.empty_meta_args
              then I
              else
          Value_Command.Docitem_Parser.create_and_check_docitem 
                              {is_monitor = false} {is_inline = false} {define = true}
                              oid pos (cid_transform cid_pos) (attr_transform doc_attrs))
        #> (fn thy => (app (check_n_tex_text thy) toks_list; thy))
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
  Toplevel.keep (fn state =>
                    (case loc of
                      NONE => ignore (output_document2 state markdown txt)
                    | SOME (_, pos) =>(ISA_core.err 
                                           "Illegal target specification -- not a theory context" 
                                           pos))) 
  o 
  Toplevel.present_local_theory loc (fn state => (output_document2 state markdown txt));


fun gen_enriched_document_command3 assert name body trans at md (margs, src_list) thy
 = (gen_enriched_document_command2 name body trans at md  (margs, src_list)  thy)
   handle ERROR msg => (if assert src_list msg then (writeln ("Correct error: "^msg^": reported.");thy)
                                               else error"Wrong error reported")

fun error_match src msg = (writeln((Input.string_of src)); String.isPrefix (Input.string_of src) msg)

fun  error_match2 [_, src] msg = error_match src msg
   | error_match2 _ _ = error "Wrong text-assertion-error. Argument format <arg><match> required."


val _ =
  Outer_Syntax.command ("text-assert-error", @{here}) "formal comment macro"
    (ODL_Meta_Args_Parser.opt_attributes -- Parse.opt_target -- Scan.repeat1 Parse.document_source 
      >> (Toplevel.theory o
          (fn ((meta_args, xstring_opt), source) =>
              (gen_enriched_document_command3 error_match2 "TTT" {body=true}
                                        I I {markdown = true} ((meta_args, xstring_opt), source)))));

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
  let fun create_and_check_docitem ((((oid, pos),cid_pos),doc_attrs),src) thy=
                  (Value_Command.Docitem_Parser.create_and_check_docitem
                          {is_monitor = false} {is_inline=true}
                          {define = false} oid pos (cid_pos) (doc_attrs) thy)
                   handle ERROR msg => (if error_match src msg 
                          then (writeln ("Correct error: "^msg^": reported.");thy)
                          else error"Wrong error reported")
  in  Outer_Syntax.command \<^command_keyword>\<open>declare_reference-assert-error\<close>
                       "declare document reference"
                       (ODL_Meta_Args_Parser.attributes -- Parse.document_source
                        >> (Toplevel.theory o create_and_check_docitem))
  end;



val _ =
  Outer_Syntax.command ("text-latex", \<^here>) "formal comment (primary style)"
    (Parse.opt_target -- Parse.document_source >> document_command2 {markdown = true});

\<close>

(* auto-tests *)
text-latex\<open>dfg\<close>

text-assert-error[aaaa::A]\<open> @{A \<open>sdf\<close>}\<close>\<open>reference ontologically inconsistent\<close>

end
(*>*)
