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
keywords "text-" "text-latex"    :: document_body
    and  "text-assert-error":: document_body

begin

section\<open>Elementary Creation of Doc-items and Access of their Attibutes\<close>


text\<open>Current status:\<close>
print_doc_classes
print_doc_items

(* this corresponds to low-level accesses : *)
ML\<open>
val docitem_tab = DOF_core.get_instances \<^context>;
val isa_transformer_tab = DOF_core.get_isa_transformers \<^context>;
val docclass_tab = DOF_core.get_onto_classes \<^context>;

Name_Space.dest_table docitem_tab;
Name_Space.dest_table isa_transformer_tab;
Name_Space.dest_table docclass_tab;
app;
\<close>


ML\<open> 

val _ = Document_Output.document_output

fun gen_enriched_document_command2 name {body} cid_transform attr_transform markdown
                                  (((((oid,pos),cid_pos), doc_attrs) : ODL_Meta_Args_Parser.meta_args_t,
                                     xstring_opt:(xstring * Position.T) option),
                                    toks_list:Input.source list) 
                                  : theory -> theory =
  let  val toplvl = Toplevel.theory_toplevel

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
                                      val file = {path = Path.make [oid ^ "_snippet.tex"],
                                                  pos = @{here}, 
                                                  content = Bytes.string strg}
                                      
                                      val _ = Generated_Files.write_file (Path.make ["latex_test"]) 
                                                                         file
                                      val _ = writeln (strg)
                                  in  () end \<comment> \<open>important observation: thy is not modified.
                                                  This implies that several text block can be 
                                                  processed in parallel in a future, as long
                                                  as they are associated to one meta arg.\<close>
       
       (* ... generating the level-attribute syntax *)
  in   
       (   Value_Command.Docitem_Parser.create_and_check_docitem 
                              {is_monitor = false} {is_inline = false} {define = true}
                              oid pos (cid_transform cid_pos) (attr_transform doc_attrs)
        #> (fn thy => (app (check_n_tex_text thy) toks_list; thy))) 
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
  Toplevel.present_local_theory loc                           
                (fn state =>  (output_document2 state markdown txt));

fun document_command3 markdown (loc, txt) trns = (document_command2 markdown (loc, txt) trns
                                                  handle exn => ((writeln "AAA"); trns))

fun gen_enriched_document_command3 assert name body cid_transform attr_transform markdown
                                  (((((oid,pos),cid_pos), doc_attrs) : ODL_Meta_Args_Parser.meta_args_t,
                                     xstring_opt:(xstring * Position.T) option),
                                    src_list:Input.source list) thy
 = (gen_enriched_document_command2 name body cid_transform attr_transform markdown 
                                  (((((oid,pos),cid_pos), doc_attrs), xstring_opt), src_list) 
                                  thy)
   handle ERROR str => (if assert src_list str then (writeln ("Correct error:"^str^":reported.");thy)
                                               else error"Wrong error reported")

fun  error_match [_, src] str = (String.isPrefix (Input.string_of src) str)
   | error_match _ _ = error "Wrong assertion format: <arg><match> required"


val _ =
  Outer_Syntax.command ("text-assert-error", @{here}) "formal comment macro"
    (ODL_Meta_Args_Parser.attributes -- Parse.opt_target -- Scan.repeat1 Parse.document_source 
      >> (Toplevel.theory o (gen_enriched_document_command3 error_match "TTT" {body=true}
                                                            I I {markdown = true}) 
                            ));


val _ =
  Outer_Syntax.command ("text-latex", \<^here>) "formal comment (primary style)"
    (Parse.opt_target -- Parse.document_source >> document_command2 {markdown = true});


\<close>

(* auto-tests *)
text-latex\<open>  dfg\<close>

text-assert-error[aaaa::A]\<open> @{A \<open>sdf\<close>}\<close>\<open>reference ontologically inconsistent\<close>


end
(*>*)
