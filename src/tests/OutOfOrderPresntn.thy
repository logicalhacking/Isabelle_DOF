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

theory 
  OutOfOrderPresntn
imports 
  "Isabelle_DOF.Conceptual"
keywords "text-" "textN"    :: document_body 
begin

section\<open>Elementary Creation of Doc-items and Access of their Attibutes\<close>


text\<open>Current status:\<close>
print_doc_classes
print_doc_items

(* this corresponds to low-level accesses : *)
ML\<open>  
val {docobj_tab={tab = docitem_tab, ...},docclass_tab, ISA_transformer_tab, monitor_tab,...} 
    = DOF_core.get_data @{context};
Symtab.dest docitem_tab;
Symtab.dest docclass_tab;
\<close>



ML\<open> 
Pure_Syn.document_command;

val _ = Thy_Output.output_document

fun gen_enriched_document_command2 cid_transform attr_transform 
                                  markdown  
                                  (((((oid,pos),cid_pos), doc_attrs) : ODL_Command_Parser.meta_args_t,
                                     xstring_opt:(xstring * Position.T) option),
                                    toks:Input.source) 
                                  : theory -> theory =
  let  val toplvl = Toplevel.theory_toplevel

       (* as side-effect, generates markup *)
       fun check_n_tex_text thy = let val ctxt = Toplevel.presentation_context (toplvl thy);
                                      val pos = Input.pos_of toks;
                                      val _ =   Context_Position.reports ctxt
                                                [(pos, Markup.language_document (Input.is_delimited toks)),
                                                 (pos, Markup.plain_text)];

                                      val text = Thy_Output.output_document 
                                                                 (Proof_Context.init_global thy) 
                                                                 markdown toks

                                      val file = {path = Path.make [oid ^ "_snippet.tex"],
                                                  pos = @{here}, 
                                                  content = Latex.output_text text}
 
                                     val _ = Generated_Files.write_file (Path.make ["latex_test"]) 
                                                                         file
                                      val _ = writeln (Latex.output_text text)
                                  in  thy end
       
       (* ... generating the level-attribute syntax *)
  in   
       (   ODL_Command_Parser.create_and_check_docitem 
                              {is_monitor = false} {is_inline = false} 
                              oid pos (cid_transform cid_pos) (attr_transform doc_attrs)
        #>  check_n_tex_text ) 
  end;

val _ =
  Outer_Syntax.command ("text-", @{here}) "formal comment macro"
    (ODL_Command_Parser.attributes -- Parse.opt_target -- Parse.document_source 
      >> (Toplevel.theory o (gen_enriched_document_command2 I I {markdown = true} )));

(* copied from Pure_syn for experiments *)

fun output_document2 state markdown txt =
  let
    val ctxt = Toplevel.presentation_context state;
    val pos = Input.pos_of txt;
    val _ =
      Context_Position.reports ctxt
        [(pos, Markup.language_document (Input.is_delimited txt)),
         (pos, Markup.plain_text)];
    val txt' = Thy_Output.output_document ctxt markdown txt
    val _ = writeln (Latex.output_text txt')
  in Thy_Output.output_document ctxt markdown txt end;

fun document_command2 markdown (loc, txt) =
  Toplevel.keep (fn state =>
                    (case loc of
                      NONE => ignore (output_document2 state markdown txt)
                    | SOME (_, pos) =>
                        error ("Illegal target specification -- not a theory context" 
                               ^ Position.here pos))) 
 o 
  Toplevel.present_local_theory loc 
                (fn state => ignore (output_document2 state markdown txt));


val _ =
  Outer_Syntax.command ("textN", \<^here>) "formal comment (primary style)"
    (Parse.opt_target -- Parse.document_source >> document_command2 {markdown = true});


\<close>


text\<open>And here a tex - text macro.\<close>
text\<open>Pythons reStructuredText (RST). @{url \<open>https://de.wikipedia.org/wiki/ReStructuredText\<close>}.
Tool: Sphinx.

\<close>

text*[aaa::B]\<open>dfg\<close>

text-[dfgdfg::B]
\<open> Lorem ipsum ...  @{thm [display] refl} _ Frédéric \textbf{TEST} \verb+sdf+ \<open>dfgdfg\<close>  \<close>

textN\<open> Lorem ipsum ...  @{thm [display] refl} _ Frédéric \textbf{TEST} \verb+sdf+ \<open>dfgdfg\<close>  \<close>

text-[asd::B]
\<open>... and here is its application macro expansion: 
     @{B [display] "dfgdfg"} 
     \textbf{TEST}
     @{cartouche [display] 
         \<open>text*[dfgdfg::B]
           \<open> Lorem ipsum ...  @{thm refl} _ Frédéric \textbf{TEST} \verb+sdf+ \<open>dfgdfg\<close>  \<close>
          \<close>}
\<close>

textN\<open>... and here is its application macro expansion: 
     @{B [display] "dfgdfg"} 
     \textbf{TEST}
     @{cartouche [display] 
         \<open>text*[dfgdfg::B]
           \<open> Lorem ipsum ...  @{thm refl} _ Frédéric \textbf{TEST} \verb+sdf+ \<open>dfgdfg\<close>  \<close>
          \<close>}\<close>

textN\<open> \<^theory_text>\<open>definition df = ...  
        \<close>
       @{theory_text [display] \<open>definition df = ...  
                               \<close>}
       @{cartouche [display]   \<open> @{figure "cfgdfg"}\<close>} \<close>

(*<*)
text\<open>Final Status:\<close>
print_doc_items
print_doc_classes 

end
(*>*)
