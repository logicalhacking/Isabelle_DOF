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
keywords "text-"     :: document_body 
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

fun output_document state markdown src =
  let
    val ctxt = Toplevel.presentation_context state;
    val _ = Context_Position.report ctxt
                (Input.pos_of src) 
                (Markup.language_document (Input.is_delimited src));
  in Thy_Output.output_document ctxt markdown src end;
  (* this thing converts also source to (latex) text ... *)

output_document : Toplevel.state -> {markdown: bool} -> Input.source -> Latex.text list;


fun gen_enriched_document_command2 cid_transform attr_transform 
                                  markdown  
                                  (((((oid,pos),cid_pos), doc_attrs) : ODL_Command_Parser.meta_args_t,
                                     xstring_opt:(xstring * Position.T) option),
                                    toks:Input.source) 
                                  : theory -> theory =
  let  val toplvl = Toplevel.theory_toplevel

       (* as side-effect, generates markup *)
       fun check_n_tex_text thy = let val text = output_document (toplvl thy) markdown toks
                                      val file = {path = Path.make [oid ^ "_snippet.tex"], 
                                                  pos = @{here}, 
                                                  content =  Latex.output_text text}
                                      val _ = Generated_Files.write_file (Path.make ["latex_test"]) file
                                      val _ = writeln (Latex.output_text text)
                                  in  thy end
       
       (* ... generating the level-attribute syntax *)
  in   
       (   ODL_Command_Parser.create_and_check_docitem false oid pos (cid_transform cid_pos) (attr_transform doc_attrs) 
        #>  check_n_tex_text ) 
  end;

val _ =
  Outer_Syntax.command ("text-", @{here}) "formal comment macro"
    (ODL_Command_Parser.attributes -- Parse.opt_target -- Parse.document_source 
      >> (Toplevel.theory o (gen_enriched_document_command2 I I {markdown = true} )));

\<close>


text\<open>And here a tex - text macro.\<close>

text-[dfgdfg::B]\<open> Lorem ipsum ...  @{thm refl} \<close>

(*<*)
text\<open>Final Status:\<close>
print_doc_items
print_doc_classes 

end
(*>*)
