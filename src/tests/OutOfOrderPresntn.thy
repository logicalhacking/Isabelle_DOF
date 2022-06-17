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

ML\<open>open Document_Output;\<close>
ML\<open>open XML; XML.string_of\<close>

ML\<open> 

val _ = Document_Output.document_output

fun gen_enriched_document_command2 name {body} cid_transform attr_transform markdown
                                  (((((oid,pos),cid_pos), doc_attrs) : ODL_Meta_Args_Parser.meta_args_t,
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
                                                  content = strg}
                                      
                                      val _ = Generated_Files.write_file (Path.make ["latex_test"]) 
                                                                         file
                                      val _ = writeln (strg)
                                  in  thy end
       
       (* ... generating the level-attribute syntax *)
  in   
       (   Value_Command.Docitem_Parser.create_and_check_docitem 
                              {is_monitor = false} {is_inline = false} 
                              oid pos (cid_transform cid_pos) (attr_transform doc_attrs)
        #>  check_n_tex_text ) 
  end;

val _ =
  Outer_Syntax.command ("text-", @{here}) "formal comment macro"
    (ODL_Meta_Args_Parser.attributes -- Parse.opt_target -- Parse.document_source 
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
                    | SOME (_, pos) =>
                        error ("Illegal target specification -- not a theory context" 
                               ^ Position.here pos))) 
 o 
  Toplevel.present_local_theory loc 
                (fn state =>  (output_document2 state markdown txt));


val _ =
  Outer_Syntax.command ("textN", \<^here>) "formal comment (primary style)"
    (Parse.opt_target -- Parse.document_source >> document_command2 {markdown = true});


\<close>


text\<open>And here a tex - text macro.\<close>
text\<open>Pythons reStructuredText (RST). @{url \<open>https://de.wikipedia.org/wiki/ReStructuredText\<close>}.
Tool: Sphinx.

\<close>

text*[aaaa::B]\<open>dfg @{thm [display] refl}\<close>
                            
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
       @{ML      [display] \<open> let val x = 3 + 4 in true end 
                           \<close>}

       @{ML_text [display] \<open> val x = ...  
                           \<close>}

       @{verbatim [display] \<open> Lorem ipsum ...  @{thm refl} _ 
                              Frédéric \textbf{TEST} \verb+sdf+ \<open>dfgdfg\<close> \<close>}
       @{theory_text [display] \<open>definition df = ... \<lambda>x.  
                               \<close>}
       @{cartouche [display]   \<open> @{figure "cfgdfg"}\<close>} \<close>

(*<*)
text\<open>Final Status:\<close>
print_doc_items
print_doc_classes 

section\<open>Experiments on Inline-Textelements\<close>
text\<open>Std Abbreviations. Inspired by the block *\<open>control spacing\<close> 
     in @{file \<open>$ISABELLE_HOME/src/Pure/Thy/document_antiquotations.ML\<close>}.
     We mechanize the table-construction and even attach the LaTeX 
     quirks to be dumped into the prelude.  \<close>

ML\<open>
val _ =
  Theory.setup
   (   Document_Output.antiquotation_raw \<^binding>\<open>doof\<close> (Scan.succeed ())
          (fn _ => fn () => Latex.string "\\emph{doof}")
    #> Document_Output.antiquotation_raw \<^binding>\<open>LATEX\<close> (Scan.succeed ())
          (fn _ => fn () => Latex.string "\\textbf{LaTeX}") 
   )
\<close>

textN\<open> \<^doof> \<^LATEX> \<close>

(* the same effect is achieved with : *)
setup \<open>DOF_lib.define_shortcut (Binding.make("bla",\<^here>)) "\\blabla"\<close>
(* Note that this assumes that the generated LaTeX macro call "\blabla" is defined somewhere in the
   target document, for example, in the tex prelude. Note that the "Binding.make" can be avoided
   using the alternative \<^binding> notation (see above).*)


setup\<open>DOF_lib.define_macro (Binding.make("blong",\<^here>)) "\\blong{" "}" (K(K()))\<close>

textN\<open> \<^blong>\<open>asd\<close> outer  \<^blong>\<open>syntax| ! see {syntax, outer}\<close> \<close>

ML\<open>

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
        |> Document_Output.output_source ctxt
        |> Document_Output.isabelle ctxt

fun string_2_theory_text_antiquotation ctxt text =
      let
        val keywords = Thy_Header.get_keywords' ctxt;
      in
        prepare_text ctxt text
        |> Token.explode0 keywords
        |> maps (Document_Output.output_token ctxt)
        |> Document_Output.isabelle ctxt
      end

fun gen_text_antiquotation name reportNcheck compile =
  Document_Output.antiquotation_raw_embedded name (Scan.lift Args.text_input)
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
  then Latex.environment block_env body
  else body;


fun boxed_text_antiquotation name (* redefined in these more abstract terms *) =
    gen_text_antiquotation name report_text 
                           (fn ctxt => string_2_text_antiquotation ctxt
                                       #> enclose_env ctxt "isarbox")


fun boxed_theory_text_antiquotation name (* redefined in these more abstract terms *) =
    gen_text_antiquotation name report_theory_text 
                           (fn ctxt => string_2_theory_text_antiquotation ctxt 
                                        #> enclose_env ctxt "isarbox")


(*   #> enclose_env ctxt "isarbox" *)

val _ = Theory.setup
   (std_text_antiquotation          \<^binding>\<open>my_text\<close> #>
    boxed_text_antiquotation        \<^binding>\<open>boxed_text\<close> #>
    std_text_antiquotation          \<^binding>\<open>my_cartouche\<close> #>
    boxed_text_antiquotation        \<^binding>\<open>boxed_cartouche\<close> #>
    std_theory_text_antiquotation   \<^binding>\<open>my_theory_text\<close>#>
    boxed_theory_text_antiquotation \<^binding>\<open>boxed_theory_text\<close>); (* is overriding possible ?*)

\<close>

textN\<open> 
      @{boxed_cartouche  [display]  \<open>definition dfg = \<lambda>x. x\<close>}
      @{boxed_theory_text [display] \<open>doc_class dfg = \<lambda>x... \<Gamma>\<close>}  \<close>
               
end
(*>*)
