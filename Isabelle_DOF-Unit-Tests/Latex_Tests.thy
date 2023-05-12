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

chapter\<open>LaTeX Generation Tests\<close>


theory   Latex_Tests
  imports    "TestKit"
             "Isabelle_DOF_Unit_Tests_document"  
  keywords   "Figure*"          :: document_body  (* still experimental feature *)

begin


section\<open>Test Purpose.\<close>
text\<open> Testing the generation of LaTeX code. Serves in particular during development. \<close>

text\<open>Output status:\<close>
print_doc_classes
print_doc_items


section\<open>Elementary Creation of Doc-items and Access of their Attibutes\<close>


text\<open>And here a tex - text macro.\<close>
text\<open>Pythons ReStructuredText (RST). 
     @{url \<open>https://de.wikipedia.org/wiki/ReStructuredText\<close>}. Tool: Sphinx.
    \<close>

text*[aaaa::B]\<open>dfg @{thm [display] refl}\<close>
                            
text-[dfgdfg::B]
\<open> Lorem ipsum ...  @{thm [display] refl}  Frédéric \textbf{TEST} \verb+sdf+ \<open>dfgdfg\<close>  \<close>

text-latex\<open> Lorem ipsum ...  @{thm [display] refl}  Frédéric \textbf{TEST} \verb+sdf+ \<open>dfgdfg\<close>  \<close>

text-[asd::B]
\<open>... and here is its application macro expansion: 
     @{B [display] "dfgdfg"} 
     \textbf{TEST}
     @{cartouche [display] 
         \<open>text*[dfgdfg::B]
           \<open> Lorem ipsum ...  @{thm refl} Frederic \textbf{TEST} \verb+sdf+ \<open>dfgdfg\<close>  \<close>
          \<close>}
\<close>

text-latex\<open>... and here is its application macro expansion: 
     @{B [display] "dfgdfg"} 
     \textbf{TEST}
     @{cartouche [display] 
         \<open>text*[dfgdfg::B]
           \<open> Lorem ipsum ...  @{thm refl}  Fr\'ed\'eric \textbf{TEST} \verb+sdf+ \<open>dfgdfg\<close>  \<close>
          \<close>}\<close>

text-latex\<open> \<^theory_text>\<open>definition df = ...  
        \<close>
       @{ML      [display] \<open> let val x = 3 + 4 in true end 
                           \<close>}

       @{ML_text [display] \<open> val x = ...  
                           \<close>}

       @{verbatim [display] \<open> Lorem ipsum ...  @{thm refl} 
                              Fr\'ed\'eric \textbf{TEST} \verb+sdf+ \<open>dfgdfg\<close> \<close>}
       @{theory_text [display] \<open>definition df = ... \<lambda>x.  
                               \<close>}
       @{cartouche [display]   \<open> @{figure "cfgdfg"}\<close>} \<close>

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

text-latex\<open> \<^doof> \<^LATEX> \<close>

(* the same effect is achieved with : *)
setup \<open>DOF_lib.define_shortcut (Binding.make("bla",\<^here>)) "\\blabla"\<close>
(* Note that this assumes that the generated LaTeX macro call "\blabla" is defined somewhere in the
   target document, for example, in the tex prelude. Note that the "Binding.make" can be avoided
   using the alternative \<^binding> notation (see above).*)


setup\<open>DOF_lib.define_macro (Binding.make("blong",\<^here>)) "\\blong{" "}" (K(K()))\<close>

(*<*)
text-latex\<open> \<^blong>\<open>asd\<close> outer  \<^blong>\<open>syntax| ! see {syntax, outer}\<close> \<close>
(*>*)

section\<open>Experimental Code and Test of advanced LaTeX for free-form text units\<close>

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
  Document_Output.antiquotation_raw_embedded name (Scan.lift Parse.embedded_input)
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
  Thy_Output.antiquotation_raw_embedded name (Scan.lift Parse.embedded_input)
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
  Thy_Output.antiquotation_raw_embedded name (Scan.lift Parse.embedded_input)
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
(*<*)
text-latex\<open> 
      @{boxed_cartouche   [display] \<open>definition dfg = \<lambda>x. x\<close>}
      @{boxed_theory_text [display] \<open>doc_class dfg = \<lambda>x... \<Gamma>\<close>}  \<close>
(*>*)



section\<open>Experimental Section for Multiple Figure Content\<close>

ML\<open>

val thy_output_display = Attrib.setup_option_bool ("thy_output_display", \<^here>);

val caption_param = Config.declare_string ("caption", \<^here>) (K "");
val width_param   = Config.declare_int    ("width", \<^here>)   (K 80);  \<comment> \<open>char per line\<close>
val scale_param   = Config.declare_int    ("scale", \<^here>)   (K 100); \<comment> \<open>in percent\<close>

Config.put caption_param;
Config.put_global;
Config.get ;

(*
      Latex.string (enclose "[" "]" (String.concat [ label_and_type, ", args={", (commas str_args), "}"]))
*)

(*
\begin{figure}[h]
     \centering

     \includegraphics[scale=0.5]{graph_a}
     \caption{An example graph}

     \label{fig:x cubed graph}
\end{figure}


\begin{figure}
     \centering

     \begin{subfigure}[b]{0.3\textwidth}

         \centering
         \includegraphics[width=\textwidth]{graph1}
         \caption{$y=x$}

         \label{fig:y equals x}   (* PROBLEM *)
     \end{subfigure}

     \hfill

     \begin{subfigure}[b]{0.3\textwidth}

         \centering
         \includegraphics[width=\textwidth]{graph2}
         \caption{$y=3sinx$}

         \label{fig:three sin x}  (* PROBLEM *)
     \end{subfigure}

     \hfill

     \begin{subfigure}[b]{0.3\textwidth}

         \centering
         \includegraphics[width=\textwidth]{graph3}
         \caption{$y=5/x$}

         \label{fig:five over x} (* PROBLEM *)
     \end{subfigure}

  \caption{Three simple graphs}
  \label{fig:three graphs}
\end{figure}


\begin{wrapfigure}{l}{0.5\textwidth}

     \centering
     \includegraphics[width=1.5cm]{logo.png}
     \caption{$y=5/x$}

\end{wrapfigure}

*)

datatype figure_type   = single | subfigure | float_embedded

(* to check if this can be done more properly: user-state or attributes ??? *)
val figure_mode        = Unsynchronized.ref(float_embedded)
val figure_label       = Unsynchronized.ref(NONE:string option)
val figure_proportions = Unsynchronized.ref([]:int list)
(* invariant : !figure_mode = subfigure_embedded ==> length(!figure_proportions) > 1 *)

fun figure_antiq (check: Proof.context -> Path.T option -> Input.source -> Path.T) =
  Args.context -- Scan.lift Parse.path_input >> (fn (ctxt, source) =>
   (check ctxt NONE source;
    let val cap = Config.get ctxt caption_param
        val cap_txt = if cap = "" then "" else (Library.enclose "\n\\caption{" "}\n" cap)
                      \<comment> \<open>this is naive. one should add an evaluation of doc antiquotations here\<close>
        val wdth= Config.get ctxt width_param
        val wdth_ltx = (if wdth = 100 then "" 
                       else if 10<=wdth andalso wdth<=99 
                            then "width=0."^(Int.toString wdth)
                            else if 1<=wdth then "width=0.0"^(Int.toString wdth)
                                 else error "width out of range (must be between 1 and 100"
                       )^"\\textwidth"
        val scl = Config.get ctxt scale_param
        val scl_ltx = if scl = 100 then "" 
                       else if 10<=scl andalso scl<=99 then "scale=0."^(Int.toString scl)
                            else if 1<=scl then "scale=0.0"^(Int.toString scl)
                                 else error "scale out of range (must be between 1 and 100"
        val fig_args = Library.enclose "[" "]" (commas [wdth_ltx,scl_ltx])
        val _ = writeln cap
        fun proportion () = "0."^ (Int.toString (100 div List.length(!figure_proportions)))
                             \<comment> \<open>naive: assumes equal proportions\<close>
        fun core arg = "\n\\centering\n"
                       ^"\\includegraphics"
                       ^fig_args^(Library.enclose "{" "}" arg)
                       ^cap_txt
                       \<comment> \<open>add internal labels here\<close>
        fun pat arg = case !figure_mode of
                       single => core arg   
                      |subfigure =>   "\n\\begin{subfigure}[b]{"^proportion ()^"\\textwidth}"
                                     ^ core arg 
                                     ^"\n\\end{subfigure}\n"
                      |float_embedded => "\n\\begin{wrapfigure}{r}{"^wdth_ltx^"}"
                                         ^ core arg 
                                         ^"\n\\end{wrapfigure}\n"
                   
    in   (Latex.output_ascii_breakable "/" (Input.string_of source))
        |> pat
        |> Latex.string
    end));

val _ = Theory.setup
 (Document_Antiquotation.setup_option \<^binding>\<open>width\<close> 
       (Config.put width_param o Document_Antiquotation.integer) #>
  Document_Antiquotation.setup_option \<^binding>\<open>scale\<close> 
       (Config.put scale_param o Document_Antiquotation.integer) #>
  Document_Antiquotation.setup_option \<^binding>\<open>caption\<close> 
       (Config.put caption_param) #>
  Document_Output.antiquotation_raw_embedded \<^binding>\<open>figure_content\<close> 
       (figure_antiq Resources.check_file) (K I)

 );
\<close>

(*<*)
text-latex\<open>
@{figure_content [width=40, scale=35, caption="This is a test"] "ROOT"}
\<close>
(*>*)
ML\<open>

fun gen_enriched_document_command3 name {body} cid_transform attr_transform markdown
                                  (((((oid,pos),cid_pos), doc_attrs) : ODL_Meta_Args_Parser.meta_args_t,
                                     xstring_opt:(xstring * Position.T) option),
                                    toks:Input.source list)
= gen_enriched_document_command2 name {body=body} cid_transform attr_transform markdown
                                  (((((oid,pos),cid_pos), doc_attrs) : ODL_Meta_Args_Parser.meta_args_t,
                                     xstring_opt:(xstring * Position.T) option),
                                     toks) \<comment> \<open>Hack : drop second and thrd args.\<close>

val _ =
  Outer_Syntax.command ("Figure*", @{here}) "multiple figure"
    (ODL_Meta_Args_Parser.attributes -- Parse.opt_target -- Scan.repeat1 Parse.document_source 
      >> (Toplevel.theory o (gen_enriched_document_command2 "TTT" {body=true} I I {markdown = true} )));


\<close>
(*
Figure*[fff::figure,src="\<open>this is a side-by-side\<close>"]
   \<open>@{figure_content [width=40, scale=35, caption="This is a test"] "ROOT"}\<close> 
   \<open> \<^doof> \<^LATEX> \<close>  
   \<open> \<^theory_text>\<open>definition df = ... \<close>
     @{ML        [display]   \<open> let val x = 3 + 4 in true end\<close>}
     @{cartouche [display]   \<open> @{figure "cfgdfg"}\<close>}
   \<close>  
*)


(*<*)

Figure*[figxxx::float,main_caption="\<open>Proofs establishing an Invariant Preservation.\<close>"]
\<open>  @{fig_content (width=40, height=35, caption="This is a right test") "figures/A.png"}  
   @{fig_content (width=40, height=35, caption="This is a left \<^term>\<open>\<sigma>\<^sub>i + 1\<close> test") "figures/A.png"} 
\<close>



(* proposed syntax for sub-figure labels : text\<open> @{figure "ffff(2)"}\<close> *)

Figure*[figxxxx::float,main_caption="\<open>Proofs establishing an Invariant Preservation.\<close>"]
\<open>@{boxed_theory_text [display]
\<open>lemma inv_c2_preserved :  "c2_inv \<sigma> \<Longrightarrow> c1_inv (\<sigma> \<langle>Hardware\<rangle>\<^sub>C\<^sub>o\<^sub>m\<^sub>p\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>H\<^sub>a\<^sub>r\<^sub>d\<^sub>w\<^sub>a\<^sub>r\<^sub>e)"
  unfolding c1_inv_def c2_inv_def 
            Computer_Hardware_to_Hardware_morphism_def
            Product_to_Component_morphism_def  
  by (auto simp: comp_def)

lemma Computer_Hardware_to_Hardware_total :
         "Computer_Hardware_to_Hardware_morphism ` ({X. c2_inv X}) 
      \<subseteq> ({X::Hardware. c1_inv X})"
  using inv_c2_preserved by auto\<close>}\<close> 

end
(*>*)
