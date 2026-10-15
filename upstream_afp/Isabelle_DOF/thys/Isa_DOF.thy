(*************************************************************************
 * Copyright (C) 
 *               2019-2022 The University of Exeter 
 *               2018-2022 The University of Paris-Saclay
 *               2018      The University of Sheffield
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

chapter \<open>The Document Ontology Framework for Isabelle\<close>

text\<open> Offering 
\<^item> text-elements that can be annotated with meta-information
\<^item> typed links to text-elements via specifically generated anti-quotations
\<^item> typed structure of this meta-information specifiable in an Ontology-Language ODL
  providing syntax and PIDE support of document classes 
\<^item> inner-syntax-antiquotations (ISA's) allowing to reference Isabelle-entities such as 
  types, terms, theorems inside the meta-information
\<^item> monitors allowing to enforce a specific textual structure of an Isabelle Document
\<^item> a basic infrastructure to define class invariants
  (for continuous checking of meta-information side-conditions of text-elements 
\<^item> LaTeX support. \<close> 
  
text\<open> In this section, we develop on the basis of a management of references Isar-markups
that provide direct support in the PIDE framework. \<close> 
  
theory Isa_DOF                (* Isabelle Document Ontology Framework *)
  imports  Isa_DOF_ODL        (* the framework: core, annotations, instances, antiquotations, ODL *)

  keywords "define_shortcut*"   "define_macro*"            :: thy_decl
  and      "use_template" "use_ontology"                   :: thy_decl
  and      "define_template" "define_ontology"             :: thy_load
  and      "list_ontologies" "list_templates"              :: diag

begin

section\<open>Shortcuts, Macros, Environments\<close>
text\<open>The features described in this section are actually \<^emph>\<open>not\<close> real ISADOF features, rather a 
slightly more abstract layer over somewhat buried standard features of the Isabelle document 
generator ... (Thanks to Makarius) Conceptually, they are \<^emph>\<open>sub-text-elements\<close>. \<close>

text\<open>This module provides mechanisms to define front-end checked:
\<^enum> \<^emph>\<open>shortcuts\<close>, i.e. machine-checked abbreviations without arguments 
  that were mapped to user-defined LaTeX code (Example: \<^verbatim>\<open>\ie\<close>)
\<^enum> \<^emph>\<open>macros\<close>  with one argument that were mapped to user-defined code. Example: \<^verbatim>\<open>\myurl{bla}\<close>.
  The argument can be potentially checked and reports can be sent to PIDE;
  if no such checking is desired, this can be expressed by setting the
  \<^theory_text>\<open>reportNtest\<close>-parameter to \<^theory_text>\<open>K(K())\<close>.
\<^enum> \<^emph>\<open>macros\<close> with two arguments, potentially independently checked. See above. 
  Example: \<^verbatim>\<open>\myurl[ding]{dong}\<close>,
\<^enum> \<^emph>\<open>boxes\<close> which are more complex sub-text-elements in the line of the \<^verbatim>\<open>verbatim\<close> or 
  \<^verbatim>\<open>theory_text\<close> environments.

Note that we deliberately refrained from a code-template definition mechanism for simplicity,
so the patterns were just described by strings.  No additional ado with quoting/unquoting 
mechanisms ... 
\<close>

ML\<open>
structure DOF_lib =
struct
fun define_shortcut name latexshcut = 
       Document_Output.antiquotation_raw name (Scan.succeed ())
          (fn _ => fn () => Latex.string latexshcut) 

(* This is a generalization of the Isabelle2020 function "control_antiquotation" from 
   document_antiquotations.ML. (Thanks Makarius!) *)
fun define_macro name s1 s2 reportNtest =
      Document_Output.antiquotation_raw_embedded name (Scan.lift Args.cartouche_input)
         (fn ctxt => 
             fn src => let val () = reportNtest ctxt src 
                       in  src |>   XML.enclose s1 s2 
                                  o Document_Output.output_document ctxt {markdown = false}
                       end);

local (* hide away really strange local construction *)
fun enclose_body2 front body1 middle body2 post =
  (if front  = "" then [] else Latex.string front) @ body1 @
  (if middle = "" then [] else Latex.string middle) @ body2 @
  (if post   = "" then [] else Latex.string post);
in
fun define_macro2 name front middle post reportNtest1 reportNtest2 =
      Document_Output.antiquotation_raw_embedded name (Scan.lift (   Args.cartouche_input 
                                                             -- Args.cartouche_input))
         (fn ctxt => 
             fn (src1,src2) => let val () = reportNtest1 ctxt src1 
                                   val () = reportNtest2 ctxt src2 
                                   val T1 = Document_Output.output_document ctxt {markdown = false} src1
                                   val T2 = Document_Output.output_document ctxt {markdown = false} src2
                               in  enclose_body2 front T1 middle T2 post
                               end);
end

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

fun std_theory_text_antiquotation name (* redefined in these more abstract terms *) =
    gen_text_antiquotation name report_theory_text string_2_theory_text_antiquotation

fun environment_delim name =
 ("%\n\\begin{" ^ Latex.output_name name ^ "}\n",
  "\n\\end{" ^ Latex.output_name name ^ "}");

fun environment_block name = environment_delim name |-> XML.enclose;

fun enclose_env verbatim ctxt block_env body =
  if Config.get ctxt Document_Antiquotation.thy_output_display
  then if verbatim 
       then environment_block block_env body
       else Latex.environment block_env body
  else XML.enclose ("\\inline"^block_env ^"{") "}" body;

end
\<close>


ML\<open>
local 
val parse_literal = Parse.alt_string || Parse.cartouche
val parse_define_shortcut = Parse.binding -- ((\<^keyword>\<open>\<rightleftharpoons>\<close> || \<^keyword>\<open>==\<close>) |-- parse_literal)
val define_shortcuts = fold(uncurry DOF_lib.define_shortcut)
in
val _ =  Outer_Syntax.command \<^command_keyword>\<open>define_shortcut*\<close> "define LaTeX shortcut"
            (Scan.repeat1 parse_define_shortcut >> (Toplevel.theory o define_shortcuts));
end
\<close>

ML\<open>
val parse_literal = Parse.alt_string || Parse.cartouche
val parse_define_shortcut =  Parse.binding 
                             -- ((\<^keyword>\<open>\<rightleftharpoons>\<close> || \<^keyword>\<open>==\<close>) |-- parse_literal)
                             --|Parse.underscore
                             -- parse_literal
                             -- (Scan.option (\<^keyword>\<open>(\<close> |-- Parse.ML_source --|\<^keyword>\<open>)\<close>))

fun define_macro (X,NONE) = (uncurry(uncurry(uncurry DOF_lib.define_macro)))(X,K(K()))
   |define_macro (X,SOME(_:Input.source)) = 
       let val check_code = K(K()) (* hack *)
           val _ = warning "Checker code support Not Yet Implemented - use ML"
       in  (uncurry(uncurry(uncurry DOF_lib.define_macro)))(X,check_code)
       end;

val _ =  Outer_Syntax.command \<^command_keyword>\<open>define_macro*\<close> "define LaTeX shortcut"
            (Scan.repeat1 parse_define_shortcut >> (Toplevel.theory o (fold define_macro)));

\<close>


section \<open>Document context: template and ontology\<close>

ML \<open>
signature DOCUMENT_CONTEXT =
sig
  val template_space: Context.generic -> Name_Space.T
  val ontology_space: Context.generic -> Name_Space.T
  val print_template: Context.generic -> string -> string
  val print_ontology: Context.generic -> string -> string
  val check_template: Context.generic -> xstring * Position.T -> string * (string * string)
  val check_ontology: Context.generic -> xstring * Position.T -> string * (string * string)
  val define_template: binding * (string * string) -> theory -> string * theory
  val define_ontology: binding * (string * string) -> theory -> string * theory
  val use_template: Context.generic -> xstring * Position.T -> unit
  val use_ontology: Context.generic -> (xstring * Position.T) list -> unit
  val list_ontologies: Context.generic -> unit
  val list_templates: Context.generic -> unit
end;

structure Document_Context: DOCUMENT_CONTEXT =
struct

(* theory data *)

local

structure Data = Theory_Data
(
  type T = (string * string) Name_Space.table * (string * string) Name_Space.table;
  val empty : T =
   (Name_Space.empty_table "document_template",
    Name_Space.empty_table "document_ontology");
  fun merge ((templates1, ontologies1), (templates2, ontologies2)) =
   (Name_Space.merge_tables (templates1, templates2),
    Name_Space.merge_tables (ontologies1, ontologies2));
);

fun naming_context thy =
  Proof_Context.init_global thy
  |> Proof_Context.map_naming (Name_Space.root_path #> Name_Space.add_path "Isabelle_DOF")
  |> Context.Proof;

fun get_space which = Name_Space.space_of_table o which o Data.get o Context.theory_of;

fun print which context =
  Name_Space.markups_extern (Context.proof_of context) (get_space which context)
  #> uncurry Markup.markups;

fun check which context arg =
  Name_Space.check context (which (Data.get (Context.theory_of context))) arg;

fun define (get, ap) (binding, arg) thy =
  let
    val (name, table') =
      Data.get thy |> get |> Name_Space.define (naming_context thy) true (binding, arg);
    val thy' = (Data.map o ap) (K table') thy;
  in (name, thy') end;

fun strip prfx sffx (path, pos) =
  (case try (unprefix prfx) (Path.file_name path) of
    NONE => error ("File name needs to have prefix " ^ quote prfx ^ Position.here pos)
  | SOME a =>
      (case try (unsuffix sffx) a of
        NONE => error ("File name needs to have suffix " ^ quote sffx ^ Position.here pos)
      | SOME b => b));

in


val template_space = get_space fst;
val ontology_space = get_space snd;

val print_template = print fst;
val print_ontology = print snd;

fun check_template context arg = check fst context arg ;
fun check_ontology context arg = check snd context arg ;

val define_template = define (fst, apfst);
val define_ontology = define (snd, apsnd);

fun use_template context arg =
  let val xml = arg |> check_template context |> snd |> fst  |> XML.string
  in Export.export (Context.theory_of context) \<^path_binding>\<open>dof/use_template\<close> xml end;

fun use_ontology context args =
  let
    val xml = args                                       
      |> map (fn a => check_ontology context a |> fst  )
      |> cat_lines |> XML.string;
  in Export.export (Context.theory_of context) \<^path_binding>\<open>dof/use_ontology\<close> xml end;

val strip_template = strip "root-" ".tex";
val strip_ontology = strip "DOF-" ".sty";


fun list cmdN sel which getName context = 
    let 
       fun get arg  =  check sel context arg |> snd |> snd;

       val full_names = map getName ((Name_Space.get_names o which) context)
       val descriptions = map get (map (fn n => (n, Position.none)) full_names) 
       val _ = map (fn (n,d) => writeln ((Active.sendback_markup_command (cmdN^" \""^n^"\""))^": "^d)) 
                   (ListPair.zip (full_names, descriptions))
    in ()  end

fun list_ontologies context = list "use_ontology" snd ontology_space  (fn n => ((Long_Name.base_name o Long_Name.qualifier) n )^"."^(Long_Name.base_name n)) context
fun list_templates context = list "use_template" fst template_space  Long_Name.base_name context

end;


(* Isar commands *)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>use_template\<close>
    "use DOF document template (as defined within theory context)"
    (Parse.position Parse.name >> (fn arg =>
      Toplevel.theory (fn thy => (use_template (Context.Theory thy) arg; thy))));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>use_ontology\<close>
    "use DOF document ontologies (as defined within theory context)"
    (Parse.and_list1 (Parse.position Parse.name) >> (fn args =>
      Toplevel.theory (fn thy => (use_ontology (Context.Theory thy) args; thy))));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>define_template\<close>
    "define DOF document template (via LaTeX root file)"
    (Parse.position (Resources.parse_file -- Parse.name) >>
      (fn ((get_file, desc), pos) => Toplevel.theory (fn thy =>
        let
          val file = get_file thy;
          val binding = Binding.make (strip_template (#src_path file, pos), pos);
          val text = cat_lines (#lines file);
        in #2 (define_template (binding, (text, desc)) thy) end)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>define_ontology\<close>
    "define DOF document ontology (via LaTeX style file)"
    (Parse.position (Resources.parse_file -- Parse.name) >>
      (fn ((get_file, desc), pos) => Toplevel.theory (fn thy =>
        let
          val file = get_file thy;
          val binding = Binding.qualify false (Long_Name.qualifier (Context.theory_long_name thy)) (Binding.make (strip_ontology (#src_path file, pos), pos));
          val text = cat_lines (#lines file);
        in #2 (define_ontology (binding, (text, desc)) thy) end)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>list_templates\<close>
    "list available DOF document templates (as defined within theory context)"
    (Scan.succeed (Toplevel.theory (fn thy => (list_templates (Context.Theory thy); thy))));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>list_ontologies\<close>
    "list available DOF document ontologies (as defined within theory context)"
    (Scan.succeed (Toplevel.theory (fn thy => (list_ontologies (Context.Theory thy); thy))));


end;
\<close>

define_template "../latex/document-templates/root-lncs.tex" 
                "Documents using Springer's LNCS class."
define_template "../latex/document-templates/root-scrartcl.tex" 
                "A simple article layout."
define_template "../latex/document-templates/root-scrreprt-modern.tex" 
                "A 'modern' looking report layout."
define_template "../latex/document-templates/root-scrreprt.tex" 
                "A simple report layout."

section \<open>Isabelle/Scala module within session context\<close>

external_file "../etc/build.props"
external_file "../scala/dof_document_build.scala"


scala_build_generated_files
  external_files
    "build.props" (in "../etc")
  and
    "scala/dof.scala"
    "scala/dof_document_build.scala" (in "../")

end
