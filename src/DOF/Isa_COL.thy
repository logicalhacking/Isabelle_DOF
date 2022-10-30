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
  imports  Isa_DOF  
  keywords "title*"        "subtitle*"      
           "chapter*"      "section*"   
           "subsection*"   "subsubsection*" 
           "paragraph*"    "subparagraph*"         
           "figure*"       "side_by_side_figure*" :: document_body 

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
   in Monitor_Command_Parser.gen_enriched_document_cmd {inline=true} I transform end; 

(*
val enriched_document_command_macro = 
    let fun transform_cid X = (writeln (@{make_string} X); X)
    in  gen_enriched_document_command {inline=true} transform_cid I end;
*)


local 
fun transform_cid thy NONE X = X
   |transform_cid thy (SOME ncid) NONE =  (SOME(ncid,@{here}))
   |transform_cid thy (SOME cid) (SOME (sub_cid,pos)) =
                             let val cid_long  = DOF_core.read_cid_global thy cid
                                 val sub_cid_long =  DOF_core.read_cid_global thy sub_cid
                             in  if DOF_core.is_subclass_global thy  sub_cid_long cid_long
                                 then (SOME (sub_cid,pos))
                                 else (* (SOME (sub_cid,pos)) *)
                                      (*  BUG : check reveals problem of Definition* misuse.  *)
                                        error("class "^sub_cid_long^
                                              " must be sub-class of "^cid_long) 
                             end  
in

fun enriched_formal_statement_command ncid (S: (string * string) list) =
   let fun transform_attr doc_attrs = (map (fn(cat,tag) => ((cat,@{here}),tag)) S) @ 
                                      (("formal_results",@{here}),"([]::thm list)")::doc_attrs
   in  fn margs => fn thy =>
          Monitor_Command_Parser.gen_enriched_document_cmd {inline=true} 
                                    (transform_cid thy ncid) transform_attr margs thy 
   end;

fun enriched_document_cmd_exp ncid (S: (string * string) list) =
   (* expands ncid into supertype-check. *)
   let fun transform_attr attrs = (map (fn(cat,tag) => ((cat,@{here}),tag)) S) @ attrs
   in  fn margs => fn thy =>
         Monitor_Command_Parser.gen_enriched_document_cmd {inline=true} (transform_cid thy ncid)
                                                                            transform_attr margs thy
   end;
end (* local *)


fun heading_command (name, pos) descr level =
  Monitor_Command_Parser.document_command (name, pos) descr
    {markdown = false, body = true} (enriched_text_element_cmd level);

val _ = heading_command ("title*", @{here}) "section heading" NONE;
val _ = heading_command ("subtitle*", @{here}) "section heading" NONE;
val _ = heading_command ("chapter*", @{here}) "section heading" (SOME (SOME 0));
val _ = heading_command ("section*", @{here}) "section heading" (SOME (SOME 1));
val _ = heading_command ("subsection*", @{here}) "subsection heading" (SOME (SOME 2));
val _ = heading_command ("subsubsection*", @{here}) "subsubsection heading" (SOME (SOME 3));
val _ = heading_command ("paragraph*", @{here}) "paragraph heading" (SOME (SOME 4));
val _ = heading_command ("subparagraph*", @{here}) "subparagraph heading" (SOME (SOME 5));

end 
end
\<close>

section\<open> Library of Standard Text Ontology \<close>

datatype placement = pl_h  | (*here*) 
                     pl_t  | (*top*)
                     pl_b  | (*bottom*)
                     pl_ht | (*here ->  top*) 
                     pl_hb   (*here ->  bottom*)

ML\<open>(Symtab.defined (#docclass_tab(DOF_core.get_data_global @{theory}))) "side_by_side_figure"\<close>

print_doc_classes


doc_class figure   = 
   relative_width   :: "int"  (* percent of textwidth *)    
   src              :: "string"
   placement        :: placement  
   spawn_columns    :: bool <= True 


doc_class side_by_side_figure = figure +
   anchor           :: "string"
   caption          :: "string"
   relative_width2  :: "int"  (* percent of textwidth *)    
   src2             :: "string"
   anchor2          :: "string"
   caption2         :: "string"

print_doc_classes

doc_class figure_group = 
   (*  trace :: "doc_class rexp list" <= "[]" automatically generated since monitor clause *)
   caption          :: "string"
   rejects             figure_group   (* this forbids recursive figure-groups not supported
                                        by the current LaTeX style-file. *)
   accepts             "\<lbrace>figure\<rbrace>\<^sup>+"

print_doc_classes



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

(*<*)

text\<open>Tests: \<^vs>\<open>-0.14cm\<close>\<close>

ML\<open> check_latex_measure @{context} (Input.string "-0.14 cm") \<close>
define_macro* vs2 \<rightleftharpoons> \<open>\vspace{\<close> _ \<open>}\<close> (check_latex_measure) (* checkers NYI on Isar-level *)
define_macro* hs2 \<rightleftharpoons> \<open>\hspace{\<close> _ \<open>}\<close> (* works fine without checker.*)

(*>*)

subsection\<open>Figures\<close>

ML\<open>open Args\<close>

ML\<open>
(* *********************************************************************** *)
(* Ontological Macro Command Support                                       *)
(* *********************************************************************** *)

val _ = Onto_Macros.heading_command ("figure*", @{here}) "figure" NONE;
val _ = Onto_Macros.heading_command ("side_by_side_figure*", @{here}) "multiple figures" NONE;
\<close>

(*<*)
(*
ML\<open>ML_Context.expression\<close>
fun setup source =
  ML_Context.expression (Input.pos_of source)
    (ML_Lex.read "Theory.setup (" @ ML_Lex.read_source source @ ML_Lex.read ")")
  |> Context.theory_map;
setup\<open>\<close>

*)
(*>*)

subsection\<open>Tables\<close>
(* TODO ! ! ! *)
(* dito the future monitor: table - block *)
(* some studies *)

text\<open>Tables are (sub) document-elements represented inside the documentation antiquotation
language. The used technology is similar to the existing railroad-diagram support 
(cf. \<^url>\<open>https://isabelle.in.tum.de/doc/isar-ref.pdf\<close>, Sec. 4.5). 

However, tables are not directly based on the ideosynchrasies of Knuth-based language design ---

However, tables come with a more abstract structure model than conventional typesetting in the 
LaTeX tradition. It is based of the following principles:
  \<^item> The core unit of a table is a \<^emph>\<open>cell\<close> having a \<^emph>\<open>configuration\<close>, i.e. a
    number of attributes specifying its width, height, borderline, etc. 
    A cell may be \<^emph>\<open>elementary\<close>, i.e. containing structured text or \<^emph>\<open>compound\<close>, 
    i.e. containing a sub-table.
  \<^item> A \<^emph>\<open>table\<close> contains either a list of \<^emph>\<open>rows\<close> or a list of \<^emph>\<open>columns\<close>, which are both
    lists of cells.
  \<^item> The tables, rows and columns posses own configurations.
  \<^item> Concerning the layout, \<^emph>\<open>propagation\<close>  laws of configurations control that 
    information flows top-down from tables to rows or columns, from rows/columns to cells,
    from left to right within rows and from top to bottom in columns; propagation produces
    the desired presentation effect of tables that cells appear somewhat uniform in it. 
  \<^item> Since rows are lists of cells, configurations are also a list of attributes.
    Attributes of the same kind may appear repeatedly. If the sub-list of attributes 
    of the same kind is shorter than the list of cells it is referring to, than
    the last element in this sub-list is duplicated as many times as necessary. This feature
    of configuration propagation is called \<^emph>\<open>filling\<close>.
  \<^item> Lists of rows and lists of cells consists of the same number of cells.
  \<^item> Since propagation and filling induce a congruence relation on table trees, a normalisation
    process is a necessary pre-requisite for the compilation to LaTeX.
\<close>

ML\<open>
local

fun mk_line st1 st2 [a] =  [a @ Latex.string st2]
   |mk_line st1 st2 (a::S) = [a @ Latex.string st1] @ mk_line st1 st2 S;

(* tab attributes for global setup *)

type cell_config =   {cell_placing    : string list, 
                      cell_height     : string list,
                      cell_width      : string list,
                      cell_bgnd_color : string list,
                      cell_line_color : string list,
                      cell_line_width : string list}

val mt_cell_config = {cell_placing   = [],
                      cell_height    = [],    
                      cell_width     = [],    
                      cell_bgnd_color= [], 
                      cell_line_color= [], 
                      cell_line_width= [] }: cell_config

(* doof wie 100 m feldweg. *)
fun upd_cell_placing key 
            {cell_placing,cell_height,cell_width, cell_bgnd_color,   
             cell_line_color,cell_line_width} : cell_config = 
            {cell_placing   = cell_placing @ [key],  cell_height    = cell_height,    
             cell_width     = cell_width,            cell_bgnd_color= cell_bgnd_color, 
             cell_line_color= cell_line_color,       cell_line_width= cell_line_width } 
            : cell_config

fun upd_cell_height num 
            {cell_placing,cell_height,cell_width, cell_bgnd_color,   
             cell_line_color,cell_line_width} : cell_config = 
            {cell_placing   = cell_placing ,  cell_height    = cell_height @ [num],    
             cell_width     = cell_width,     cell_bgnd_color= cell_bgnd_color, 
             cell_line_color= cell_line_color,cell_line_width= cell_line_width } 
            : cell_config

fun upd_cell_width num 
            {cell_placing,cell_height,cell_width, cell_bgnd_color,   
             cell_line_color,cell_line_width} : cell_config = 
            {cell_placing   = cell_placing ,   cell_height    = cell_height,    
             cell_width     = cell_width@[num],cell_bgnd_color= cell_bgnd_color, 
             cell_line_color= cell_line_color, cell_line_width= cell_line_width } 
            : cell_config

fun upd_cell_bgnd_color str 
            {cell_placing,cell_height,cell_width, cell_bgnd_color,   
             cell_line_color,cell_line_width} : cell_config = 
            {cell_placing   = cell_placing ,   cell_height    = cell_height,    
             cell_width     = cell_width,      cell_bgnd_color= cell_bgnd_color@[str], 
             cell_line_color= cell_line_color, cell_line_width= cell_line_width } 
            : cell_config

fun upd_cell_line_color str 
            {cell_placing,cell_height,cell_width, cell_bgnd_color,   
             cell_line_color,cell_line_width} : cell_config = 
            {cell_placing   = cell_placing ,         cell_height    = cell_height,    
             cell_width     = cell_width,            cell_bgnd_color= cell_bgnd_color, 
             cell_line_color= cell_line_color@[str], cell_line_width= cell_line_width } 
            : cell_config

fun upd_cell_line_width num 
            {cell_placing,cell_height,cell_width, cell_bgnd_color,   
             cell_line_color,cell_line_width} : cell_config = 
            {cell_placing    = cell_placing ,   cell_height     = cell_height,    
             cell_width      = cell_width,      cell_bgnd_color = cell_bgnd_color, 
             cell_line_color = cell_line_color, cell_line_width = cell_line_width@[num] } 
            : cell_config


val (tab_cell_placing, tab_cell_placing_setup)
     = Attrib.config_string \<^binding>\<open>tab_cell_placing\<close> (K "center");
val (tab_cell_height, tab_cell_height_setup)
     = Attrib.config_string \<^binding>\<open>tab_cell_height\<close> (K "0.0cm");
val (tab_cell_width, tab_cell_width_setup)
     = Attrib.config_string \<^binding>\<open>tab_cell_width\<close> (K "0.0cm");
val (tab_cell_bgnd_color, tab_cell_bgnd_color_setup)
     = Attrib.config_string \<^binding>\<open>tab_cell_bgnd_height\<close> (K "white");
val (tab_cell_line_color, tab_cell_line_color_setup)
     = Attrib.config_string \<^binding>\<open>tab_cell_line_color\<close> (K "black");
val (tab_cell_line_width, tab_cell_line_width_setup)
     = Attrib.config_string \<^binding>\<open>tab_cell_line_height\<close> (K "0.0cm");

fun default_cell_config ctxt = {cell_placing    = [Config.get ctxt tab_cell_placing],
                                cell_height     = [Config.get ctxt tab_cell_height],    
                                cell_width      = [Config.get ctxt tab_cell_width],    
                                cell_bgnd_color = [Config.get ctxt tab_cell_bgnd_color], 
                                cell_line_color = [Config.get ctxt tab_cell_line_color], 
                                cell_line_width = [Config.get ctxt tab_cell_line_width]}
                              : cell_config


val _ = Theory.setup(   tab_cell_placing_setup
                     #> tab_cell_height_setup
                     #> tab_cell_width_setup
                     #> tab_cell_bgnd_color_setup
                     #> tab_cell_line_color_setup
                     #> tab_cell_line_width_setup
                    )

val cell_placingN    = "cell_placing"
val cell_heightN     = "cell_height" 
val cell_widthN      = "cell_width"
val cell_bgnd_colorN = "cell_bgnd_color" 
val cell_line_colorN = "cell_line_color"
val cell_line_widthN = "cell_line_width" 

val placing_scan = Args.$$$ "left" || Args.$$$ "center" || Args.$$$ "right" 

val color_scan   =   Args.$$$ "none" || Args.$$$ "red" || Args.$$$ "green"                   || Args.$$$ "blue" || Args.$$$ "black"

(*

val _ = Scan.lift 

fun lift scan (st, xs) =
  let val (y, xs') = scan xs
  in (y, (st, xs')) end;

*)

fun tabitem_modes (ctxt, toks) = 
       let val (y, toks') = ((((Scan.optional 
                      (Args.parens 
                         (Parse.list1
                           (   (Args.$$$ cell_placingN |-- Args.$$$ "=" -- placing_scan
                                >> (fn (_, k) => upd_cell_placing k))   
                            || (Args.$$$ cell_heightN |-- Args.$$$ "=" -- parse_latex_measure
                                >> (fn (_, k) => upd_cell_height k))    
                            || (Args.$$$ cell_widthN |-- Args.$$$ "=" -- parse_latex_measure
                                >> (fn (_, k) => upd_cell_width k))    
                            || (Args.$$$ cell_bgnd_colorN |-- Args.$$$ "=" -- color_scan
                                >> (fn (_, k) => upd_cell_bgnd_color k))
                            || (Args.$$$ cell_line_colorN |-- Args.$$$ "=" -- color_scan
                                >> (fn (_, k) => upd_cell_line_color k))
                            || (Args.$$$ cell_line_widthN |-- Args.$$$ "=" -- parse_latex_measure
                                >> (fn (_, k) => upd_cell_line_width k))
                      ))) [K (default_cell_config (Context.the_proof ctxt))]) 
                      : (cell_config -> cell_config) list parser)
                      >> (foldl1 (op #>)))
                      : (cell_config -> cell_config) parser)
                      (toks)
        in (y, (ctxt, toks')) end


datatype table_tree  = mk_tab    of cell_config * cell_group
                     | mk_cell   of cell_config * Input.source
   and   cell_group  = mk_row    of cell_config * table_tree list
                     | mk_column of cell_config * table_tree list
                                             


val tab_config_parser =  tabitem_modes : ((cell_config -> cell_config) ) context_parser
val table_parser =  tab_config_parser -- Scan.repeat1(Scan.repeat1(Scan.lift Args.cartouche_input))

fun table_antiquotation name scan =
  Document_Output.antiquotation_raw_embedded name 
    scan
    (fn ctxt => 
      (fn (cfg_trans,content:Input.source list list) =>
          let val cfg = cfg_trans mt_cell_config
              val _ = writeln ("XXX"^ @{make_string} cfg)
              fun check _ = ()  (* ToDo *)
              val _  = check content
          in  content 
              |> (map(map (Document_Output.output_document ctxt {markdown = false})
                  #> mk_line "&" "\\\\"
                  #> List.concat )
                  #> List.concat)
              |> XML.enclose "\\table[allerhandquatsch]{" "}"
          end
      )
    );

fun cell_antiquotation name scan =
    Document_Output.antiquotation_raw_embedded name 
    scan
    (fn ctxt => 
      (fn (cfg_trans,content:Input.source) => 
          let val cfg = cfg_trans mt_cell_config
              val _ = writeln ("XXX"^ @{make_string} cfg) 
          in  content |> Document_Output.output_document ctxt {markdown = false}
          end
      )
    )

fun row_antiquotation name scan =
    Document_Output.antiquotation_raw_embedded name 
    scan
    (fn ctxt => 
      (fn (cfg_trans,content:Input.source list) => 
          let val cfg = cfg_trans mt_cell_config
              val _ = writeln ("XXX"^ @{make_string} cfg) 
          in  content |> (map (Document_Output.output_document ctxt {markdown = false})
                          #> List.concat)
          end
      )
    )

fun column_antiquotation name scan =
    Document_Output.antiquotation_raw_embedded name 
    scan
    (fn ctxt => 
      (fn (cfg_trans,content:Input.source list) => 
          let val cfg = cfg_trans mt_cell_config
              val _ = writeln ("XXX"^ @{make_string} cfg) 
          in  content |> (map (Document_Output.output_document ctxt {markdown = false})
                          #> List.concat)
          end
      )
    )

in

val _ = Theory.setup 
           (   table_antiquotation  \<^binding>\<open>table_inline\<close> 
                                    table_parser
            #> table_antiquotation  \<^binding>\<open>subtab\<close> table_parser
            #> cell_antiquotation   \<^binding>\<open>cell\<close>   
                                    (tab_config_parser--Scan.lift Args.cartouche_input)
            #> row_antiquotation    \<^binding>\<open>row\<close>  
                                    (tab_config_parser--Scan.repeat1(Scan.lift Args.cartouche_input))  
            #> column_antiquotation \<^binding>\<open>column\<close> 
                                    (tab_config_parser--Scan.repeat1(Scan.lift Args.cartouche_input))
           );

end
\<close>


define_shortcut* clearpage \<rightleftharpoons> \<open>\clearpage{}\<close>
                 hf \<rightleftharpoons> \<open>\hfill\<close> 
                 br \<rightleftharpoons> \<open>\break\<close> 


declare[[tab_cell_placing="left",tab_cell_height="18.0cm"]]

section\<open>Tests\<close>
(*<*)
text\<open> @{table_inline  [display] (cell_placing = center,cell_height =\<open>12.0cm\<close>,
                                 cell_height =\<open>13pt\<close>,  cell_width = \<open>12.0cm\<close>,
                                 cell_bgnd_color=black,cell_line_color=red,cell_line_width=\<open>12.0cm\<close>)
          \<open>\<open>\<^cell>\<open>dfg\<close> \<^col>\<open>dfg\<close> \<^row>\<open>dfg\<close> @{cell (cell_height =\<open>12.0cm\<close>) \<open>abracadabra\<close>}\<close>
           \<open>\<open>1\<close>  \<open>2\<close>  \<open>3\<sigma>\<close>\<close>
          \<close>}
      \<^cell>\<open>dfg\<close>  @{row \<open>is technical\<close> \<open> \<open>\<sigma> * a\<^sub>4\<close> \<close>}\<close>
(*>*)

ML\<open>@{term "side_by_side_figure"};
   @{typ "doc_class rexp"}; 
   DOF_core.SPY;

\<close>

text\<open>@{term_ \<open>3 + 4::int\<close>} @{value_ \<open>3 + 4::int\<close>} \<close>
end
