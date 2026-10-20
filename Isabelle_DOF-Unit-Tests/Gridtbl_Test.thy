(*************************************************************************
 * Copyright (C) 
 *               2026      The University of Paris-Saclay
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

chapter\<open>Regression Tests for Grid Tables (gridtbl)\<close>

theory 
  Gridtbl_Test
imports 
  "Isabelle_DOF-Ontologies.Conceptual"
  TestKit
begin

section\<open>Test Purpose.\<close>
text\<open>The antiquotation \<open>gridtbl\<close> of the COL: parsing (spans, rulers, alignment markers,
logical lengths, cartouche cells), the reporting of syntax errors, and the generated \<^verbatim>\<open>LaTeX\<close>.\<close>

ML\<open>
local
  val T = Gridtbl.parse_string o cat_lines
  fun fails msg lines =
    (T lines; false) handle ERROR m => String.isSubstring msg m
  fun ltx (t : Latex.text) = implode (map XML.string_of t)
  fun cell_of (t : Gridtbl.table) (r, c) =
    the (find_first (fn (x : Gridtbl.cell) => #row x = r andalso #col x = c) (#cells t))
  fun text_of (x : Gridtbl.cell) = space_implode "/" (map Symbol_Pos.content (#content x))
  fun latex lines = ltx (Gridtbl_Latex.output_table \<^context> (T lines))
in

(* 1. spans, rulers (also in the middle), irregular grid *)
val t1 = T
 ["+-------+---------------+",
  "|       | L2 and L3     |",
  "| L1    +-------+-------+",
  "|       | L2    | L3    |",
  "+=======+=======+=======+",
  "|       | BBB   | CCC   |",
  "| AAA   +-------+-------+",
  "|       |   DDDDD       |",
  "+-------+-------+-------+",
  "|               | FFF   |",
  "|     EEEEE     +-------+",
  "|               | GGG   |",
  "+---------------+-------+"]
val _ = @{assert} (#nrows t1 = 6 andalso #ncols t1 = 3 andalso #col_widths t1 = [8, 8, 8])
val _ = @{assert} (length (#cells t1) = 11)
val _ = @{assert} (let val c = cell_of t1 (0, 0) in #rowspan c = 2 andalso #colspan c = 1 end)
val _ = @{assert} (let val c = cell_of t1 (0, 1) in #rowspan c = 1 andalso #colspan c = 2 end)
val _ = @{assert} (let val c = cell_of t1 (4, 0) in #rowspan c = 2 andalso #colspan c = 2
                                                    andalso text_of c = "EEEEE" end)
val _ = @{assert} (nth (#hrules t1) 2 = [Gridtbl.Double, Gridtbl.Double, Gridtbl.Double])
val _ = @{assert} (nth (#hrules t1) 1 = [Gridtbl.No_Rule, Gridtbl.Single, Gridtbl.Single])
val _ = @{assert} (nth (#hrules t1) 5 = [Gridtbl.No_Rule, Gridtbl.No_Rule, Gridtbl.Single])

(* 2. alignment markers; rulers at the first and the last border *)
val t2 = T
 ["+:=====:+------:+",
  "|   a   | b     |",
  "+:------+-------+",
  "|   c   | d     |",
  "+=======+=======+"]
val _ = @{assert} (#align (cell_of t2 (0, 0)) = Gridtbl.Center)
val _ = @{assert} (#align (cell_of t2 (0, 1)) = Gridtbl.Right)
val _ = @{assert} (#align (cell_of t2 (1, 0)) = Gridtbl.Left)
val _ = @{assert} (#align (cell_of t2 (1, 1)) = Gridtbl.Default)
val _ = @{assert} (hd (#hrules t2) = [Gridtbl.Double, Gridtbl.Single]
                   andalso List.last (#hrules t2) = [Gridtbl.Double, Gridtbl.Double])

(* 3. logical lengths: the bold variants count as the number of their symbols *)
val t3 = T
 ["+---\<^bold>\<open>---\<close>+---+",
  "\<^bold>\<open>|\<close> a    | b |",
  "+\<^bold>\<open>======\<close>+===+"]
val _ = @{assert} (#col_widths t3 = [7, 4] andalso text_of (cell_of t3 (0, 0)) = "a")

(* 4. cartouche cells: a '|' inside is content; lines of a cell are kept separately *)
val t4 = T
 ["+----------+-------+",
  "| \<open>a|b\<open>c\<close>\<close> | x     |",
  "|  more    | y     |",
  "+----------+-------+"]
val _ = @{assert} (text_of (cell_of t4 (0, 0)) = "\<open>a|b\<open>c\<close>\<close>/more")

(* 4b. the bold symbol (alone) is a bold vertical bar of logical length one *)
val t5 = T
 ["+-----+-----+",
  "\<^bold> a   | b   \<^bold>",
  "+-----+-----+"]
val _ = @{assert} (#col_widths t5 = [6, 6])
val _ = @{assert} (#leftb (cell_of t5 (0, 0)) andalso not (#rightb (cell_of t5 (0, 0)))
                   andalso #rightb (cell_of t5 (0, 1)))
val _ = @{assert} (String.isSubstring "!{\\vrule width \\DOFgridthick}"
                     (latex ["+-----+-----+", "\<^bold> a   | b   |", "+-----+-----+"]))
val _ = @{assert} (nth (#hrules (T ["+\<^bold>\<open>---\<close>+", "|   |", "+---+"])) 0 = [Gridtbl.Thick])

(* 5. generated LaTeX *)
val l1 = latex ["+-----+-----+", "| a   | b   |", "+=====+=====+"]
val _ = @{assert} (String.isSubstring "\\hhline{|=|=|}" l1
                   andalso String.isSubstring "\\multicolumn{1}{|l}{" l1
                   andalso String.isSubstring "\\multicolumn{1}{|l|}{" l1)
val l2 = ltx (Gridtbl_Latex.output_table \<^context> t1)
val _ = @{assert} (String.isSubstring "{\\raggedright}{2}{L1}" l2 andalso
                   String.isSubstring "\\multicolumn{2}{|l|}{" l2 andalso
                   String.isSubstring "\\hhline{|~|-|-|}" l2)
val _ = @{assert} (String.isSubstring "\\centering" (latex ["+:---:+", "| x   |", "+-----+"]))

(* 6. syntax errors are reported *)
val _ = @{assert} (fails "logical length" ["+---+---+", "| a | b  |", "+---+---+"])
val _ = @{assert} (fails "closed" ["+---+---+", "| a | b |", "+---+-- +"])
val _ = @{assert} (fails "closed" ["+---+---+", "| a | b |"])
val _ = @{assert} (fails "mixes" ["+--=+---+", "| a | b |", "+---+---+"])
val _ = @{assert} (fails "indented less" ["  +---+", "  | a |", "+---+"])
val _ = @{assert} (fails "must start" ["| a |", "+---+"])
val _ = @{assert} (fails "empty" ["", ""])
val _ = @{assert} (fails "blank line" ["+---+", "", "+---+"])

end
\<close>

section\<open>Document Integration\<close>

text\<open>An ordinary text with a grid table: \<^gridtbl>\<open>
+--------------+--------+------------------------+
| Class        | Chk    | Time                   |
+==============+========+========================+
| \<open>\<^emph>\<open>figure\<close>\<close>  | 12     | \<open>@{term \<open>1+1::nat\<close>}\<close>   |
+--------------+--------+------------------------+
| a \<open>|\<close> b      | 3      | 0.5                    |
+--------------+--------+------------------------+
\<close>\<close>

text*[gt1::A, x = "3"]\<open>A table inside an ontology-aware text-element:
\<^gridtbl>\<open>
+-----+-----------+
|     | L2 and L3 |
| L1  +-----+-----+
|     | L2  | L3  |
+=====+=====+=====+
\<close>\<close>

end
