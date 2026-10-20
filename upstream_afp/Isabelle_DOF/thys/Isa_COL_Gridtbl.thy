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

chapter \<open>Grid Tables: Parsing and Layout\<close>

text\<open> This theory provides the front-end of the reStructuredText-style ``grid tables'' of
      the COL: a parser from the ASCII-art (or \<^verbatim>\<open>\<^bold>\<close>-symbol) representation to an abstract
      table with row/column spans, alignments and rulers. It is independent of the generation of
      LaTeX (which is done in \<^verbatim>\<open>Isa_COL\<close>) and has no dependency on the DOF core.

      The syntax extends the rst grid tables as follows:
      \<^item> rulers (\<^verbatim>\<open>=====\<close>) may occur at \<^emph>\<open>any\<close> horizontal border line (in particular the first
        and the last), not just once as a head separator;
      \<^item> row alignment is based on \<^emph>\<open>logical\<close> lengths: every ASCII symbol (\<^verbatim>\<open>|\<close>, \<^verbatim>\<open>+\<close>, \<^verbatim>\<open>-\<close>, \<^verbatim>\<open>=\<close>,
        \<^verbatim>\<open>:\<close>, or any other symbol such as \<open>\<alpha>\<close>) has length one, and \<^verbatim>\<open>\<^bold>\<open>---\<close>\<close>, which is admitted
        as alternative for any run of structural symbols, has the length of its content;
      \<^item> markdown-style alignment markers: \<^verbatim>\<open>:-----:\<close> (centered), \<^verbatim>\<open>:-----\<close> (left), \<^verbatim>\<open>-----:\<close>
        (right) in the border of a cell;
      \<^item> cell content may be a cartouche (which is later evaluated like any other text).
    \<close>

theory Isa_COL_Gridtbl
  imports Main
begin

ML\<open>
structure Gridtbl =
struct

datatype halign = Default | Left | Center | Right
datatype rule   = No_Rule | Single | Thick | Double  (* horizontal border: none, '---', bold '---', '===' *)

(* one logical column of the source: a symbol, its position, and the original source symbols
   (only the first logical column of a \<^bold>-run carries the whole run) *)
type gcell = {sym: string, pos: Position.T, bold: bool, orig: Symbol_Pos.T list}

type cell = {row: int, col: int, rowspan: int, colspan: int, align: halign,
             leftb: bool, rightb: bool,         (* bold left / right vertical border *)
             content: Symbol_Pos.T list list}   (* trimmed source lines of the cell *)

type table = {nrows: int, ncols: int,
              col_widths: int list,              (* logical widths (between the borders) *)
              cells: cell list,                  (* in reading order *)
              hrules: rule list list}            (* (nrows+1) x ncols; the horizontal borders *)

fun drop_while p = snd o chop_prefix p
fun err pos msg = error ("Grid table: " ^ msg ^ Position.here pos)

val bold_sym = chr 92 ^ "<^bold>"
val structural = ["|", "+", "-", "=", ":"]


(* 1. Lines, indentation, logical columns *)

fun split_lines (syms: Symbol_Pos.T list) : (Position.T * Symbol_Pos.T list) list =
  let fun go cur acc [] = rev ((Position.none, rev cur) :: acc)
        | go cur acc (("\n", p) :: ss) = go [] ((p, rev cur) :: acc) ss
        | go cur acc (s :: ss) = go (s :: cur) acc ss
  in go [] [] syms end

fun is_blank_sp (s, _) = Symbol.is_blank s

val trim_end = rev o drop_while is_blank_sp o rev

fun lex_line (syms: Symbol_Pos.T list) : gcell list =
  let
    fun plain (s, p) = {sym = s, pos = p, bold = false, orig = [(s, p)]}
    (* the bold symbol (without argument) is a bold vertical bar of logical length one *)
    fun bar (bs as (_, p)) = {sym = "|", pos = p, bold = true, orig = [bs]}
    fun go [] = []
      | go ((bs as (b, _)) :: rest) =
          if b <> bold_sym then plain bs :: go rest
          else
            (case rest of
               (os as (o', _)) :: rest' =>
                 if o' <> Symbol.open_ then bar bs :: go rest
                 else
                   let val (inner, after) = chop_prefix (fn (s, _) => s <> Symbol.close) rest'
                   in case after of
                        cl :: after' =>
                          if not (null inner) andalso forall (member (op =) structural o fst) inner
                          then
                            let val whole = bs :: os :: inner @ [cl]
                            in map_index (fn (i, (s, p)) =>
                                 {sym = s, pos = p, bold = true,
                                  orig = if i = 0 then whole else []}) inner
                               @ go after'
                            end
                          else plain bs :: go rest
                      | [] => plain bs :: go rest
                   end
             | [] => [bar bs])
  in go syms end


(* 2. Cell discovery on the logical grid *)

fun parse_syms (src: Symbol_Pos.T list) : table =
  let
    val lines0 = split_lines src |> map (apsnd trim_end)
    val lines1 = lines0 |> drop_while (null o snd) |> rev |> drop_while (null o snd) |> rev
    val _ = null lines1 andalso error "Grid table: empty table"
    val first_pos = (case snd (hd lines1) of (_, p) :: _ => p | [] => Position.none)
    val indent = length (fst (chop_prefix is_blank_sp (snd (hd lines1))))
    fun strip (nlpos, l) =
      let val (bl, _) = chop_prefix is_blank_sp l
      in if null l then err (if nlpos = Position.none then first_pos else nlpos)
                            "blank line inside table"
         else if length bl < indent then err (snd (hd l)) "line is indented less than the table"
         else drop indent l end
    val glines = map (Vector.fromList o lex_line o strip) lines1
    val g = Vector.fromList glines
    val H = Vector.length g
    val W = Vector.length (Vector.sub (g, 0))
    val _ = Vector.app (fn row =>
              if Vector.length row <> W then
                let val last = if Vector.length row = 0 then first_pos
                               else #pos (Vector.sub (row, Vector.length row - 1))
                in err last ("line has logical length " ^ string_of_int (Vector.length row) ^
                             ", expected " ^ string_of_int W) end
              else ()) g
    fun at (r, c) = Vector.sub (Vector.sub (g, r), c)
    fun sym r c = #sym (at (r, c))
    fun pos r c = #pos (at (r, c))
    fun is_h s = s = "-" orelse s = "=" orelse s = ":" orelse s = "+"
    fun is_v s = s = "|" orelse s = "+"
    fun hscan r c1 c2 = forall (fn c => is_h (sym r c)) (c1 upto c2)
    fun vscan c r1 r2 = forall (fn r => is_v (sym r c)) (r1 upto r2)

    (* smallest closed rectangle with top-left corner (t,l) *)
    fun find_cell (t, l) =
      let
        fun rows c r =
          if r >= H then NONE
          else
            let val ch = sym r c
            in if not (is_v ch) then NONE
               else if ch = "+" andalso r > t + 1 andalso sym r l = "+"
                       andalso hscan r l c andalso vscan l t r then SOME r
               else rows c (r + 1)
            end
        fun cols c =
          if c >= W then NONE
          else
            let val ch = sym t c
            in if not (is_h ch) then NONE
               else if ch = "+" andalso c > l + 1
               then (case rows c (t + 1) of SOME b => SOME (t, l, b, c) | NONE => cols (c + 1))
               else cols (c + 1)
            end
      in if sym t l = "+" then cols (l + 1) else NONE end

    val _ = if sym 0 0 = "+" then () else err (pos 0 0) "table must start with '+'"
    fun discover [] _ acc = rev acc
      | discover ((t, l) :: q) seen acc =
          if Inttab.defined seen (t * W + l) then discover q seen acc
          else
            let val seen' = Inttab.update (t * W + l, ()) seen
            in case find_cell (t, l) of
                 NONE => discover q seen' acc
               | SOME (cell as (_, _, b, r)) =>
                   let val next = filter (fn (r', c') => sym r' c' = "+") [(t, r), (b, l), (b, r)]
                   in discover (q @ next) seen' (cell :: acc) end
            end
    val rects = discover [(0, 0)] Inttab.empty []

    (* every position must be border of, or interior to, exactly one structure *)
    val border = Array.array (H * W, false)
    val inside = Array.array (H * W, ~1)
    fun setb r c = Array.update (border, r * W + c, true)
    val _ = List.app (fn (t, l, b, r) =>
              (List.app (fn c => (setb t c; setb b c)) (l upto r);
               List.app (fn rr => (setb rr l; setb rr r)) (t upto b))) rects
    val _ = map_index (fn (i, (t, l, b, r)) =>
              List.app (fn rr => List.app (fn c =>
                  if Array.sub (inside, rr * W + c) >= 0 orelse Array.sub (border, rr * W + c)
                  then err (pos rr c) "overlapping cells"
                  else Array.update (inside, rr * W + c, i)) (l + 1 upto r - 1)) (t + 1 upto b - 1))
            rects
    val _ = List.app (fn r => List.app (fn c =>
              if Array.sub (border, r * W + c) orelse Array.sub (inside, r * W + c) >= 0 then ()
              else err (pos r c) "character is not part of a well-formed (closed) cell") (0 upto W - 1))
            (0 upto H - 1)

    (* spans: slots between the distinct horizontal/vertical border lines *)
    val rbs = sort_distinct int_ord (maps (fn (t, _, b, _) => [t, b]) rects)
    val cbs = sort_distinct int_ord (maps (fn (_, l, _, r) => [l, r]) rects)
    fun idx xs x = find_index (fn y => y = x) xs
    val nrows = length rbs - 1
    val ncols = length cbs - 1
    val slots = Array.array (nrows * ncols, 0)
    fun seg_info r c1 c2 =
      let
        val inner = map (sym r) (c1 + 1 upto c2 - 1)
        val bars = filter (fn s => s = "-" orelse s = "=") inner
        val bold = exists (fn c => #bold (at (r, c))) (c1 + 1 upto c2 - 1)
        val kind =
          if null bars then err (pos r c1) "border without '-' or '='"
          else if forall (fn s => s = "-") bars then (if bold then Thick else Single)
          else if forall (fn s => s = "=") bars then Double
          else err (pos r c1) "border mixes '-' and '='"
        val a = (case (hd inner = ":", List.last inner = ":") of
                   (true, true) => Center | (true, false) => Left
                 | (false, true) => Right | _ => Default)
      in (kind, a) end
    val hr = Array.array ((nrows + 1) * ncols, No_Rule)
    fun set_rule k cs kind pos' =
      List.app (fn j =>
        let val old = Array.sub (hr, k * ncols + j)
        in if old <> No_Rule andalso old <> kind then err pos' "inconsistent border"
           else Array.update (hr, k * ncols + j, kind) end) cs
    fun mk_cell (t, l, b, r) =
      let
        val (row, rowend) = (idx rbs t, idx rbs b)
        val (col, colend) = (idx cbs l, idx cbs r)
        val _ = List.app (fn i => List.app (fn j =>
                  Array.update (slots, i * ncols + j, Array.sub (slots, i * ncols + j) + 1))
                  (col upto colend - 1)) (row upto rowend - 1)
        val (kt, at_) = seg_info t l r
        val (kb, ab) = seg_info b l r
        val _ = set_rule row (col upto colend - 1) kt (pos t l)
        val _ = set_rule rowend (col upto colend - 1) kb (pos b l)
        val align = if at_ <> Default then at_ else ab
        val content =
          (t + 1 upto b - 1)
          |> map (fn rr => maps (fn c => #orig (at (rr, c))) (l + 1 upto r - 1)
                           |> trim_end |> drop_while is_blank_sp)
          |> drop_while null |> rev |> drop_while null |> rev
        fun edge_bold c = exists (fn rr => #bold (at (rr, c))) (t + 1 upto b - 1)
      in {row = row, col = col, rowspan = rowend - row, colspan = colend - col,
          align = align, leftb = edge_bold l, rightb = edge_bold r, content = content} : cell end
    val cells = map mk_cell rects
    val _ = Array.appi (fn (i, n) =>
              if n = 1 then ()
              else err (pos (nth rbs (i div ncols)) (nth cbs (i mod ncols)))
                       "cells do not tile the table") slots
    val hrules = map (fn k => map (fn j => Array.sub (hr, k * ncols + j)) (0 upto ncols - 1))
                     (0 upto nrows)
    val cells' = sort (fn (a : cell, b : cell) =>
                          prod_ord int_ord int_ord ((#row a, #col a), (#row b, #col b))) cells
  in {nrows = nrows, ncols = ncols,
      col_widths = map (fn j => nth cbs (j + 1) - nth cbs j) (0 upto ncols - 1),
      cells = cells', hrules = hrules} end

fun parse_input (src: Input.source) = parse_syms (Input.source_explode src)
fun parse_string (s: string) = parse_syms (Symbol_Pos.explode0 s)


(* debugging / testing *)
fun string_of_align a = case a of Default => "" | Left => "<" | Center => "^" | Right => ">"
fun string_of_rule r = case r of No_Rule => " " | Single => "-" | Thick => "#" | Double => "="
fun string_of_table ({nrows, ncols, col_widths, cells, hrules} : table) =
  "rows=" ^ string_of_int nrows ^ " cols=" ^ string_of_int ncols ^ " widths="
  ^ commas (map string_of_int col_widths) ^ "\n"
  ^ cat_lines (map (fn (k, rs) => "rule" ^ string_of_int k ^ " " ^
                                  implode (map string_of_rule rs)) (tag_list 0 hrules))
  ^ "\n"
  ^ cat_lines (map (fn {row, col, rowspan, colspan, align, content, ...} =>
        "(" ^ string_of_int row ^ "," ^ string_of_int col ^ ")+" ^ string_of_int rowspan ^ "x"
        ^ string_of_int colspan ^ string_of_align align ^ " "
        ^ quote (space_implode "/" (map Symbol_Pos.content content))) cells)

end

(* 3. LaTeX output *)

structure Gridtbl_Latex =
struct

(* split a line into plain parts and top-level balanced cartouches (whose content is returned) *)
fun chunks (syms: Symbol_Pos.T list) : (bool * Symbol_Pos.T list) list =
  let
    fun flush_plain acc = if null acc then [] else [(false, rev acc)]
    fun cart _ _ [] = NONE
      | cart d inner ((s as (c, _)) :: ss) =
          if c = Symbol.open_ then cart (d + 1) (s :: inner) ss
          else if c = Symbol.close then
            (if d = 1 then SOME (rev inner, ss) else cart (d - 1) (s :: inner) ss)
          else cart d (s :: inner) ss
    fun go acc [] = flush_plain acc
      | go acc ((s as (c, _)) :: ss) =
          if c = Symbol.open_ then
            (case cart 1 [] ss of
               SOME (inner, rest) => flush_plain acc @ ((true, inner) :: go [] rest)
             | NONE => go (s :: acc) ss)
          else go (s :: acc) ss
  in go [] syms end

fun output_syms ctxt syms =
  let
    fun edge_blank ss = (case ss of s :: _ => Gridtbl.is_blank_sp s | [] => false)
    val space = Latex.string " "
    val core = Gridtbl.drop_while Gridtbl.is_blank_sp (Gridtbl.trim_end syms)
  in
    if null syms then []
    else if null core then space
    else
      (if edge_blank syms then space else [])
      @ Document_Output.output_document ctxt {markdown = false}
          (Input.source false (Symbol_Pos.content core) (Symbol_Pos.range core))
      @ (if edge_blank (rev syms) then space else [])
  end

fun output_content ctxt (lines: Symbol_Pos.T list list) : Latex.text =
  lines
  |> map (maps (fn (_, syms) => output_syms ctxt syms) o chunks)
  |> separate (Latex.string "\n")
  |> flat

fun output_table ctxt ({nrows, ncols, col_widths, cells, hrules}: Gridtbl.table) : Latex.text =
  let
    val total = fold (curry op +) col_widths 0
    val sum_widths = fold (curry op +)
    fun wsum col span = sum_widths (take span (drop col col_widths)) 0
    fun cellw (c: Gridtbl.cell) =
      "\\DOFgridcellw{" ^ string_of_int (wsum (#col c) (#colspan c)) ^ "}{" ^ string_of_int total
      ^ "}{" ^ string_of_int ncols ^ "}{" ^ string_of_int (ncols + 1) ^ "}{"
      ^ string_of_int (#colspan c - 1) ^ "}"
    fun align_cmd a =
      (case a of Gridtbl.Center => "\\centering" | Gridtbl.Right => "\\raggedleft"
               | _ => "\\raggedright")
    fun starts i j = find_first (fn (c: Gridtbl.cell) => #row c = i andalso #col c = j) cells
    fun covers i j = find_first (fn (c: Gridtbl.cell) =>
          #row c < i andalso i < #row c + #rowspan c andalso #col c <= j
          andalso j < #col c + #colspan c) cells
    (* vertical border at column boundary m, in row slot i? *)
    fun vline i m = i >= 0 andalso i < nrows andalso
          exists (fn (c: Gridtbl.cell) =>
                     #row c <= i andalso i < #row c + #rowspan c
                     andalso (#col c = m orelse #col c + #colspan c = m)) cells

    (* is the vertical border at column boundary m in row slot i bold? *)
    fun vbold i m =
      exists (fn (c: Gridtbl.cell) =>
                #row c <= i andalso i < #row c + #rowspan c
                andalso ((#col c = m andalso #leftb c)
                         orelse (#col c + #colspan c = m andalso #rightb c))) cells
    fun bar b = if b then "!{\\vrule width \\DOFgridthick}" else "|"

    fun hrule k =
      let
        val rs = nth hrules k
        fun ch r = (case r of Gridtbl.No_Rule => "~" | Gridtbl.Single => "-" | Gridtbl.Thick => "-"
                            | Gridtbl.Double => "=")
        fun junction m =
          if m = 0 orelse m = ncols orelse vline (k - 1) m orelse vline k m
          then bar (vbold (k - 1) m orelse vbold k m) else ""
        val thick = exists (fn r => r = Gridtbl.Thick) rs
      in if forall (fn r => r = Gridtbl.No_Rule) rs then []
         else (if thick then Latex.string "\\noalign{\\global\\arrayrulewidth=\\DOFgridthick}" else [])
              @ Latex.string ("\\hhline{" ^ junction 0 ^
                implode (map_index (fn (j, r) => ch r ^ junction (j + 1)) rs) ^ "}\n")
              @ (if thick then Latex.string "\\noalign{\\global\\arrayrulewidth=\\DOFgridthin}\n" else [])
      end

    fun item i col last text span =
      Latex.string ("\\multicolumn{" ^ string_of_int span ^ "}{" ^ bar (vbold i col) ^ "l"
                    ^ (if last then bar (vbold i ncols) else "") ^ "}{")
      @ text @ Latex.string "}"

    fun row i =
      let
        fun go j =
          if j >= ncols then []
          else
            (case starts i j of
               SOME c =>
                 let val txt = Latex.string ("\\DOFgridcell{" ^ cellw c ^ "}{" ^ align_cmd (#align c)
                                             ^ "}{" ^ string_of_int (#rowspan c) ^ "}{")
                               @ output_content ctxt (#content c) @ Latex.string "}"
                 in (fn last => item i j last txt (#colspan c)) :: go (j + #colspan c) end
             | NONE =>
                 (case covers i j of
                    SOME c => (fn last => item i j last [] (#colspan c)) :: go (j + #colspan c)
                  | NONE => error "Grid table: internal error (uncovered slot)"))
        val items = go 0
        val n = length items
      in flat (separate (Latex.string " & ") (map_index (fn (k, f) => f (k = n - 1)) items))
         @ Latex.string " \\\\\n" @ hrule (i + 1)
      end
  in Latex.string "\\par\\smallskip\\noindent\n"
     @ Latex.string ("\\begin{tabular}{|" ^ implode (replicate ncols "l|") ^ "}\n")
     @ hrule 0
     @ flat (map row (0 upto nrows - 1))
     @ Latex.string "\\end{tabular}\\par\\smallskip\n"
  end

val _ = Theory.setup
  (Document_Output.antiquotation_raw_embedded \<^binding>\<open>gridtbl\<close> (Scan.lift Parse.embedded_input)
    (fn ctxt => output_table ctxt o Gridtbl.parse_input))

end
\<close>

subsection \<open>Tests\<close>

ML\<open>
local
  val T = Gridtbl.parse_string o cat_lines
  fun fails lines = (T lines; false) handle ERROR _ => true
in
val ex1 = T
 ["+-----+-----------+",
  "|     | L2 and L3 |",
  "| L1  +-----+-----+",
  "|     | L2  | L3  |",
  "+=====+=====+=====+",
  "|     | BBB | CCC |",
  "| AAA +-----+-----+",
  "|     |   DDDDD   |",
  "+-----+-----+-----+",
  "|           | FFF |",
  "|   EEEEE   +-----+",
  "|           | GGG |",
  "+-----------+-----+"]
val _ = writeln (Gridtbl.string_of_table ex1)

val _ = @{assert} (#nrows ex1 = 6 andalso #ncols ex1 = 3)
val _ = @{assert} (length (#cells ex1) = 11)
(* misaligned right border *)
val _ = @{assert} (fails ["+---+---+", "| a | b  |", "+---+---+"])
val _ = @{assert} (fails ["+---+---+", "| a | b |", "+---+-- +"])
val _ = @{assert} (fails ["+---+---+", "| a | b |"])
val _ = @{assert} (fails ["+--=+---+", "| a | b |", "+---+---+"])
val _ = @{assert} (fails ["+---+---+", "| a | b |", "  +---+---+"])

(* markdown alignment, rulers at first and last line, content with cartouche, bold borders *)
val ex2 = T
 ["+:=====:+------:+",
  "| \<open>a|b\<close> | b     |",
  "+-------+:------+",
  "|   c   | d     |",
  "+=======+=======+"]
val _ = writeln (Gridtbl.string_of_table ex2)

val ex3 = T
 ["+---\<^bold>\<open>---\<close>+---+",
  "\<^bold>\<open>|\<close> a    | b |",
  "+\<^bold>\<open>======\<close>+===+"]
val _ = writeln (Gridtbl.string_of_table ex3)
end
\<close>

end
