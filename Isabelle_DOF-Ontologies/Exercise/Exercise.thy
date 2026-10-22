(*************************************************************************
 * Copyright (C) 
 *               2026      The University of Exeter 
 *               2026      The University of Paris-Saclay
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

(*<*)
theory  Exercise
  imports  "Isabelle_DOF.Isa_COL" 
  "Isabelle_DOF-Ontologies.document_templates"
  keywords "exercise_role" :: document_raw
begin

define_ontology "DOF-Exercise.sty" "Writing exercise sheets, for students, professors and examiners."
(*>*)

chapter \<open>An Ontology for Exercise Sheets\<close>

text\<open>This ontology is an abstraction of the \<^LaTeX> package \<^verbatim>\<open>exercise.sty\<close> (see
\<^url>\<open>https://ctan.org/pkg/exercise\<close>; a description is contained in this directory). It models
exercise sheets consisting of \<^emph>\<open>exercises\<close>, which are optionally divided into \<^emph>\<open>parts\<close>, which 
contain \<^emph>\<open>tasks\<close> (the ``questions'' of the package) with \<^emph>\<open>subtasks\<close> and their \<^emph>\<open>solutions\<close> (the 
``answers''). The sheets are structured by monitors, not by lists. 

Every element has an \<^emph>\<open>audience\<close>: the lowest of the three roles \<open>student\<close>, \<open>professor\<close> and 
\<open>examiner\<close> that sees it. A sheet is typeset in \<^emph>\<open>three variants\<close> (see \<^verbatim>\<open>DOF-Exercise.sty\<close>): 
for the student (tasks), for the professor (additionally the solutions) and for the examiner 
(additionally the remarks addressed to external evaluators).\<close>

section\<open>Audiences: The Selection Concept\<close>

datatype audience = student | professor | examiner

text\<open>The audiences are ordered: \<open>student\<close> < \<open>professor\<close> < \<open>examiner\<close>. An element is shown in
a variant if the role of the variant is at least the audience of the element.\<close>

section\<open>Exercise Elements\<close>

doc_class exercise_element = text_element +
      title      :: string       <= "''''"
      difficulty :: int          <= "0"
      visible_to :: audience     <= "student"
      \<comment> \<open>The body of an element is the text that is presented to the audience.\<close>

doc_class "exercise" = exercise_element +      \<comment> \<open>environment \<open>Exercise\<close> of exercise.sty\<close>
      origin     :: string       <= "''''"
      \<comment> \<open>The body gives context information or background material of the exercise.\<close>

doc_class exercise_part = exercise_element +            \<comment> \<open>\<open>ExePart\<close> of exercise.sty\<close>
      name       :: string       <= "''''"        \<comment> \<open>denomination of the part, Preliminary\<close>
      \<comment> \<open>A part groups several tasks of an exercise.\<close>

doc_class task = exercise_element +            \<comment> \<open>\<open>Question\<close> of exercise.sty\<close>
      points         :: int          <= "0"    \<comment> \<open>weight in the marking scheme\<close>
      \<comment> \<open>The body of a task formulates the question.\<close>

doc_class subtask = exercise_element +         \<comment> \<open>\<open>subQuestion\<close> of exercise.sty\<close>
      points         :: int          <= "0"    \<comment> \<open>weight in the marking scheme\<close>
      \<comment> \<open>The body of a subtask formulates the question.\<close>

doc_class solution = exercise_element +        \<comment> \<open>\<open>Answer\<close> of exercise.sty\<close>
      refers_to      :: "(task + subtask)"
      also_refers_to :: "(task + subtask)list"  <= "[]"
      visible_to     :: audience     <= "professor"
      \<comment> \<open>The solution belongs to the preceding task or subtask.\<close>

doc_class remark = exercise_element +          \<comment> \<open>no equivalent in exercise.sty\<close>
      visible_to     :: audience     <= "examiner"
      \<comment> \<open>A comment for the external evaluators, the marking scheme.\<close>

section\<open>Exercise Sheets\<close>

text\<open>A sheet is a monitor. It only fixes the skeleton of the questions: exercises with optional
parts, which consist of tasks with their subtasks. Solutions and remarks are not part of the
skeleton; they may occur anywhere inside the sheet. A solution is tied to its task or subtask by
the attribute \<open>refers_to\<close>, which is checked by the type system.

A sheet can also be declared as a text element, for example
\<open>text*[td1::exercise_sheet, category=TD]\<open>Title\<close>\<close>. Its body is the title of the sheet; it replaces the
\<open>title*\<close> of the other ontologies. In this form, the attributes of the sheet (an optional subtitle,
the category, the course, the institution and the year) appear in the title of the document, but the
structure of the sheet is not checked by the monitor.\<close>

datatype category = TD | TP | CM | Exam

text\<open>The \<^emph>\<open>category\<close> of a sheet is one of
\<^item> \<open>TD\<close> (``travaux dirigés''): exercises worked on in a tutorial,
\<^item> \<open>TP\<close> (``travaux pratiques''): practical exercises, for example in a laboratory or at a computer,
\<^item> \<open>CM\<close> (``cours magistral''): exercises that accompany a lecture, and
\<^item> \<open>Exam\<close> (``examen''): an examination.\<close>

doc_class exercise_sheet =
      category      :: category <= "TD"
      subtitle      :: string  <= "''''"
      institution   :: string  <= "''''"
      course        :: string  <= "''''"
      year          :: int     <= "0"
      accepts "\<lbrace> exercise ~~ \<lbrace> \<lbrakk>exercise_part\<rbrakk> ~~ \<lbrace> task ~~ \<lbrace>subtask\<rbrace>\<^sup>* \<rbrace>\<^sup>+ \<rbrace>\<^sup>+ \<rbrace>\<^sup>+"

section\<open>Checks and Commands for Sheets\<close>

text\<open>The category of a sheet has consequences. For an examination, every task must be marked
with points; this is checked when the sheet is closed, when all its tasks are known.\<close>

ML\<open>
fun check_exam_points oid _ ctxt =
  let
    val thy = Context.theory_of ctxt
    val category = ISA_core.compute_attr_access ctxt "category" oid NONE \<^here>
    val cid_task = DOF_core.get_onto_class_name_global "task" thy
    val traces = AttributeAccess.compute_trace_ML ctxt oid NONE \<^here>
    fun without_points (cid, oid') =
      cid = cid_task andalso
      snd (HOLogic.dest_number (ISA_core.compute_attr_access ctxt "points" oid' NONE \<^here>)) <= 0
  in
    if Long_Name.base_name (Term.term_name category) <> "Exam" then true
    else (case find_first without_points traces of
            NONE => true
          | SOME (_, oid') => error ("Task " ^ oid' ^ " of an exam needs points."))
  end
\<close>

setup\<open>
fn thy =>
let val cid = "exercise_sheet"
    val binding = DOF_core.binding_from_onto_class_pos cid thy
    val cid_long = DOF_core.get_onto_class_name_global cid thy
in  DOF_core.add_closing_ml_invariant binding 
      (DOF_core.make_ml_invariant (check_exam_points, cid_long)) thy end
\<close>

text\<open>The command \<open>exercise_role\<close> sets the role of the document that is generated from the
theory: \<open>exercise_role student\<close>, \<open>exercise_role professor\<close> or \<open>exercise_role examiner\<close>. 
It overrides the role given by the name of the document variant (see \<^verbatim>\<open>DOF-Exercise.sty\<close>); 
without an argument, the role of the variant is kept. The command shows a banner with the role and 
with the data of the open sheet (category, course, institution, year); so it should be given after 
the opening of the monitor, before the first exercise.\<close>

ML\<open>
local
  val roles = ["student", "professor", "examiner"]

  fun open_sheet thy =
    let val cid_sheet = DOF_core.get_onto_class_name_global "exercise_sheet" thy
        val names = map fst (Name_Space.dest_table (DOF_core.get_monitor_infos (Proof_Context.init_global thy)))
        fun is_sheet name = 
          let val DOF_core.Instance {cid, ...} = DOF_core.get_instance_global (Long_Name.base_name name) thy
          in cid = cid_sheet end
    in find_first is_sheet names |> Option.map Long_Name.base_name end

  fun sheet_latex thy =
    (case open_sheet thy of
       NONE => []
     | SOME oid =>
         let val ctxt = Context.Theory thy
             fun attr a = ISA_core.compute_attr_access ctxt a oid NONE Position.none
             val category = Long_Name.base_name (Term.term_name (attr "category"))
             fun esc sym =
               if Symbol.is_ascii sym
               then (case sym of
                       "\\" => "\\textbackslash{}" | "{" => "\\{" | "}" => "\\}" | "#" => "\\#" 
                     | "$" => "\\$" | "%" => "\\%" | "&" => "\\&" | "_" => "\\_" 
                     | "^" => "\\^{}" | "~" => "\\~{}" | _ => sym)
               else Latex.output_symbols [sym]
             fun str a = String.concat (map esc (Symbol.explode (HOLogic.dest_string (attr a))))
             val year = snd (HOLogic.dest_number (attr "year"))
         in Latex.string ("\\DOFexeSetSheet{" ^ category ^ "}{" ^ str "course" ^ "}{" 
                          ^ str "institution" ^ "}{" ^ string_of_int year ^ "}\n") end)

  fun output role_opt st =
    let val thy = Proof_Context.theory_of (Toplevel.presentation_context st)
    in (case role_opt of
          NONE => []
        | SOME role => Latex.string ("\\DOFexeSetRole{" ^ role ^ "}\n"))
       @ sheet_latex thy @ Latex.string "\\DOFexeShowBanner\n" end
in
val _ = Outer_Syntax.command \<^command_keyword>\<open>exercise_role\<close> 
          "set the role (student, professor, examiner) of the generated document"
          (Scan.option (Parse.position Parse.name) >> (fn role_pos =>
             let val role_opt = Option.map #1 role_pos
                 val _ = (case role_pos of
                            SOME (role, pos) =>
                              if member (op =) roles role then ()
                              else error ("Unknown role " ^ quote role ^ ", must be one of "
                                          ^ commas_quote roles ^ Position.here pos)
                          | NONE => ())
             in Toplevel.present (output role_opt) o Toplevel.present_local_theory NONE (output role_opt) end))
end
\<close>

(*<*)
end
(*>*)
