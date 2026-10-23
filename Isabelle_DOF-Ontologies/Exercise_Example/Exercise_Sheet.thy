(*<*)
theory Exercise_Sheet
  imports "Isabelle_DOF-Ontologies.Exercise"
begin
(*>*)

text\<open>This is an example of the ontology \<^verbatim>\<open>Exercise\<close>: one exercise sheet, typeset in three variants
(see the option \<^verbatim>\<open>document_variants\<close> in the \<^verbatim>\<open>ROOT\<close> file) for students (the tasks), for
professors (additionally the solutions) and for examiners (additionally the remarks on the marking).
The PDFs of the three variants are generated into the directory \<^verbatim>\<open>output\<close>.\<close>

use_template%invisible "exercise"
use_ontology%invisible "Isabelle_DOF-Ontologies.Exercise"

section\<open>The Sheet\<close>

text\<open>The sheet is declared as a text element (its body is the title of the document) and, in parallel,
as a monitor, which checks the structure of the exercises: exercises with optional parts, which
consist of tasks with their subtasks. Solutions and remarks may occur everywhere.\<close>

text*[sheet_title::exercise_sheet, category=TD,
      subtitle="\<open>Natural Numbers, Induction and Truth Tables\<close>",
      institution="\<open>Universite Paris-Saclay\<close>", course="\<open>Logic\<close>", year=2026]
  \<open>Exercise Sheet 1: Natural Numbers\<close>

open_monitor*%invisible[sheet::exercise_sheet, category=TD,
                        institution="\<open>Universite Paris-Saclay\<close>", course="\<open>Logic\<close>",
                        year=2026]

text\<open>The command \<^theory_text>\<open>exercise_role\<close> prints the banner with the role of the variant and the data of
the sheet. It can also set the role, as in \<^theory_text>\<open>exercise_role professor\<close>, which overrides the variant.\<close>

exercise_role

section\<open>Exercises\<close>

text*[ex1::"exercise", title="\<open>Addition\<close>", difficulty=2, origin="\<open>Folklore\<close>"]
\<open>In this exercise, we study the addition on the natural numbers, which is defined by the
equations \<^term>\<open>0 + m = m\<close> and \<^term>\<open>Suc n + m = Suc (n + m)\<close>.\<close>

text*[p1::exercise_part, title="\<open>Warm-up\<close>"]\<open>Elementary facts.\<close>

text*[t1::task, difficulty=1, points=2]\<open>What is \<^term>\<open>1 + 1 :: nat\<close>?\<close>
text*[s1::solution, refers_to="Inl @{task \<open>t1\<close>}"]\<open>It is \<^term>\<open>2 :: nat\<close>.\<close>
text*[r1::remark]\<open>Give both points if the argument is correct, one for the result only.\<close>

text*[p2::exercise_part, title="\<open>Induction\<close>"]\<open>Proofs on the structure of the natural numbers.\<close>

text*[t2::task, difficulty=2, points=6]\<open>Prove that the addition is commutative.\<close>
text*[st1::subtask, points=2]\<open>Show the base case \<^term>\<open>0 + m = m + 0\<close>.\<close>
text*[ss1::solution, refers_to="Inr @{subtask \<open>st1\<close>}"]
\<open>By definition of the addition and induction on \<^term>\<open>m\<close>.\<close>
text*[st2::subtask, points=4]\<open>Show the step case.\<close>
text*[ss2::solution, refers_to="Inr @{subtask \<open>st2\<close>}", also_refers_to="[Inl @{task \<open>t2\<close>}]"]
\<open>Use the induction hypothesis and the associativity. The theorem is machine-checked as
@{thm add.commute}.\<close>
text*[r2::remark]\<open>Only the induction in the step case is worth four points.\<close>

text*[ex2::"exercise", title="\<open>Truth Tables\<close>", difficulty=1]
\<open>Boolean functions are given by their truth tables.\<close>

text*[t3::task, difficulty=1, points=4]
\<open>Complete the truth table of the implication \<^term>\<open>A \<longrightarrow> B\<close>, with \<open>1\<close> for true and \<open>0\<close> for false:

\<^gridtbl>\<open>
+-----+-----+-------+
| A   | B   | A \<rightarrow> B |
+=====+=====+=======+
| 0   | 0   |       |
+-----+-----+-------+
| 0   | 1   |       |
+-----+-----+-------+
| 1   | 0   |       |
+-----+-----+-------+
| 1   | 1   |       |
+-----+-----+-------+
\<close>\<close>

text*[s3::solution, refers_to="Inl @{task \<open>t3\<close>}"]
\<open>The implication is false only for \<open>A = 1\<close> and \<open>B = 0\<close>:

\<^gridtbl>\<open>
+-----+-----+-------+
| A   | B   | A \<rightarrow> B |
+=====+=====+=======+
| 0   | 0   | 1     |
+-----+-----+-------+
| 0   | 1   | 1     |
+-----+-----+-------+
| 1   | 0   | 0     |
+-----+-----+-------+
| 1   | 1   | 1     |
+-----+-----+-------+
\<close>\<close>

text*[r3::remark]
\<open>One point per correct line. The marking scheme of the sheet:

\<^gridtbl>\<open>
+-----------+--------+
| Task      | Points |
+===========+========+
| 1         | 2      |
+-----------+--------+
| 2         | 6      |
+-----------+--------+
| 3         | 4      |
+===========+========+
| Total     | 12     |
+-----------+--------+
\<close>\<close>

close_monitor*%invisible[sheet]

(*<*)
end
(*>*)
