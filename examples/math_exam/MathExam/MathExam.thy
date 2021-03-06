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

(*<*)
theory MathExam
  imports "Isabelle_DOF.math_exam"
    HOL.Real
begin
(*>*)   
(* open_monitor*[exam::MathExam]  *)

section*[header::Header,examSubject= "[algebra]", 
            date="''02-05-2018''", timeAllowed="90::int"] \<open>Exam number 1\<close>
text\<open>
\begin{itemize}
\item Use black ink or black ball-point pen. 
\item Draw diagrams in pencil.
\item Answer all questions in the spaces provided.
\end{itemize}
\<close>

text*[idir::Author, affiliation="''CentraleSupelec''", 
         email="''idir.aitsadoune@centralesupelec.fr''"]
        \<open>Idir AIT SADOUNE\<close>
  
  
figure*[figure::figure, spawn_columns=False,
        relative_width="80", 
        src="''figures/Polynomialdeg5''"] 
        \<open>A Polynome.\<close>


subsubsection*[exo1 :: Exercise, content="[q1::Task,q2::Task]"]\<open>Exercise 1\<close>
text\<open>
Here are the first four lines of a number pattern.
\begin{itemize}
\item Line 1 : @{term "1*6 + 2*4 = 2*7"}
\item Line 2 : @{term "2*7 + 2*5 = 3*8"}
\item Line 3 : @{term "3*8 + 2*6 = 4*9"}
\item Line 4 : @{term "4*9 + 2*7 = 5*10"} 
\end{itemize}
\<close>

declare [[show_sorts=false]]  
subsubsection*[exo2 :: Exercise, content="[q1::Task,q2::Task]"]\<open>Exercise 2\<close> 
  
text\<open>Find the roots of the polynome:
@{term "(x^3) - 6 * x^2 + 5 * x + 12"}.
Note the intermediate steps in the following fields and submit the solution.\<close>
text\<open>
\begin{Form}[action={http://your-web-server.com/path/receiveform.cgi}]
\begin{tabular}{l}
    From @{term "(x^3) - 6 * x^2 + 5 * x + 12"}  \\\\  
    \TextField{have 1} \\\\  
    \TextField{have 2} \\\\  
    \TextField{have 3} \\\\
    \TextField{finally show} \\\\
    \CheckBox[width=1em]{Has the polynomial as many solutions as its degree ? } \\\\
    \Submit{Submit}\\
\end{tabular}
\end{Form}
\<close>

(* a bit brutal, as long as lemma* does not yet work *)
(*<*)
lemma check_polynome :
  fixes x::real 
  shows "(x^3) - 6 * x^2 + 5 * x + 12 = (x-4) * (x+1) * (x - 3)"
        
proof -
  have * : "(x-4) * (x+1) * (x - 3) = (x-4) * ((x+1) * (x-3))"
         by simp
  have ** : "... = (x-4) * (x^2 - 2*x - 3)"
    apply(auto simp: right_diff_distrib add.commute semiring_normalization_rules(1)[symmetric])
    by (simp add: semiring_normalization_rules(29))
  have *** : "... = x^3 - 6 * x^2 + 5 * x + 12"
    apply(auto simp: right_diff_distrib left_diff_distrib add.commute semiring_normalization_rules(1)[symmetric])
    by (simp add: numeral_3_eq_3 semiring_normalization_rules(29))
  show ?thesis
    by(simp only: * ** ***)
qed
(*>*)

text*[a1::Answer_Formal_Step]\<open>First Step: Fill in term and justification\<close>
text*[a2::Answer_Formal_Step]\<open>Next Step: Fill in term and justification\<close>
text*[a3::Answer_Formal_Step]\<open>Next Step: Fill in term and justification\<close>
text*[a4::Answer_Formal_Step]\<open>Next Step: Fill in term and justification\<close>
  
text*[q1::Task, local_grade="oneStar", mark="1::int", type="formal"] 
\<open>Complete Line 10 :  @{term "10*x + 2*y =  11*16"}\<close>

subsubsection*[exo3 :: Exercise, content="[q1::Task,q2::Task]"]\<open>Exercise 3\<close>  

text*[q2::Task, local_grade="threeStars", mark="3::int", type="formal"] 
\<open>Prove that  @{term "n*(n+5) + 2*(n+3) "} is always the product of two numbers 
   with a difference of 5.
\<close> 
(* this does not work on the level of the LaTeX output for known restrictions of the Toplevel. *)
(* close_monitor*[exam :: MathExam] *)

end
