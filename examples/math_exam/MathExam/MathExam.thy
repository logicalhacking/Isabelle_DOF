(*<*)
theory MathExam
  imports "../../../ontologies/mathex_onto"
    Real
begin
(*>*)   
open_monitor*[exam::MathExam] 


section*[header::Header,examSubject= "[algebra]", 
            date="''02-05-2018''", timeAllowed="90::int"] {* Exam number 1 *}
text{* 
\begin{itemize}
\item Use black ink or black ball-point pen. 
\item Draw diagrams in pencil.
\item Answer all questions in the spaces provided.
\end{itemize}
*}

subsection*[idir::Author, affiliation="''CentraleSupelec''", 
         email="''idir.aitsadoune@centralesupelec.fr''"]
        {*Idir AIT SADOUNE*}
  
  
(* should be in DOF-core 

* causes crash on the LaTeX side:
 ( FP-DIV )
*** ! Undefined control sequence.
*** <argument> ...ative_width}}{100} \includegraphics
***                                                   [width=\scale \textwidth ]...
*** l.44 {A Polynome.}
*)
figure*[figure::figure, spawn_columns=False,relative_width="''80''", 
        src="''figures/Polynomialdeg5.png''"] 
        \<open>A Polynome.\<close>


subsubsection*[exo1 :: Exercise, content="[q1::Task,q2::Task]"]\<open>Exercise 1\<close>
text{* 
Here are the first four lines of a number pattern.
\begin{itemize}
\item Line 1 : @{term "1*6 + 2*4 = 2*7"}
\item Line 2 : @{term "2*7 + 2*5 = 3*8"}
\item Line 3 : @{term "3*8 + 2*6 = 4*9"}
\item Line 4 : @{term "4*9 + 2*7 = 5*10"} 
\end{itemize}
*}

declare [[show_sorts=false]]  
subsubsection*[exo2 :: Exercise, content="[q1::Task,q2::Task]"]\<open>Exercise 2\<close> 
  
text{* Find the roots of the polynome:
@{term "(x^3) - 6 * x^2 + 5 * x + 12"}.
Note the intermediate steps in the following fields and submit the solution.  *}
text{*
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
*}

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
  
text*[a1::Answer_Formal_Step]{* First Step: Fill in term and justification *}
text*[a2::Answer_Formal_Step]{* Next Step: Fill in term and justification *}
text*[a3::Answer_Formal_Step]{* Next Step: Fill in term and justification *}
text*[a4::Answer_Formal_Step]{* Next Step: Fill in term and justification *}
  
text*[q1::Task, level="oneStar", mark="1::int", type="formal"] 
{* Complete Line 10 :  @{term "10*x + 2*y =  11*16"} *}

subsubsection*[exo3 :: Exercise, content="[q1::Task,q2::Task]"]\<open>Exercise 3\<close>  

text*[q2::Task, level="threeStars", mark="3::int", type="formal"] 
{* Prove that  @{term "n*(n+5) + 2*(n+3) "} is always the product of two numbers 
   with a difference of 5.
*} 
(* this does not work on the level of the LaTeX output for known restrictions of the Toplevel. *)
close_monitor*[exam::MathExam] 

end
