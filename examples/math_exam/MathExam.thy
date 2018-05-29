theory MathExam
  imports "../../ontologies/mathex_onto"
    Real
begin
   
open_monitor*[exam::MathExam] 

section*[idir::Author, affiliation="''CentraleSupelec''", 
         email="''idir.aitsadoune@centralesupelec.fr''"]
{*Idir AIT SADOUNE*}

subsection*[header::Header,examSubject= "algebra",  examTitle="''Exam number 1''", 
            date="''02-05-2018''", timeAllowed="90::int"]
{* 
\begin{itemize}
\item Use black ink or black ball-point pen. 
\item Draw diagrams in pencil.
\item Answer all questions in the spaces provided.
\end{itemize}
*}

(*
text*[fig1::figure, width = "Some(textwidth 80)", 
      "file"="@{file ''../../../figures/Dogfood-Intro.png''}"]
     {* Ouroboros I : This paper from inside ... *}  
*)

subsubsection*[exo1 :: Exercise, Exercise.content="[q1::Task,q2::Task]"]
{* 
Here are the first four lines of a number pattern.
\begin{itemize}
\item Line 1 : @{term "1*6 + 2*4 = 2*7"}
\item Line 2 : @{term "2*7 + 2*5 = 3*8"}
\item Line 3 : @{term "3*8 + 2*6 = 4*9"}
\item Line 4 : @{term "4*9 + 2*7 = 5*10"} 
\end{itemize}
*}

lemma XX : "(x ^ 3) + 2 * (x^2) + 11 * x - 12 = (x-4) * (x+1) * (x - 3)"
proof -
  have  " (x ^ 3) + 2 * (x^2) + 11 * x - 12 = (x + 1) * ( x ^ 2 - 2 * x - 3)"
    sorry
  have "... = (x + 1) * (x + 4) * (x - 3)"
    sorry
  show ?thesis
    sorry
qed
  

  
text*[q1::Task, level="oneStar", mark="1::int", type="formal"] 
{*
Complete Line 10 :  @{term "10*x + 2*y =  11*16"}
*}

text*[q2::Task, level="threeStars", mark="3::int", type="formal"] 
{*
Prove that  @{term "n*(n+5) + 2*(n+3) "} is always the product of two numbers with a difference of 5.
*}


close_monitor*[exam] 

end
