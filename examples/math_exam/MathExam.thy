theory MathExam
  imports "../../ontologies/mathex_onto"
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

subsubsection*[exo1 :: Exercise, Exercise.content="[q1::Question,q2::Question]"]
{* 
Here are the first four lines of a number pattern.
\begin{itemize}
\item Line 1 : @{term "1*6 + 2*4 = 2*7"}
\item Line 2 : @{term "2*7 + 2*5 = 3*8"}
\item Line 3 : @{term "3*8 + 2*6 = 4*9"}
\item Line 4 : @{term "4*9 + 2*7 = 5*10"} 
\end{itemize}
*}

text*[q1::Question, level="oneStar", Question.mark="1::int", type="formal"] 
{*
Complete Line 10 :  @{term "10*x + 2*y =  11*16"}
*}

text*[q2::Question, level="threeStars", Question.mark="3::int", type="formal"] 
{*
Prove that  @{term "n*(n+5) + 2*(n+3) "} is always the product of two numbers with a difference of 5.
*}


close_monitor*[exam] 

end
