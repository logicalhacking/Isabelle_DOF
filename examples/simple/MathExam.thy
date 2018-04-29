theory MathExam
  imports "../../ontologies/mathex_onto"
begin
   
open_monitor*[exam::MathExam] 

text*[idir::Author, affiliation="''CentraleSupelec''", 
      email="''idir.aitsadoune@centralesupelec.fr''"]
{*Idir AIT SADOUNE*}

text*[header::Header,examSubject= "algebra",  examTitle="''Exam number 1''"]
{* Please follow directions carefully and show all your work.*}

section*[exo1 :: Exercise, Exercise.content="[q1::Question,q2,q3]", mark="15::int"]{* Exercise 1.*}
text*[q1::Question, level="twoStars", Question.mark="5::int"] 
{*
Give an example of each of the following : 
\begin{itemize}
\item - a rational number which is not integer.
\item - a real number which is not rational.
\end{itemize}
*}

text*[q2::Question, level="oneStar", Question.mark="5::int"] 
{*
Write in interval notation : @{term "-3 < x"} and  @{term "x < 5"}
*}

text*[q3::Question, level="oneStar", Question.mark="5::int"] 
{* True or false : @{term "0/8 = 0"} *}

close_monitor*[exam] 

end
