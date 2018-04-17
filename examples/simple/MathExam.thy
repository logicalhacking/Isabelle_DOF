theory MathExam
  imports "../../ontologies/mathex_onto"
begin

open_monitor*[exam::MathExam] 

text*[header::Header,examGrade=A1, examSubject= algebra]{*Exam number 1*}
text*[idir::Author, affiliation="CentraleSupelec"]{*Idir AIT SADOUNE*}

section*[exo1 :: Exercise, content="[q1,q2,q3]"]
{* Please follow directions carefully ans show all your work.*}

text*[q1::Question, level=twoStars, mark=5] 
{*
Give an example of each of the following : 
a - a rational number which is not integer.
b - a real number which is not rational.
*}

text*[q2::Question, level=oneStar, mark=5] 
{*
Write in interval notation : @{term ''-3 < x < 5''}
*}

text*[q3::Question, level=oneStar, mark=5] 
{*
True or false : @{term ''0/8 = 0''}
*}

(*

section{* Example*}  
 
term "[ @{thm ''refl''}] @ [ @{thm ''sym''}, @{thm ''trans''} ] "
  
text{*
      @{term "[ @{thm ''refl''}] @ [ @{thm ''sym''}, @{thm ''trans''} ]"}} are the theorems
of the equational logic fragment of HOL.
*}
*)  

close_monitor*[exam] 

end