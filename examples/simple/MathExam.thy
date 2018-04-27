theory MathExam
  imports "../../ontologies/mathex_onto"
begin

open_monitor*[exam::MathExam] 

text*[idir::Author, affiliation="CentraleSupelec"]{*Idir AIT SADOUNE*}

text*[header::Header,examGrade="A1", examSubject= "algebra", examTitle="Exam number 1"]
{* Please follow directions carefully and show all your work.*}

section*[exo1 :: Exercise, content="[q1,q2,q3]", mark="15"]{* Exercise 1.*}
text*[q1::Question, level="twoStars", mark="5"] 
{*
Give an example of each of the following : 
a - a rational number which is not integer.
b - a real number which is not rational.
*}

text*[q2::Question, level="oneStar", mark="5"] 
{*
Write in interval notation : @{term "-3 < x"} and  @{term "x < 5"}
*}

text*[q3::Question, level="oneStar", mark="5"] 
{* True or false : @{term "0/8 = 0"} *}

close_monitor*[exam] 

end
