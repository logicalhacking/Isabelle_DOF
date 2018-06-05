theory BAC2017
  imports "../../ontologies/mathex_onto"
    Real
begin
   
open_monitor*[exam::MathExam] 

section*[idir::Author,affiliation="''CentraleSupelec''", 
email="''idir.aitsadoune@centralesupelec.fr''"]
{*Idir AIT SADOUNE*}

section*[header::Header,examSubject= "[algebra,geometry]", 
 examTitle="''BACCALAUREAT GENERAL MATHEMATIQUES''", 
date="''21-06-2017''", 
timeAllowed="240::int"]
{* 
\begin{itemize}
\item Les calculatrices électroniques de poche sont autorisées, conformément à la réglementation en vigueur.
\item Le sujet est composé de 4 exercices indépendants.
\item Le candidat doit traiter tous les exercices.
\item Le candidat est invité à faire figurer sur la copie toute trace de recherche, même incomplète ou non fructueuse, qu’il aura développée.
\item Il est rappelé que la qualité de la rédaction, la clarté et la précision des raisonnements entreront pour une part importante dans l’appréciation des copies.
\end{itemize}
*}

section*[exo1 :: Exercise,Exercise.concerns= "{examiner,validator,student}",
Exercise.content="[q1::Task]"]
{* 
On considère la fonction h définie sur l’intervalle [0..+\<infinity>] par : @{term "h(x) = x * e^(-x)"}
*}

  
subsection*[q1::Task, Task.concerns= "{examiner,validator,student}",
subitems="[q11]",
level="oneStar", mark="1::int", type="formal"] 
{* Déterminer la limite de la fonction h en +\<infinity>. *}

text*[q11::Answer_Formal_Step]
{* First Step: Fill in term and justifi*}



close_monitor*[exam] 

end
