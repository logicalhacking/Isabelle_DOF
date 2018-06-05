theory BAC2017
  imports "../../ontologies/mathex_onto"
    Deriv Transcendental
begin
   
open_monitor*[exam::MathExam] 

section*[idir::Author,affiliation="''CentraleSupelec''", 
email="''idir.aitsadoune@centralesupelec.fr''"]
{*Idir AIT SADOUNE*}

subsection*[header::Header,examSubject= "[algebra,geometry]", 
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

subsubsection*[exo1 :: Exercise,Exercise.concerns= "{examiner,validator,student}",
Exercise.content="[q1::Task]"]
{* 
On considère la fonction h définie sur l’intervalle [0..+\<infinity>] par : @{term "h(x) = x * exponent (-x)"}
*}

definition h :: "real \<Rightarrow> real"
  where "h x \<equiv> x * exp (- x)"

  
subsubsection*[q1::Task, Task.concerns= "{examiner,validator,student}",
level="oneStar", mark="1::int", type="formal"] 
{* Déterminer la limite de la fonction @{term h} en +\<infinity>. *}

text*[a1::Answer_Formal_Step]
{* First Step: Fill in term and justification*}

lemma q1 : "(h \<longlongrightarrow> (0::real)) at_top"
  sorry

  
subsubsection*[q2::Task, Task.concerns= "{examiner,validator,student}",
level="oneStar", mark="1::int", type="formal"] 
{* Étudier les variations de la fonction @{term h} sur l'intervalle [0..+\<infinity>] et dresser son tableau
   de variation} *}
find_theorems exp

text*[a2::Answer_Formal_Step]
{* First Step: Fill in term and justification*}

lemma q2_a : "DERIV h x :> (1 - x) * exp (- x)"
proof -
  have * : "DERIV (exp \<circ> uminus) x :> - (exp (-x))"
    by (simp add: has_derivative_minus has_derivative_compose Transcendental.DERIV_exp)
  have ** : "DERIV id x :> 1"
    by (metis DERIV_ident eq_id_iff)
  have *** : "DERIV h x :> x * (- (exp (- x))) + 1 * (exp (- x))"
    by (simp add: * ** has_derivative_mult)
  show ?thesis
    by (metis "***" left_diff_distrib mult_minus_right uminus_add_conv_diff)
qed


close_monitor*[exam] 

end
