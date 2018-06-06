theory BAC2017
  imports "../../ontologies/mathex_onto"
    Deriv Transcendental
begin
   
open_monitor*[exam::MathExam] 


section*[idir::Author,affiliation="''CentraleSupelec''", 
email="''idir.aitsadoune@centralesupelec.fr''"]
{*Idir AIT SADOUNE*}

section*[keller::Author,affiliation="''LRI, Univ. Paris-Sud''", 
email="''Chantal.Keller@lri.fr''"]
{*Chantal KELLER*}


section*[header::Header,examSubject= "[analysis,geometry]", 
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


subsection*[exo1 :: Exercise,
    Exercise.concerns= "{examiner,validator,student}",
    Exercise.content="[q1::Task,q2,q3a]"]
{* 
On considère la fonction h définie sur l’intervalle [0..+\<infinity>] par : @{term "h(x) = x * exponent (-x)"}
*}

definition h :: "real \<Rightarrow> real"
  where "h x \<equiv> x * exp (- x)"

 
subsubsection*[q1::Task, Task.concerns= "{examiner,validator,student}",
level="oneStar", mark="1::int", type="formal"] 
{* Déterminer la limite de la fonction @{term h} en +\<infinity>. *}

text*[a1::Answer_Formal_Step]
{* Fill in term and justification*}

lemma q1 : "(h \<longlongrightarrow> (0::real)) at_top"
  sorry

subsubsection*[v1::Validation,
    proofs="[q1::thm]"]
  {* See lemma q1 *}

  
subsubsection*[q2::Task, Task.concerns= "{examiner,validator,student}",
level="oneStar", mark="1::int", type="formal"] 
{* Étudier les variations de la fonction @{term h} sur l'intervalle [0..+\<infinity>] et dresser son tableau
   de variation *}

text*[a2::Answer_Formal_Step]
{* Fill in term and justification*}

definition h' :: "real \<Rightarrow> real"
  where "h' x \<equiv> (1 - x) * exp (- x)"

lemma q2_a : "DERIV h x :> h' x"
proof -
  have * : "DERIV (exp \<circ> uminus) x :> - (exp (-x))"
    by (simp add: has_derivative_compose)
  have ** : "DERIV id x :> 1"
    by (metis DERIV_ident eq_id_iff)
  have *** : "DERIV h x :> x * (- (exp (- x))) + 1 * (exp (- x))"
    by (simp add: * ** has_derivative_mult comp_def)
  show ?thesis
    by (metis "***" left_diff_distrib mult_minus_right uminus_add_conv_diff)
qed

lemma q2_b : "0 \<le> x \<and> x \<le> y \<and> y \<le> 1 \<Longrightarrow> h x \<le> h y"
  sorry

lemma q2_c : "1 \<le> x \<and> x \<le> y \<Longrightarrow> h x \<ge> h y"
  sorry

subsubsection*[v2::Validation,
    proofs="[q2_b::thm, q2_c]"]
  {* See lemmas q2_b and q2_c *}


subsubsection*[q3a::Task, Task.concerns= "{examiner,validator,student}",
level="oneStar", mark="1::int", type="formal"] 
{* Vérifier que pour tout nombre réel x appartenant à l'intervalle [0..+\<infinity>], on a :
   @term{h x = (exp (- x)) - (h' x)} *}

text*[a3a::Answer_Formal_Step]
{* Fill in term and justification*}

lemma q3a : "h x = (exp (- x)) - (h' x)"
  by (simp add : h_def h'_def left_diff_distrib)

subsubsection*[v3a::Validation,
    proofs="[q3a::thm]"]
  {* See lemma q3a *}


subsection*[sol1 :: Solution,
    Solution.content="[exo1::Exercise]",
    Solution.valids = "[v1::Validation,v2,v3a]"]
{* 
See validations.
*}



close_monitor*[exam] 

end
