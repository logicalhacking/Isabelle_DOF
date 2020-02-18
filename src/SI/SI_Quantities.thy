section \<open> SI Quantities \<close>

theory SI_Quantities
  imports SI_Units Optics.Lenses
begin


subsection \<open> The \<^theory_text>\<open>Quantity\<close>-type and its operations \<close>

record 'a Quantity =
  magn :: 'a   \<comment> \<open> Magnitude of the quantity \<close>
  unit :: Unit \<comment> \<open> Unit of the quantity \<close>

lemma Quantity_eq_intro:
  assumes "magn x = magn y" "unit x = unit y" "more x = more y"
  shows "x = y"
  by (simp add: assms)

instantiation Quantity_ext :: (times, times) times
begin
  definition [si_def]:
    "times_Quantity_ext x y = \<lparr> magn = magn x \<cdot> magn y, unit = unit x \<cdot> unit y, \<dots> = more x \<cdot> more y \<rparr>"
instance ..
end

lemma magn_times [simp]: "magn (x \<cdot> y) = magn x \<cdot> magn y" by (simp add: times_Quantity_ext_def)
lemma unit_times [simp]: "unit (x \<cdot> y) = unit x \<cdot> unit y" by (simp add: times_Quantity_ext_def)
lemma more_times [simp]: "more (x \<cdot> y) = more x \<cdot> more y" by (simp add: times_Quantity_ext_def)

instantiation Quantity_ext :: (zero, zero) zero
begin
  definition "zero_Quantity_ext = \<lparr> magn = 0, unit = 1, \<dots> = 0 \<rparr>"
instance ..
end

lemma magn_zero [simp]: "magn 0 = 0" by (simp add: zero_Quantity_ext_def)
lemma unit_zero [simp]: "unit 0 = 1" by (simp add: zero_Quantity_ext_def)
lemma more_zero [simp]: "more 0 = 0" by (simp add: zero_Quantity_ext_def)

instantiation Quantity_ext :: (one, one) one
begin
  definition [si_def]: "one_Quantity_ext = \<lparr> magn = 1, unit = 1, \<dots> = 1 \<rparr>"
instance ..
end

lemma magn_one [simp]: "magn 1 = 1" by (simp add: one_Quantity_ext_def)
lemma unit_one [simp]: "unit 1 = 1" by (simp add: one_Quantity_ext_def)
lemma more_one [simp]: "more 1 = 1" by (simp add: one_Quantity_ext_def)

instantiation Quantity_ext :: (inverse, inverse) inverse
begin
  definition [si_def]: "inverse_Quantity_ext x = \<lparr> magn = inverse (magn x), unit = inverse (unit x), \<dots> = inverse (more x) \<rparr>"
  definition [si_def]: "divide_Quantity_ext x y = \<lparr> magn = magn x / magn y, unit = unit x / unit y, \<dots> = more x / more y \<rparr>"
instance ..
end

lemma magn_inverse [simp]: "magn (inverse x) = inverse (magn x)" 
  by (simp add: inverse_Quantity_ext_def)

lemma unit_inverse [simp]: "unit (inverse x) = inverse (unit x)" 
  by (simp add: inverse_Quantity_ext_def)

lemma more_inverse [simp]: "more (inverse x) = inverse (more x)" 
  by (simp add: inverse_Quantity_ext_def)

lemma magn_divide [simp]: "magn (x / y) = magn x / magn y" 
  by (simp add: divide_Quantity_ext_def)

lemma unit_divide [simp]: "unit (x / y) = unit x / unit y" 
  by (simp add: divide_Quantity_ext_def)

lemma more_divide [simp]: "more (x / y) = more x / more y" 
  by (simp add: divide_Quantity_ext_def)

instance Quantity_ext :: (comm_monoid_mult, comm_monoid_mult) comm_monoid_mult
  by (intro_classes, simp_all add: one_Quantity_ext_def 
                                   times_Quantity_ext_def mult.assoc, simp add: mult.commute)

instance Quantity_ext :: (ab_group_mult, ab_group_mult) ab_group_mult
  by (intro_classes, rule Quantity_eq_intro, simp_all)

subsection \<open> SI Tagged Types \<close>
text\<open>We 'lift' SI type expressions to SI tagged type expressions as follows:\<close>

typedef (overloaded) ('n, 'u::si_type) tQuant ("_[_]" [999,0] 999) 
                     = "{x :: 'n Quantity. unit x = SI('u)}"
  morphisms fromUnit toUnit by (rule_tac x="\<lparr> magn = undefined, unit = SI('u) \<rparr>" in exI, simp)

setup_lifting type_definition_tQuant

text \<open> Coerce values when their units are equivalent \<close>

definition coerceUnit :: "'u\<^sub>2 itself \<Rightarrow> 'a['u\<^sub>1::si_type] \<Rightarrow> 'a['u\<^sub>2::si_type]" where
"SI('u\<^sub>1) = SI('u\<^sub>2) \<Longrightarrow> coerceUnit t x = (toUnit (fromUnit x))"

section\<open>Operations SI-tagged types via their Semantic Domains\<close>

subsection\<open>Predicates on SI-tagged types\<close>

text \<open> Two SI types are equivalent if they have the same value-level units. \<close>

lift_definition Quant_equiv :: "'n['a::si_type] \<Rightarrow> 'n['b::si_type] \<Rightarrow> bool" (infix "\<approx>\<^sub>Q" 50) is
"(=)" .

text\<open>This gives us an equivalence, but, unfortunately, not a congruence.\<close>

lemma Quant_equiv_refl [simp]: "a \<approx>\<^sub>Q a"
  by (simp add: Quant_equiv_def)

lemma Quant_equiv_sym: "a \<approx>\<^sub>Q b \<Longrightarrow> b \<approx>\<^sub>Q a"
  by (simp add: Quant_equiv_def)

lemma Quant_equiv_trans: "\<lbrakk> a \<approx>\<^sub>Q b; b \<approx>\<^sub>Q c \<rbrakk> \<Longrightarrow> a \<approx>\<^sub>Q c"
  by (simp add: Quant_equiv_def)

(* the following series of equivalent statements ... *)

lemma coerceQuant_eq_iff:
  fixes x :: "'a['u\<^sub>1::si_type]"
  assumes "SI('u\<^sub>1) = SI('u\<^sub>2::si_type)"
  shows "(coerceUnit TYPE('u\<^sub>2) x) \<approx>\<^sub>Q x"
  by (metis Quant_equiv.rep_eq assms coerceUnit_def toUnit_cases toUnit_inverse)

(* or equivalently *)

lemma coerceQuant_eq_iff2:
  fixes x :: "'a['u\<^sub>1::si_type]"
  assumes "SI('u\<^sub>1) = SI('u\<^sub>2::si_type)" and "y = (coerceUnit TYPE('u\<^sub>2) x)"
  shows "x \<approx>\<^sub>Q y"
  using Quant_equiv_sym assms(1) assms(2) coerceQuant_eq_iff by blast

lemma updown_eq_iff:
  fixes x :: "'a['u\<^sub>1::si_type]" fixes y :: "'a['u\<^sub>2::si_type]"
  assumes "SI('u\<^sub>1) = SI('u\<^sub>2::si_type)" and "y = (toUnit (fromUnit x))"
  shows "x \<approx>\<^sub>Q y"
  by (simp add: assms(1) assms(2) coerceQuant_eq_iff2 coerceUnit_def)

text\<open>This is more general that \<open>y = x \<Longrightarrow> x \<approx>\<^sub>Q y\<close>, since x and y may have different type.\<close>

find_theorems "(toUnit (fromUnit _))"

lemma eq_ : 
  fixes x :: "'a['u\<^sub>1::si_type]" fixes y :: "'a['u\<^sub>2::si_type]"
  assumes  "x \<approx>\<^sub>Q y"
  shows "SI('u\<^sub>1) = SI('u\<^sub>2::si_type)"
  by (metis (full_types) Quant_equiv.rep_eq assms fromUnit mem_Collect_eq)

subsection\<open>Operations on SI-tagged types\<close>

lift_definition 
  Quant_times :: "('n::times)['a::si_type] \<Rightarrow> 'n['b::si_type] \<Rightarrow> 'n['a \<cdot>'b]" (infixl "\<^bold>\<cdot>" 69) is "(*)"
  by (simp add: si_sem_UnitTimes_def times_Quantity_ext_def)
  
lift_definition 
  Quant_inverse :: "('n::inverse)['a::si_type] \<Rightarrow> 'n['a\<^sup>-\<^sup>1]" ("(_\<^sup>-\<^sup>\<one>)" [999] 999) is "inverse"
  by (simp add: inverse_Quantity_ext_def si_sem_UnitInv_def)

abbreviation 
  Quant_divide :: "('n::{times,inverse})['a::si_type] \<Rightarrow> 'n['b::si_type] \<Rightarrow> 'n['a/'b]" (infixl "\<^bold>'/" 70) where
"Quant_divide x y \<equiv> x \<^bold>\<cdot> y\<^sup>-\<^sup>\<one>"

abbreviation Quant_sq ("(_)\<^sup>\<two>" [999] 999) where "u\<^sup>\<two> \<equiv> u\<^bold>\<cdot>u"
abbreviation Quant_cube ("(_)\<^sup>\<three>" [999] 999) where "u\<^sup>\<three> \<equiv> u\<^bold>\<cdot>u\<^bold>\<cdot>u"
abbreviation Quant_quart ("(_)\<^sup>\<four>" [999] 999) where "u\<^sup>\<four> \<equiv> u\<^bold>\<cdot>u\<^bold>\<cdot>u\<^bold>\<cdot>u"

abbreviation Quant_neq_sq ("(_)\<^sup>-\<^sup>\<two>" [999] 999) where "u\<^sup>-\<^sup>\<two> \<equiv> (u\<^sup>\<two>)\<^sup>-\<^sup>\<one>"
abbreviation Quant_neq_cube ("(_)\<^sup>-\<^sup>\<three>" [999] 999) where "u\<^sup>-\<^sup>\<three> \<equiv> (u\<^sup>\<three>)\<^sup>-\<^sup>\<one>"
abbreviation Quant_neq_quart ("(_)\<^sup>-\<^sup>\<four>" [999] 999) where "u\<^sup>-\<^sup>\<four> \<equiv> (u\<^sup>\<three>)\<^sup>-\<^sup>\<one>"

instantiation tQuant :: (zero,si_type) zero
begin
lift_definition zero_tQuant :: "('a, 'b) tQuant" is "\<lparr> magn = 0, unit = SI('b) \<rparr>" 
  by simp
instance ..
end

instantiation tQuant :: (one,si_type) one
begin
lift_definition one_tQuant :: "('a, 'b) tQuant" is "\<lparr> magn = 1, unit = SI('b) \<rparr>"
  by simp
instance ..
end

instantiation tQuant :: (plus,si_type) plus
begin
lift_definition plus_tQuant :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> 'a['b]"
  is "\<lambda> x y. \<lparr> magn = magn x + magn y, unit = SI('b) \<rparr>"
  by (simp)
instance ..
end

instance tQuant :: (semigroup_add,si_type) semigroup_add
  by (intro_classes, transfer, simp add: add.assoc)

instance tQuant :: (ab_semigroup_add,si_type) ab_semigroup_add
  by (intro_classes, transfer, simp add: add.commute)

instance tQuant :: (monoid_add,si_type) monoid_add
  by (intro_classes; (transfer, simp))
  
instance tQuant :: (comm_monoid_add,si_type) comm_monoid_add
  by (intro_classes; transfer, simp)

instantiation tQuant :: (uminus,si_type) uminus
begin
lift_definition uminus_tQuant :: "'a['b] \<Rightarrow> 'a['b]" 
  is "\<lambda> x. \<lparr> magn = - magn x, unit = unit x \<rparr>" by (simp)
instance ..
end

instantiation tQuant :: (minus,si_type) minus
begin
lift_definition minus_tQuant :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> 'a['b]"
  is "\<lambda> x y. \<lparr> magn = magn x - magn y, unit = unit x \<rparr>" by (simp)

instance ..
end

instance tQuant :: (numeral,si_type) numeral ..

instance tQuant :: (ab_group_add,si_type) ab_group_add
  by (intro_classes, (transfer, simp)+)

instantiation tQuant :: (times,si_type) times
begin
lift_definition times_tQuant :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> 'a['b]" 
  is "\<lambda> x y. \<lparr> magn = magn x * magn y, unit = SI('b) \<rparr>"
  by simp
instance ..
end

instance tQuant :: (power,si_type) power ..

instance tQuant :: (semigroup_mult,si_type) semigroup_mult
  by (intro_classes, transfer, simp add: mult.assoc)

instance tQuant :: (ab_semigroup_mult,si_type) ab_semigroup_mult
  by (intro_classes, (transfer, simp add: mult.commute))

instance tQuant :: (semiring,si_type) semiring
  by (intro_classes, (transfer, simp add: distrib_left distrib_right)+)

instance tQuant :: (semiring_0,si_type) semiring_0
  by (intro_classes, (transfer, simp)+)

instance tQuant :: (comm_semiring,si_type) comm_semiring
  by (intro_classes, transfer, simp add: linordered_field_class.sign_simps(18) mult.commute)

instance tQuant :: (mult_zero,si_type) mult_zero
  by (intro_classes, (transfer, simp)+)

instance tQuant :: (comm_semiring_0,si_type) comm_semiring_0
  by (intro_classes, (transfer, simp)+)

instantiation tQuant :: (real_vector,si_type) real_vector
begin

lift_definition scaleR_tQuant :: "real \<Rightarrow> 'a['b] \<Rightarrow> 'a['b]" 
  is "\<lambda> r x. \<lparr> magn = r *\<^sub>R magn x, unit = unit x \<rparr>" by simp

instance
  by (intro_classes, (transfer, simp add: scaleR_add_left scaleR_add_right)+)
end

instance tQuant :: (ring,si_type) ring
  by (intro_classes, (transfer, simp)+)

instance tQuant :: (comm_monoid_mult,si_type) comm_monoid_mult
  by (intro_classes, (transfer, simp add: mult.commute)+)

instance tQuant :: (comm_semiring_1,si_type) comm_semiring_1
  by (intro_classes; (transfer, simp add: semiring_normalization_rules(1-8,24)))

instantiation tQuant :: (divide,si_type) divide
begin
lift_definition divide_tQuant :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> 'a['b]" 
  is "\<lambda> x y. \<lparr> magn = magn x div magn y, unit = SI('b) \<rparr>" by simp
instance ..
end

instantiation tQuant :: (inverse,si_type) inverse
begin
lift_definition inverse_tQuant :: "'a['b] \<Rightarrow> 'a['b]" 
  is "\<lambda> x. \<lparr> magn = inverse (magn x), unit = SI('b) \<rparr>" by simp
instance ..
end

instantiation tQuant :: (order,si_type) order
begin
  lift_definition less_eq_tQuant :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> bool" is "\<lambda> x y. magn x \<le> magn y" .
  lift_definition less_tQuant :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> bool" is "\<lambda> x y. magn x < magn y" .
  instance by (intro_classes, (transfer, simp add: less_le_not_le)+)
end


lift_definition mk_unit :: "'a \<Rightarrow> 'u itself \<Rightarrow> ('a::one)['u::si_type]" 
  is "\<lambda> n u. \<lparr> magn = n, unit = SI('u) \<rparr>" by simp

syntax "_mk_unit" :: "logic \<Rightarrow> type \<Rightarrow> logic" ("UNIT'(_, _')")
translations "UNIT(n, 'a)" == "CONST mk_unit n TYPE('a)"

subsection \<open>Polymorphic Operations for Elementary SI Units \<close>

definition [si_def]: "meter    = UNIT(1, Length)"
definition [si_def]: "second   = UNIT(1, Time)"
definition [si_def]: "kilogram = UNIT(1, Mass)"
definition [si_def]: "ampere   = UNIT(1, Current)"
definition [si_def]: "kelvin   = UNIT(1, Temperature)"
definition [si_def]: "mole     = UNIT(1, Amount)"
definition [si_def]: "candela  = UNIT(1, Intensity)"

subsubsection \<open>The Projection: Stripping the SI-Tags \<close>

definition magnQuant :: "'a['u::si_type] \<Rightarrow> 'a" ("\<lbrakk>_\<rbrakk>\<^sub>Q") where
"magnQuant x = magn (fromUnit x)"

subsubsection \<open>More Operations \<close>

lemma unit_eq_iff_magn_eq:
  "x = y \<longleftrightarrow> \<lbrakk>x\<rbrakk>\<^sub>Q = \<lbrakk>y\<rbrakk>\<^sub>Q"
  by (auto simp add: magnQuant_def, transfer, simp)

lemma unit_equiv_iff:
  fixes x :: "'a['u\<^sub>1::si_type]" and y :: "'a['u\<^sub>2::si_type]"
  shows "x \<approx>\<^sub>Q y \<longleftrightarrow> \<lbrakk>x\<rbrakk>\<^sub>Q = \<lbrakk>y\<rbrakk>\<^sub>Q \<and> SI('u\<^sub>1) = SI('u\<^sub>2)"
proof -
  have "\<forall>t ta. (ta::'a['u\<^sub>2]) = t \<or> magn (fromUnit ta) \<noteq> magn (fromUnit t)"
    by (simp add: magnQuant_def unit_eq_iff_magn_eq)
  then show ?thesis
    by (metis (full_types) Quant_equiv.rep_eq coerceQuant_eq_iff2 eq_ magnQuant_def)
qed

lemma unit_le_iff_magn_le:
  "x \<le> y \<longleftrightarrow> \<lbrakk>x\<rbrakk>\<^sub>Q \<le> \<lbrakk>y\<rbrakk>\<^sub>Q"
  by (auto simp add: magnQuant_def; (transfer, simp))

lemma magnQuant_zero [si_def]: "\<lbrakk>0\<rbrakk>\<^sub>Q = 0"
  by (simp add: magnQuant_def, transfer, simp)

lemma magnQuant_one [si_def]: "\<lbrakk>1\<rbrakk>\<^sub>Q = 1"
  by (simp add: magnQuant_def, transfer, simp)

lemma magnQuant_plus [si_def]: "\<lbrakk>x + y\<rbrakk>\<^sub>Q = \<lbrakk>x\<rbrakk>\<^sub>Q + \<lbrakk>y\<rbrakk>\<^sub>Q"
  by (simp add: magnQuant_def, transfer, simp)

lemma magnQuant_times [si_def]: "\<lbrakk>x * y\<rbrakk>\<^sub>Q = \<lbrakk>x\<rbrakk>\<^sub>Q * \<lbrakk>y\<rbrakk>\<^sub>Q"
  by (simp add: magnQuant_def, transfer, simp)

lemma magnQuant_div [si_def]: "\<lbrakk>x / y\<rbrakk>\<^sub>Q = \<lbrakk>x\<rbrakk>\<^sub>Q / \<lbrakk>y\<rbrakk>\<^sub>Q"
  by (simp add: magnQuant_def, transfer, simp)

lemma magnQuant_qinv [si_def]: "\<lbrakk>x\<^sup>-\<^sup>\<one>\<rbrakk>\<^sub>Q = inverse \<lbrakk>x\<rbrakk>\<^sub>Q"
  by (simp add: magnQuant_def, transfer, simp)

lemma magnQuant_qdiv [si_def]: "\<lbrakk>(x::('a::field)[_]) \<^bold>/ y\<rbrakk>\<^sub>Q = \<lbrakk>x\<rbrakk>\<^sub>Q / \<lbrakk>y\<rbrakk>\<^sub>Q"
  by (simp add: magnQuant_def, transfer, simp add: field_class.field_divide_inverse)

lemma magnQuant_numeral [si_def]: "\<lbrakk>numeral n\<rbrakk>\<^sub>Q = numeral n"
  apply (induct n, simp_all add: si_def)
  apply (metis magnQuant_plus numeral_code(2))
  apply (metis magnQuant_one magnQuant_plus numeral_code(3))
  done

lemma magnQuant_mk [si_def]: "\<lbrakk>UNIT(n, 'u::si_type)\<rbrakk>\<^sub>Q = n"
  by (simp add: magnQuant_def, transfer, simp)

method si_calc = 
  (simp add: unit_eq_iff_magn_eq unit_le_iff_magn_le si_def)

end