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

instantiation Quantity_ext :: (ord, ord) ord
begin
  definition less_eq_Quantity_ext :: "('a, 'b) Quantity_scheme \<Rightarrow> ('a, 'b) Quantity_scheme \<Rightarrow> bool"
    where "less_eq_Quantity_ext x y = (magn x \<le> magn y \<and> unit x = unit y \<and> more x \<le> more y)"
  definition less_Quantity_ext :: "('a, 'b) Quantity_scheme \<Rightarrow> ('a, 'b) Quantity_scheme \<Rightarrow> bool"
    where "less_Quantity_ext x y = (x \<le> y \<and> \<not> y \<le> x)"

instance ..

end

instance Quantity_ext :: (order, order) order
  by (intro_classes, auto simp add: less_Quantity_ext_def less_eq_Quantity_ext_def)

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

lift_definition qless_eq :: "'n::order['a::si_type] \<Rightarrow> 'n['b::si_type] \<Rightarrow> bool" (infix "\<lesssim>\<^sub>Q" 50) is
"(\<le>)" .

lift_definition qequiv :: "'n['a::si_type] \<Rightarrow> 'n['b::si_type] \<Rightarrow> bool" (infix "\<cong>\<^sub>Q" 50) is
"(=)" .

text\<open>This gives us an equivalence, but, unfortunately, not a congruence.\<close>

lemma qequiv_refl [simp]: "a \<cong>\<^sub>Q a"
  by (simp add: qequiv_def)

lemma qequiv_sym: "a \<cong>\<^sub>Q b \<Longrightarrow> b \<cong>\<^sub>Q a"
  by (simp add: qequiv_def)

lemma qequiv_trans: "\<lbrakk> a \<cong>\<^sub>Q b; b \<cong>\<^sub>Q c \<rbrakk> \<Longrightarrow> a \<cong>\<^sub>Q c"
  by (simp add: qequiv_def)

theorem qeq_iff_same_dim:
  fixes x y :: "'a['u::si_type]"
  shows "x \<cong>\<^sub>Q y \<longleftrightarrow> x = y"
  by (transfer, simp)

(* the following series of equivalent statements ... *)

lemma coerceQuant_eq_iff:
  fixes x :: "'a['u\<^sub>1::si_type]"
  assumes "SI('u\<^sub>1) = SI('u\<^sub>2::si_type)"
  shows "(coerceUnit TYPE('u\<^sub>2) x) \<cong>\<^sub>Q x"
  by (metis qequiv.rep_eq assms coerceUnit_def toUnit_cases toUnit_inverse)

(* or equivalently *)

lemma coerceQuant_eq_iff2:
  fixes x :: "'a['u\<^sub>1::si_type]"
  assumes "SI('u\<^sub>1) = SI('u\<^sub>2::si_type)" and "y = (coerceUnit TYPE('u\<^sub>2) x)"
  shows "x \<cong>\<^sub>Q y"
  using qequiv_sym assms(1) assms(2) coerceQuant_eq_iff by blast

lemma updown_eq_iff:
  fixes x :: "'a['u\<^sub>1::si_type]" fixes y :: "'a['u\<^sub>2::si_type]"
  assumes "SI('u\<^sub>1) = SI('u\<^sub>2::si_type)" and "y = (toUnit (fromUnit x))"
  shows "x \<cong>\<^sub>Q y"
  by (simp add: assms(1) assms(2) coerceQuant_eq_iff2 coerceUnit_def)

text\<open>This is more general that \<open>y = x \<Longrightarrow> x \<cong>\<^sub>Q y\<close>, since x and y may have different type.\<close>

find_theorems "(toUnit (fromUnit _))"

lemma eq_ : 
  fixes x :: "'a['u\<^sub>1::si_type]" fixes y :: "'a['u\<^sub>2::si_type]"
  assumes  "x \<cong>\<^sub>Q y"
  shows "SI('u\<^sub>1) = SI('u\<^sub>2::si_type)"
  by (metis (full_types) qequiv.rep_eq assms fromUnit mem_Collect_eq)

subsection\<open>Operations on SI-tagged types\<close>

lift_definition 
  qtimes :: "('n::comm_ring_1)['a::si_type] \<Rightarrow> 'n['b::si_type] \<Rightarrow> 'n['a \<cdot>'b]" (infixl "\<^bold>\<cdot>" 69) is "(*)"
  by (simp add: si_sem_UnitTimes_def times_Quantity_ext_def)
  
lift_definition 
  qinverse :: "('n::field)['a::si_type] \<Rightarrow> 'n['a\<^sup>-\<^sup>1]" ("(_\<^sup>-\<^sup>\<one>)" [999] 999) is "inverse"
  by (simp add: inverse_Quantity_ext_def si_sem_UnitInv_def)

abbreviation 
  qdivide :: "('n::field)['a::si_type] \<Rightarrow> 'n['b::si_type] \<Rightarrow> 'n['a/'b]" (infixl "\<^bold>'/" 70) where
"qdivide x y \<equiv> x \<^bold>\<cdot> y\<^sup>-\<^sup>\<one>"

abbreviation qsq ("(_)\<^sup>\<two>" [999] 999) where "u\<^sup>\<two> \<equiv> u\<^bold>\<cdot>u"
abbreviation qcube ("(_)\<^sup>\<three>" [999] 999) where "u\<^sup>\<three> \<equiv> u\<^bold>\<cdot>u\<^bold>\<cdot>u"
abbreviation qquart ("(_)\<^sup>\<four>" [999] 999) where "u\<^sup>\<four> \<equiv> u\<^bold>\<cdot>u\<^bold>\<cdot>u\<^bold>\<cdot>u"

abbreviation qneq_sq ("(_)\<^sup>-\<^sup>\<two>" [999] 999) where "u\<^sup>-\<^sup>\<two> \<equiv> (u\<^sup>\<two>)\<^sup>-\<^sup>\<one>"
abbreviation qneq_cube ("(_)\<^sup>-\<^sup>\<three>" [999] 999) where "u\<^sup>-\<^sup>\<three> \<equiv> (u\<^sup>\<three>)\<^sup>-\<^sup>\<one>"
abbreviation qneq_quart ("(_)\<^sup>-\<^sup>\<four>" [999] 999) where "u\<^sup>-\<^sup>\<four> \<equiv> (u\<^sup>\<three>)\<^sup>-\<^sup>\<one>"

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

instantiation tQuant :: (order,si_type) order
begin
  lift_definition less_eq_tQuant :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> bool" is "\<lambda> x y. magn x \<le> magn y" .
  lift_definition less_tQuant :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> bool" is "\<lambda> x y. magn x < magn y" .
  instance by (intro_classes, (transfer, simp add: less_le_not_le)+)
end

lift_definition scaleQ :: "'a \<Rightarrow> 'a::comm_ring_1['u::si_type] \<Rightarrow> 'a['u]" (infixr "*\<^sub>Q" 63)
  is "\<lambda> r x. \<lparr> magn = r * magn x, unit = SI('u) \<rparr>" by simp

notation scaleQ (infixr "\<odot>" 63)

lift_definition mk_unit :: "'a \<Rightarrow> 'u itself \<Rightarrow> ('a::one)['u::si_type]" 
  is "\<lambda> n u. \<lparr> magn = n, unit = SI('u) \<rparr>" by simp

syntax "_mk_unit" :: "logic \<Rightarrow> type \<Rightarrow> logic" ("UNIT'(_, _')")
translations "UNIT(n, 'a)" == "CONST mk_unit n TYPE('a)"

subsection \<open>Polymorphic Operations for Elementary SI Units \<close>

definition [si_def, si_eq]: "meter    = UNIT(1, Length)"
definition [si_def, si_eq]: "second   = UNIT(1, Time)"
definition [si_def, si_eq]: "kilogram = UNIT(1, Mass)"
definition [si_def, si_eq]: "ampere   = UNIT(1, Current)"
definition [si_def, si_eq]: "kelvin   = UNIT(1, Temperature)"
definition [si_def, si_eq]: "mole     = UNIT(1, Amount)"
definition [si_def, si_eq]: "candela  = UNIT(1, Intensity)"

definition dimless ("\<one>") 
  where [si_def, si_eq]: "dimless  = UNIT(1, NoDimension)"

end