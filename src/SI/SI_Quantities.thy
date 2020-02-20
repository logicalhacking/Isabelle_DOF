section \<open> SI Quantities \<close>

theory SI_Quantities
  imports SI_Units
begin

subsection \<open> The \<^theory_text>\<open>Quantity\<close>-type and its operations \<close>

record 'a Quantity =
  mag :: 'a   \<comment> \<open> Magnitude of the quantity \<close>
  dim  :: Dimension \<comment> \<open> Dimension of the quantity \<close>

lemma Quantity_eq_intro:
  assumes "mag x = mag y" "dim x = dim y" "more x = more y"
  shows "x = y"
  by (simp add: assms)

instantiation Quantity_ext :: (times, times) times
begin
  definition [si_def]:
    "times_Quantity_ext x y = \<lparr> mag = mag x \<cdot> mag y, dim = dim x \<cdot> dim y, \<dots> = more x \<cdot> more y \<rparr>"
instance ..
end

lemma mag_times [simp]: "mag (x \<cdot> y) = mag x \<cdot> mag y" by (simp add: times_Quantity_ext_def)
lemma dim_times [simp]: "dim (x \<cdot> y) = dim x \<cdot> dim y" by (simp add: times_Quantity_ext_def)
lemma more_times [simp]: "more (x \<cdot> y) = more x \<cdot> more y" by (simp add: times_Quantity_ext_def)

instantiation Quantity_ext :: (zero, zero) zero
begin
  definition "zero_Quantity_ext = \<lparr> mag = 0, dim = 1, \<dots> = 0 \<rparr>"
instance ..
end

lemma mag_zero [simp]: "mag 0 = 0" by (simp add: zero_Quantity_ext_def)
lemma dim_zero [simp]: "dim 0 = 1" by (simp add: zero_Quantity_ext_def)
lemma more_zero [simp]: "more 0 = 0" by (simp add: zero_Quantity_ext_def)

instantiation Quantity_ext :: (one, one) one
begin
  definition [si_def]: "one_Quantity_ext = \<lparr> mag = 1, dim = 1, \<dots> = 1 \<rparr>"
instance ..
end

lemma mag_one [simp]: "mag 1 = 1" by (simp add: one_Quantity_ext_def)
lemma dim_one [simp]: "dim 1 = 1" by (simp add: one_Quantity_ext_def)
lemma more_one [simp]: "more 1 = 1" by (simp add: one_Quantity_ext_def)

instantiation Quantity_ext :: (inverse, inverse) inverse
begin
  definition [si_def]: "inverse_Quantity_ext x = \<lparr> mag = inverse (mag x), dim = inverse (dim x), \<dots> = inverse (more x) \<rparr>"
  definition [si_def]: "divide_Quantity_ext x y = \<lparr> mag = mag x / mag y, dim = dim x / dim y, \<dots> = more x / more y \<rparr>"
instance ..
end

lemma mag_inverse [simp]: "mag (inverse x) = inverse (mag x)" 
  by (simp add: inverse_Quantity_ext_def)

lemma dim_inverse [simp]: "dim (inverse x) = inverse (dim x)" 
  by (simp add: inverse_Quantity_ext_def)

lemma more_inverse [simp]: "more (inverse x) = inverse (more x)" 
  by (simp add: inverse_Quantity_ext_def)

lemma mag_divide [simp]: "mag (x / y) = mag x / mag y" 
  by (simp add: divide_Quantity_ext_def)

lemma dim_divide [simp]: "dim (x / y) = dim x / dim y" 
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
    where "less_eq_Quantity_ext x y = (mag x \<le> mag y \<and> dim x = dim y \<and> more x \<le> more y)"
  definition less_Quantity_ext :: "('a, 'b) Quantity_scheme \<Rightarrow> ('a, 'b) Quantity_scheme \<Rightarrow> bool"
    where "less_Quantity_ext x y = (x \<le> y \<and> \<not> y \<le> x)"

instance ..

end

instance Quantity_ext :: (order, order) order
  by (intro_classes, auto simp add: less_Quantity_ext_def less_eq_Quantity_ext_def)

subsection \<open> SI Tagged Types \<close>
text\<open>We 'lift' SI type expressions to SI tagged type expressions as follows:\<close>

typedef (overloaded) ('n, 'u::si_type) tQuant ("_[_]" [999,0] 999) 
                     = "{x :: 'n Quantity. dim x = SI('u)}"
  morphisms fromQ toQ by (rule_tac x="\<lparr> mag = undefined, dim = SI('u) \<rparr>" in exI, simp)

setup_lifting type_definition_tQuant

text \<open> Coerce values when their dimensions are equivalent \<close>

definition coerceUnit :: "'u\<^sub>2 itself \<Rightarrow> 'a['u\<^sub>1::si_type] \<Rightarrow> 'a['u\<^sub>2::si_type]" where
"SI('u\<^sub>1) = SI('u\<^sub>2) \<Longrightarrow> coerceUnit t x = (toQ (fromQ x))"

section\<open>Operations SI-tagged types via their Semantic Domains\<close>

subsection\<open>Predicates on SI-tagged types\<close>

text \<open> Two SI types are equivalent if they have the same value-level dimensions. \<close>

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
  by (metis qequiv.rep_eq assms coerceUnit_def toQ_cases toQ_inverse)

(* or equivalently *)

lemma coerceQuant_eq_iff2:
  fixes x :: "'a['u\<^sub>1::si_type]"
  assumes "SI('u\<^sub>1) = SI('u\<^sub>2::si_type)" and "y = (coerceUnit TYPE('u\<^sub>2) x)"
  shows "x \<cong>\<^sub>Q y"
  using qequiv_sym assms(1) assms(2) coerceQuant_eq_iff by blast

lemma updown_eq_iff:
  fixes x :: "'a['u\<^sub>1::si_type]" fixes y :: "'a['u\<^sub>2::si_type]"
  assumes "SI('u\<^sub>1) = SI('u\<^sub>2::si_type)" and "y = (toQ (fromQ x))"
  shows "x \<cong>\<^sub>Q y"
  by (simp add: assms(1) assms(2) coerceQuant_eq_iff2 coerceUnit_def)

text\<open>This is more general that \<open>y = x \<Longrightarrow> x \<cong>\<^sub>Q y\<close>, since x and y may have different type.\<close>

lemma qeq: 
  fixes x :: "'a['u\<^sub>1::si_type]" fixes y :: "'a['u\<^sub>2::si_type]"
  assumes  "x \<cong>\<^sub>Q y"
  shows "SI('u\<^sub>1) = SI('u\<^sub>2::si_type)"
  by (metis (full_types) qequiv.rep_eq assms fromQ mem_Collect_eq)

subsection\<open>Operations on SI-tagged types\<close>

lift_definition 
  qtimes :: "('n::comm_ring_1)['a::si_type] \<Rightarrow> 'n['b::si_type] \<Rightarrow> 'n['a \<cdot>'b]" (infixl "\<^bold>\<cdot>" 69) is "(*)"
  by (simp add: si_sem_DimTimes_def times_Quantity_ext_def)
  
lift_definition 
  qinverse :: "('n::field)['a::si_type] \<Rightarrow> 'n['a\<^sup>-\<^sup>1]" ("(_\<^sup>-\<^sup>\<one>)" [999] 999) is "inverse"
  by (simp add: inverse_Quantity_ext_def si_sem_DimInv_def)

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
lift_definition zero_tQuant :: "('a, 'b) tQuant" is "\<lparr> mag = 0, dim = SI('b) \<rparr>" 
  by simp
instance ..
end

instantiation tQuant :: (one,si_type) one
begin
lift_definition one_tQuant :: "('a, 'b) tQuant" is "\<lparr> mag = 1, dim = SI('b) \<rparr>"
  by simp
instance ..
end

instantiation tQuant :: (plus,si_type) plus
begin
lift_definition plus_tQuant :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> 'a['b]"
  is "\<lambda> x y. \<lparr> mag = mag x + mag y, dim = SI('b) \<rparr>"
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
  is "\<lambda> x. \<lparr> mag = - mag x, dim = dim x \<rparr>" by (simp)
instance ..
end

instantiation tQuant :: (minus,si_type) minus
begin
lift_definition minus_tQuant :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> 'a['b]"
  is "\<lambda> x y. \<lparr> mag = mag x - mag y, dim = dim x \<rparr>" by (simp)

instance ..
end

instance tQuant :: (numeral,si_type) numeral ..

instance tQuant :: (ab_group_add,si_type) ab_group_add
  by (intro_classes, (transfer, simp)+)

instantiation tQuant :: (order,si_type) order
begin
  lift_definition less_eq_tQuant :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> bool" is "\<lambda> x y. mag x \<le> mag y" .
  lift_definition less_tQuant :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> bool" is "\<lambda> x y. mag x < mag y" .
  instance by (intro_classes, (transfer, simp add: less_le_not_le)+)
end

lift_definition scaleQ :: "'a \<Rightarrow> 'a::comm_ring_1['u::si_type] \<Rightarrow> 'a['u]" (infixr "*\<^sub>Q" 63)
  is "\<lambda> r x. \<lparr> mag = r * mag x, dim = SI('u) \<rparr>" by simp

notation scaleQ (infixr "\<odot>" 63)

lift_definition mk_unit :: "'u itself \<Rightarrow> ('a::one)['u::si_type]" 
  is "\<lambda> u. \<lparr> mag = 1, dim = SI('u) \<rparr>" by simp

syntax "_mk_unit" :: "type \<Rightarrow> logic" ("UNIT'(_')")
translations "UNIT('a)" == "CONST mk_unit TYPE('a)"

subsection \<open>Polymorphic Operations for Elementary SI Units \<close>

definition [si_eq]: "meter    = UNIT(Length)"
definition [si_eq]: "second   = UNIT(Time)"
definition [si_eq]: "kilogram = UNIT(Mass)"
definition [si_eq]: "ampere   = UNIT(Current)"
definition [si_eq]: "kelvin   = UNIT(Temperature)"
definition [si_eq]: "mole     = UNIT(Amount)"
definition [si_eq]: "candela  = UNIT(Intensity)"

definition dimless ("\<one>") 
  where [si_eq]: "dimless  = UNIT(NoDimension)"

end