section \<open> Quantities \<close>

theory ISQ_Quantities
  imports ISQ_Dimensions
begin

section \<open> Quantity Semantic Domain \<close>

text \<open> Here, we give a semantic domain for particular values of physical quantities. A quantity 
  is usually expressed as a number and a measurement unit, and the goal is to support this. First,
  though, we give a more general semantic domain where a quantity has a magnitude and a dimension. \<close>

record 'a Quantity =
  mag  :: 'a        \<comment> \<open> Magnitude of the quantity. \<close>
  dim  :: Dimension \<comment> \<open> Dimension of the quantity -- denote the kind of quantity. \<close>

text \<open> The quantity type is parametric as we permit the magnitude to be represented using any kind 
  of numeric type, such as \<^typ>\<open>int\<close>, \<^typ>\<open>rat\<close>, or \<^typ>\<open>real\<close>, though we usually minimally expect
  a field. \<close>

lemma Quantity_eq_intro:
  assumes "mag x = mag y" "dim x = dim y" "more x = more y"
  shows "x = y"
  by (simp add: assms)

text \<open> We can define several arithmetic operators on quantities. Multiplication takes multiplies
  both the magnitudes and the dimensions. \<close>

instantiation Quantity_ext :: (times, times) times
begin
  definition [si_def]:
    "times_Quantity_ext x y = \<lparr> mag = mag x \<cdot> mag y, dim = dim x \<cdot> dim y, \<dots> = more x \<cdot> more y \<rparr>"
instance ..
end

lemma mag_times  [simp]: "mag (x \<cdot> y) = mag x \<cdot> mag y" by (simp add: times_Quantity_ext_def)
lemma dim_times  [simp]: "dim (x \<cdot> y) = dim x \<cdot> dim y" by (simp add: times_Quantity_ext_def)
lemma more_times [simp]: "more (x \<cdot> y) = more x \<cdot> more y" by (simp add: times_Quantity_ext_def)

text \<open> The zero and one quantities are both dimensionless quantities with magnitude of \<^term>\<open>0\<close> and
  \<^term>\<open>1\<close>, respectively. \<close>

instantiation Quantity_ext :: (zero, zero) zero
begin
  definition "zero_Quantity_ext = \<lparr> mag = 0, dim = 1, \<dots> = 0 \<rparr>"
instance ..
end

lemma mag_zero  [simp]:  "mag 0 = 0" by (simp add: zero_Quantity_ext_def)
lemma dim_zero  [simp]:  "dim 0 = 1" by (simp add: zero_Quantity_ext_def)
lemma more_zero [simp]: "more 0 = 0" by (simp add: zero_Quantity_ext_def)

instantiation Quantity_ext :: (one, one) one
begin
  definition    [si_def]: "one_Quantity_ext = \<lparr> mag = 1, dim = 1, \<dots> = 1 \<rparr>"
instance ..
end

lemma mag_one  [simp]: "mag 1 = 1" by (simp add: one_Quantity_ext_def)
lemma dim_one  [simp]: "dim 1 = 1" by (simp add: one_Quantity_ext_def)
lemma more_one [simp]: "more 1 = 1" by (simp add: one_Quantity_ext_def)

text \<open> Quantity inversion inverts both the magnitude and the dimension. Similarly, division of
  one quantity by another, divides both the magnitudes and the dimensions. \<close>

instantiation Quantity_ext :: (inverse, inverse) inverse
begin
definition [si_def]: 
   "inverse_Quantity_ext x = \<lparr> mag = inverse (mag x), dim = inverse (dim x), \<dots> = inverse (more x) \<rparr>"
definition [si_def]: 
   "divide_Quantity_ext x y = \<lparr> mag = mag x / mag y, dim = dim x / dim y, \<dots> = more x / more y \<rparr>"
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

text \<open> As for dimensions, quantities form a commutative monoid and an abelian group. \<close>

instance Quantity_ext :: (comm_monoid_mult, comm_monoid_mult) comm_monoid_mult
  by (intro_classes, simp_all add: one_Quantity_ext_def 
                                   times_Quantity_ext_def mult.assoc, simp add: mult.commute)

instance Quantity_ext :: (ab_group_mult, ab_group_mult) ab_group_mult
  by (intro_classes, rule Quantity_eq_intro, simp_all)

text \<open> We can also define a partial order on quantities. \<close>

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

text \<open> We can define plus and minus as well, but these are partial operators as they are defined
  only when the quantities have the same dimension. \<close>

instantiation Quantity_ext :: (plus, plus) plus
begin
  definition [si_def]:
    "dim x = dim y \<Longrightarrow> 
     plus_Quantity_ext x y = \<lparr> mag = mag x + mag y, dim = dim x, \<dots> = more x + more y \<rparr>"
instance ..
end

instantiation Quantity_ext :: (uminus, uminus) uminus
begin
  definition [si_def]:
    "uminus_Quantity_ext x = \<lparr> mag = - mag x , dim = dim x, \<dots> = - more x \<rparr>"
instance ..
end

instantiation Quantity_ext :: (minus, minus) minus
begin
  definition [si_def]:
    "dim x = dim y \<Longrightarrow> 
      minus_Quantity_ext x y = \<lparr> mag = mag x - mag y, dim = dim x, \<dots> = more x - more y \<rparr>"
instance ..
end

section \<open> Dimension Typed Quantities \<close>

text \<open> We can now define the type of quantities with parametrised dimension types. \<close>

typedef (overloaded) ('n, 'd::dim_type) QuantT ("_[_]" [999,0] 999) 
                     = "{x :: 'n Quantity. dim x = QD('d)}"
  morphisms fromQ toQ by (rule_tac x="\<lparr> mag = undefined, dim = QD('d) \<rparr>" in exI, simp)

setup_lifting type_definition_QuantT

text \<open> A dimension typed quantity is parameterised by two types: \<^typ>\<open>'a\<close>, the numeric type for the
  magntitude, and \<^typ>\<open>'d\<close> for the dimension expression, which is an element of \<^class>\<open>dim_type\<close>. 
  The type \<^typ>\<open>('n, 'd) QuantT\<close> is to \<^typ>\<open>'n Quantity\<close> as dimension types are to \<^typ>\<open>Dimension\<close>. 
  Specifically, an element of \<^typ>\<open>('n', 'd) QuantT\<close> is a quantity whose dimension is \<^typ>\<open>'d\<close>.

  Intuitively, the formula \<^term>\<open>x :: 'n['d]\<close> can be read as ``$x$ is a quantity of \<^typ>\<open>'d\<close>'',
  for example it might be a quantity of length, or a quantity of mass. \<close>

text \<open> Since quantities can have dimension type expressions that are distinct, but denote the same
  dimension, it is necessary to define the following function for coercion between two dimension
  expressions. This requires that the underlying dimensions are the same. \<close>

definition coerceQuantT :: "'d\<^sub>2 itself \<Rightarrow> 'a['d\<^sub>1::dim_type] \<Rightarrow> 'a['d\<^sub>2::dim_type]" where
[si_def]: "QD('d\<^sub>1) = QD('d\<^sub>2) \<Longrightarrow> coerceQuantT t x = (toQ (fromQ x))"

syntax
  "_QCOERCE" :: "type \<Rightarrow> logic \<Rightarrow> logic" ("QCOERCE[_]")

translations
  "QCOERCE['t]" == "CONST coerceQuantT TYPE('t)"

subsection \<open> Predicates on Typed Quantities \<close>

text \<open> The standard HOL order \<^term>\<open>(\<le>)\<close> and equality \<^term>\<open>(=)\<close> have the homogeneous type
  \<^typ>\<open>'a \<Rightarrow> 'a \<Rightarrow> bool\<close> and so they cannot compare values of different types. Consequently,
  we define a heterogeneous order and equivalence on typed quantities. \<close>

lift_definition qless_eq :: "'n::order['a::dim_type] \<Rightarrow> 'n['b::dim_type] \<Rightarrow> bool" (infix "\<lesssim>\<^sub>Q" 50) 
  is "(\<le>)" .

lift_definition qequiv :: "'n['a::dim_type] \<Rightarrow> 'n['b::dim_type] \<Rightarrow> bool" (infix "\<cong>\<^sub>Q" 50) 
  is "(=)" .

text \<open> These are both fundamentally the same as the usual order and equality relations, but they
  permit potentially different dimension types, \<^typ>\<open>'a\<close> and \<^typ>\<open>'b\<close>. Two typed quantities are
  comparable only when the two dimension types have the same semantic dimension.
\<close>

lemma qequiv_refl [simp]: "a \<cong>\<^sub>Q a"
  by (simp add: qequiv_def)

lemma qequiv_sym: "a \<cong>\<^sub>Q b \<Longrightarrow> b \<cong>\<^sub>Q a"
  by (simp add: qequiv_def)

lemma qequiv_trans: "\<lbrakk> a \<cong>\<^sub>Q b; b \<cong>\<^sub>Q c \<rbrakk> \<Longrightarrow> a \<cong>\<^sub>Q c"
  by (simp add: qequiv_def)

theorem qeq_iff_same_dim:
  fixes x y :: "'a['d::dim_type]"
  shows "x \<cong>\<^sub>Q y \<longleftrightarrow> x = y"
  by (transfer, simp)

lemma coerceQuant_eq_iff:
  fixes x :: "'a['d\<^sub>1::dim_type]"
  assumes "QD('d\<^sub>1) = QD('d\<^sub>2::dim_type)"
  shows "(coerceQuantT TYPE('d\<^sub>2) x) \<cong>\<^sub>Q x"
  by (metis qequiv.rep_eq assms coerceQuantT_def toQ_cases toQ_inverse)

lemma coerceQuant_eq_iff2:
  fixes x :: "'a['d\<^sub>1::dim_type]"
  assumes "QD('d\<^sub>1) = QD('d\<^sub>2::dim_type)" and "y = (coerceQuantT TYPE('d\<^sub>2) x)"
  shows "x \<cong>\<^sub>Q y"
  using qequiv_sym assms(1) assms(2) coerceQuant_eq_iff by blast
 
lemma updown_eq_iff:
  fixes x :: "'a['d\<^sub>1::dim_type]" fixes y :: "'a['d\<^sub>2::dim_type]"
  assumes "QD('d\<^sub>1) = QD('d\<^sub>2::dim_type)" and "y = (toQ (fromQ x))"
  shows "x \<cong>\<^sub>Q y"
  by (simp add: assms(1) assms(2) coerceQuant_eq_iff2 coerceQuantT_def)

text\<open>This is more general that \<open>y = x \<Longrightarrow> x \<cong>\<^sub>Q y\<close>, since x and y may have different type.\<close>

lemma qeq: 
  fixes x :: "'a['d\<^sub>1::dim_type]" fixes y :: "'a['d\<^sub>2::dim_type]"
  assumes "x \<cong>\<^sub>Q y"
  shows "QD('d\<^sub>1) = QD('d\<^sub>2)"
  by (metis (full_types) qequiv.rep_eq assms fromQ mem_Collect_eq)

subsection\<open> Operators on Typed Quantities \<close>

text \<open> We define several operators on typed quantities. These variously compose the dimension types
  as well. Multiplication composes the two dimension types. Inverse constructs and inverted 
  dimension type. Division is defined in terms of multiplication and inverse. \<close>

lift_definition 
  qtimes :: "('n::comm_ring_1)['a::dim_type] \<Rightarrow> 'n['b::dim_type] \<Rightarrow> 'n['a \<cdot>'b]" (infixl "\<^bold>\<cdot>" 69) 
  is "(*)" by (simp add: dim_ty_sem_DimTimes_def times_Quantity_ext_def)

lift_definition 
  qinverse :: "('n::field)['a::dim_type] \<Rightarrow> 'n['a\<^sup>-\<^sup>1]" ("(_\<^sup>-\<^sup>\<one>)" [999] 999) 
  is "inverse" by (simp add: inverse_Quantity_ext_def dim_ty_sem_DimInv_def)

abbreviation (input)
  qdivide :: "('n::field)['a::dim_type] \<Rightarrow> 'n['b::dim_type] \<Rightarrow> 'n['a/'b]" (infixl "\<^bold>'/" 70) where
"qdivide x y \<equiv> x \<^bold>\<cdot> y\<^sup>-\<^sup>\<one>"

text \<open> We also provide some helpful notations for expressing heterogeneous powers. \<close>

abbreviation qsq         ("(_)\<^sup>\<two>"  [999] 999) where "u\<^sup>\<two> \<equiv> u\<^bold>\<cdot>u"
abbreviation qcube       ("(_)\<^sup>\<three>"  [999] 999) where "u\<^sup>\<three> \<equiv> u\<^bold>\<cdot>u\<^bold>\<cdot>u"
abbreviation qquart      ("(_)\<^sup>\<four>"  [999] 999) where "u\<^sup>\<four> \<equiv> u\<^bold>\<cdot>u\<^bold>\<cdot>u\<^bold>\<cdot>u"

abbreviation qneq_sq     ("(_)\<^sup>-\<^sup>\<two>" [999] 999) where "u\<^sup>-\<^sup>\<two> \<equiv> (u\<^sup>\<two>)\<^sup>-\<^sup>\<one>"
abbreviation qneq_cube   ("(_)\<^sup>-\<^sup>\<three>" [999] 999) where "u\<^sup>-\<^sup>\<three> \<equiv> (u\<^sup>\<three>)\<^sup>-\<^sup>\<one>"
abbreviation qneq_quart  ("(_)\<^sup>-\<^sup>\<four>" [999] 999) where "u\<^sup>-\<^sup>\<four> \<equiv> (u\<^sup>\<three>)\<^sup>-\<^sup>\<one>"

text \<open> Analogous to the \<^const>\<open>scaleR\<close> operator for vectors, we define the following scalar
  multiplication that scales an existing quantity by a numeric value. This operator is
  especially important for the representation of quantity values, which consist of a numeric
  value and a unit. \<close>

lift_definition scaleQ :: "'a \<Rightarrow> 'a::comm_ring_1['d::dim_type] \<Rightarrow> 'a['d]" (infixr "*\<^sub>Q" 63)
  is "\<lambda> r x. \<lparr> mag = r * mag x, dim = QD('d) \<rparr>" by simp

notation scaleQ (infixr "\<odot>" 63)

text \<open> Finally, we instantiate the arithmetic types classes where possible. We do not instantiate
  \<^class>\<open>times\<close> because this results in a nonsensical homogeneous product on quantities. \<close>

instantiation QuantT :: (zero,dim_type) zero
begin
lift_definition zero_QuantT :: "('a, 'b) QuantT" is "\<lparr> mag = 0, dim = QD('b) \<rparr>" 
  by simp
instance ..
end

instantiation QuantT :: (one,dim_type) one
begin
lift_definition one_QuantT :: "('a, 'b) QuantT" is "\<lparr> mag = 1, dim = QD('b) \<rparr>"
  by simp
instance ..
end

text \<open> The following specialised one element has both magnitude and dimension 1: it is a 
  dimensionless quantity. \<close>

abbreviation qone :: "'n::one[\<one>]" ("\<one>") where "qone \<equiv> 1"

text \<open> Unlike for semantic quantities, the plus operator on typed quantities is total, since the
  type system ensures that the dimensions (and the dimension types) must be the same. \<close>

instantiation QuantT :: (plus,dim_type) plus
begin
lift_definition plus_QuantT :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> 'a['b]"
  is "\<lambda> x y. \<lparr> mag = mag x + mag y, dim = QD('b) \<rparr>"
  by (simp)
instance ..
end

text \<open> We can also show that typed quantities are commutative \<^emph>\<open>additive\<close> monoids. Indeed, addition
  is a much easier operator to deal with in typed quantities, unlike product. \<close>

instance QuantT :: (semigroup_add,dim_type) semigroup_add
  by (intro_classes, transfer, simp add: add.assoc)

instance QuantT :: (ab_semigroup_add,dim_type) ab_semigroup_add
  by (intro_classes, transfer, simp add: add.commute)

instance QuantT :: (monoid_add,dim_type) monoid_add
  by (intro_classes; (transfer, simp))
  
instance QuantT :: (comm_monoid_add,dim_type) comm_monoid_add
  by (intro_classes; transfer, simp)

instantiation QuantT :: (uminus,dim_type) uminus
begin
lift_definition uminus_QuantT :: "'a['b] \<Rightarrow> 'a['b]" 
  is "\<lambda> x. \<lparr> mag = - mag x, dim = dim x \<rparr>" by (simp)
instance ..
end

instantiation QuantT :: (minus,dim_type) minus
begin
lift_definition minus_QuantT :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> 'a['b]"
  is "\<lambda> x y. \<lparr> mag = mag x - mag y, dim = dim x \<rparr>" by (simp)

instance ..
end

instance QuantT :: (numeral,dim_type) numeral ..

text \<open> Moreover, types quantities also form an additive group. \<close>

instance QuantT :: (ab_group_add,dim_type) ab_group_add
  by (intro_classes, (transfer, simp)+)

text \<open> Typed quantities helpfully can be both partially and a linearly ordered. \<close>

instantiation QuantT :: (order,dim_type) order
begin
  lift_definition less_eq_QuantT :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> bool" is "\<lambda> x y. mag x \<le> mag y" .
  lift_definition less_QuantT :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> bool" is "\<lambda> x y. mag x < mag y" .
  instance by (intro_classes, (transfer, simp add: less_le_not_le)+)
end

instance QuantT :: (linorder,dim_type) linorder
  by (intro_classes, transfer, auto)

instantiation QuantT :: (scaleR,dim_type) scaleR
begin
lift_definition scaleR_QuantT :: "real \<Rightarrow> 'a['b] \<Rightarrow> 'a['b]"
is "\<lambda> n q. \<lparr> mag = n *\<^sub>R mag q, dim = dim q \<rparr>" by (simp)
instance ..
end

instance QuantT :: (real_vector,dim_type) real_vector
  by (intro_classes, (transfer, simp add: scaleR_add_left scaleR_add_right)+)

instantiation QuantT :: (norm,dim_type) norm
begin
lift_definition norm_QuantT :: "'a['b] \<Rightarrow> real" 
is "\<lambda> x. norm (mag x)" .
instance ..
end

instantiation QuantT :: (sgn_div_norm,dim_type) sgn_div_norm
begin
definition sgn_QuantT :: "'a['b] \<Rightarrow> 'a['b]" where
"sgn_QuantT x = x /\<^sub>R norm x"
instance by (intro_classes, simp add: sgn_QuantT_def)
end

instantiation QuantT :: (dist_norm,dim_type) dist_norm
begin
definition dist_QuantT :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> real" where
"dist_QuantT x y = norm (x - y)"
instance
  by (intro_classes, simp add: dist_QuantT_def)
end

instantiation QuantT :: ("{uniformity_dist,dist_norm}",dim_type) uniformity_dist
begin
definition uniformity_QuantT :: "('a['b] \<times> 'a['b]) filter" where
"uniformity_QuantT = (INF e\<in>{0 <..}. principal {(x, y). dist x y < e})"
instance
  by (intro_classes, simp add: uniformity_QuantT_def)
end

instantiation QuantT :: ("{dist_norm,open_uniformity,uniformity_dist}",dim_type) open_uniformity
begin

definition open_QuantT :: "('a['b]) set \<Rightarrow> bool" where
"open_QuantT U = (\<forall>x\<in>U. eventually (\<lambda>(x', y). x' = x \<longrightarrow> y \<in> U) uniformity)"
instance by (intro_classes, simp add: open_QuantT_def)
end

text \<open> Quantities form a real normed vector space. \<close>

instance QuantT :: (real_normed_vector,dim_type) real_normed_vector
  by (intro_classes; transfer, auto simp add: norm_triangle_ineq)

end