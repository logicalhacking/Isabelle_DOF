section \<open> Multiplication Group Classes \<close>

theory Groups_mult
  imports Main
begin

notation times (infixl "\<cdot>" 70)

class group_mult = inverse + monoid_mult +
  assumes left_inverse: "inverse a \<cdot> a = 1"
  assumes multi_inverse_conv_div [simp]: "a \<cdot> (inverse b) = a / b"
begin

lemma div_conv_mult_inverse: "a / b = a \<cdot> (inverse b)"
  by simp

sublocale mult: group times 1 inverse
  by standard (simp_all add: left_inverse)

lemma diff_self [simp]: "a / a = 1"
  using mult.right_inverse by auto

lemma mult_distrib_inverse [simp]: "(a * b) / b = a"
  by (metis local.mult_1_right local.multi_inverse_conv_div mult.right_inverse mult_assoc)

end

class ab_group_mult = comm_monoid_mult + group_mult
begin

lemma mult_distrib_inverse' [simp]: "(a * b) / a = b"
  using local.mult_distrib_inverse mult_commute by fastforce

lemma inverse_distrib: "inverse (a * b)  =  (inverse a) * (inverse b)"
  by (simp add: local.mult.inverse_distrib_swap mult_commute)

end

end