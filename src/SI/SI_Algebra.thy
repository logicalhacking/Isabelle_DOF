section \<open> Algebraic Laws \<close>

theory SI_Algebra
  imports SI_Proof
begin

subsection \<open> Quantity Scale \<close>

lemma scaleQ_add_right: "a \<odot> x + y = (a \<odot> x) + (a \<odot> y)"
  by (transfer, simp add: distrib_left)

lemma scaleQ_add_left: "a + b \<odot> x = (a \<odot> x) + (b \<odot> x)"
  by (transfer, simp add: distrib_right)

lemma scaleQ_scaleQ: "a \<odot> b \<odot> x = a \<cdot> b \<odot> x"
  by (transfer, simp add: mult.assoc)

lemma scaleQ_one [simp]: "1 \<odot> x = x"
  by (transfer, simp)

lemma scaleQ_zero [simp]: "0 \<odot> x = 0"
  by (transfer, simp)

lemma scaleQ_inv: "-a \<odot> x = a \<odot> -x"
  by (transfer, simp)

lemma scaleQ_as_qprod: "a \<odot> x \<cong>\<^sub>Q (a \<odot> \<one>) \<^bold>\<cdot> x"
  unfolding si_def
  by (transfer, simp add: si_sem_NoDimension_def)

lemma mult_scaleQ_left [simp]: "(a \<odot> x) \<^bold>\<cdot> y = a \<odot> x \<^bold>\<cdot> y"
  by (transfer, simp add: si_sem_UnitTimes_def mult.assoc)

lemma mult_scaleQ_right [simp]: "x \<^bold>\<cdot> (a \<odot> y) = a \<odot> x \<^bold>\<cdot> y"
  by (transfer, simp add: si_sem_UnitTimes_def times_Quantity_ext_def mult.assoc)

subsection \<open> Field Laws \<close>

lemma qtimes_commute: "x \<^bold>\<cdot> y \<cong>\<^sub>Q y \<^bold>\<cdot> x"
  by si_calc

text\<open>Observe that this commutation law also commutes the types.\<close>
 
(* just a check that instantiation works for special cases ... *)
lemma "    (UNIT(x, J) \<^bold>\<cdot> UNIT(y::'a::comm_ring_1, N))
        \<cong>\<^sub>Q (UNIT(y, N) \<^bold>\<cdot> UNIT(x, J)) "
  by(simp add: qtimes_commute)

lemma qtimes_assoc: "(x \<^bold>\<cdot> y) \<^bold>\<cdot> z  \<cong>\<^sub>Q  x \<^bold>\<cdot> (y \<^bold>\<cdot> z)"
  by (si_calc)

lemma qtimes_left_unit: "\<one> \<^bold>\<cdot> x \<cong>\<^sub>Q x"
  by (si_calc)

lemma qtimes_right_unit: "x \<^bold>\<cdot> \<one> \<cong>\<^sub>Q x"
  by (si_calc)

text\<open>The following weak congruences will allow for replacing equivalences in contexts
     built from product and inverse. \<close>

lemma qtimes_weak_cong_left:
  assumes "x \<cong>\<^sub>Q y"
  shows  "x\<^bold>\<cdot>z \<cong>\<^sub>Q y\<^bold>\<cdot>z"
  using assms by si_calc

lemma qtimes_weak_cong_right:
  assumes "x \<cong>\<^sub>Q y"
  shows  "z\<^bold>\<cdot>x \<cong>\<^sub>Q z\<^bold>\<cdot>y"
  using assms by si_calc

lemma qinverse_weak_cong:
  assumes "x \<cong>\<^sub>Q y"
  shows   "x\<^sup>-\<^sup>\<one> \<cong>\<^sub>Q y\<^sup>-\<^sup>\<one>"
  using assms by si_calc

lemma qinverse_qinverse: "x\<^sup>-\<^sup>\<one>\<^sup>-\<^sup>\<one> \<cong>\<^sub>Q x"
  by si_calc

lemma qinverse_nonzero_iff_nonzero: "x\<^sup>-\<^sup>\<one> = 0 \<longleftrightarrow> x = 0"
  by si_calc

lemma qinverse_qtimes: "(x \<^bold>\<cdot> y)\<^sup>-\<^sup>\<one> \<cong>\<^sub>Q x\<^sup>-\<^sup>\<one> \<^bold>\<cdot> y\<^sup>-\<^sup>\<one>"
  by si_calc

lemma qinverse_qdivide: "(x \<^bold>/ y)\<^sup>-\<^sup>\<one> \<cong>\<^sub>Q y \<^bold>/ x"
  by si_calc

lemma qtimes_cancel: "x \<noteq> 0 \<Longrightarrow> x \<^bold>/ x \<cong>\<^sub>Q \<one>"
  by si_calc

end
