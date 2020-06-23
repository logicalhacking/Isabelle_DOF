section \<open> Algebraic Laws \<close>

theory ISQ_Algebra
  imports ISQ_Proof
begin

subsection \<open> Quantity Scale \<close>

lemma scaleQ_add_right: "a \<odot> x + y = (a \<odot> x) + (a \<odot> y)"
  by (si_simp add: distrib_left)

lemma scaleQ_add_left: "a + b \<odot> x = (a \<odot> x) + (b \<odot> x)"
  by (si_simp add: distrib_right)

lemma scaleQ_scaleQ: "a \<odot> b \<odot> x = a \<cdot> b \<odot> x"
  by si_simp

lemma scaleQ_one [simp]: "1 \<odot> x = x"
  by si_simp

lemma scaleQ_zero [simp]: "0 \<odot> x = 0"
  by si_simp

lemma scaleQ_inv: "-a \<odot> x = a \<odot> -x"
  by si_calc

lemma scaleQ_as_qprod: "a \<odot> x \<cong>\<^sub>Q (a \<odot> \<one>) \<^bold>\<cdot> x"
  by (si_simp)

lemma mult_scaleQ_left [simp]: "(a \<odot> x) \<^bold>\<cdot> y = a \<odot> x \<^bold>\<cdot> y"
  by (si_simp add: mult.assoc)

lemma mult_scaleQ_right [simp]: "x \<^bold>\<cdot> (a \<odot> y) = a \<odot> x \<^bold>\<cdot> y"
  by si_simp

subsection \<open> Field Laws \<close>

lemma qtimes_commute: "x \<^bold>\<cdot> y \<cong>\<^sub>Q y \<^bold>\<cdot> x"
  by si_calc

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
  using assms by si_simp

lemma qtimes_weak_cong_right:
  assumes "x \<cong>\<^sub>Q y"
  shows  "z\<^bold>\<cdot>x \<cong>\<^sub>Q z\<^bold>\<cdot>y"
  using assms by si_calc

lemma qinverse_weak_cong:
  assumes "x \<cong>\<^sub>Q y"
  shows   "x\<^sup>-\<^sup>\<one> \<cong>\<^sub>Q y\<^sup>-\<^sup>\<one>"
  using assms by si_calc

lemma scaleQ_cong:
  assumes "y \<cong>\<^sub>Q z"
  shows "x \<odot> y \<cong>\<^sub>Q x \<odot> z"
  using assms by si_calc

lemma qinverse_qinverse: "x\<^sup>-\<^sup>\<one>\<^sup>-\<^sup>\<one> \<cong>\<^sub>Q x"
  by si_calc

lemma qinverse_nonzero_iff_nonzero: "x\<^sup>-\<^sup>\<one> = 0 \<longleftrightarrow> x = 0"
  by (auto, si_calc+)

lemma qinverse_qtimes: "(x \<^bold>\<cdot> y)\<^sup>-\<^sup>\<one> \<cong>\<^sub>Q x\<^sup>-\<^sup>\<one> \<^bold>\<cdot> y\<^sup>-\<^sup>\<one>"
  by si_calc

lemma qinverse_qdivide: "(x \<^bold>/ y)\<^sup>-\<^sup>\<one> \<cong>\<^sub>Q y \<^bold>/ x"
  by si_calc

lemma qtimes_cancel: "x \<noteq> 0 \<Longrightarrow> x \<^bold>/ x \<cong>\<^sub>Q \<one>"
  by si_calc

end
