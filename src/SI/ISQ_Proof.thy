section \<open> Proof Support for Quantities \<close>

theory ISQ_Proof
  imports ISQ_Quantities
begin

named_theorems si_transfer

definition magQ :: "'a['u::dim_type] \<Rightarrow> 'a" ("\<lbrakk>_\<rbrakk>\<^sub>Q") where
[si_def]: "magQ x = mag (fromQ x)"

definition dimQ :: "'a['u::dim_type] \<Rightarrow> Dimension" where
[si_def]: "dimQ x = dim (fromQ x)"

lemma unit_eq_iff_mag_eq [si_transfer]:
  "x = y \<longleftrightarrow> \<lbrakk>x\<rbrakk>\<^sub>Q = \<lbrakk>y\<rbrakk>\<^sub>Q"
  by (auto simp add: magQ_def, transfer, simp)

lemma unit_equiv_iff [si_transfer]:
  fixes x :: "'a['u\<^sub>1::dim_type]" and y :: "'a['u\<^sub>2::dim_type]"
  shows "x \<cong>\<^sub>Q y \<longleftrightarrow> \<lbrakk>x\<rbrakk>\<^sub>Q = \<lbrakk>y\<rbrakk>\<^sub>Q \<and> QD('u\<^sub>1) = QD('u\<^sub>2)"
proof -
  have "\<forall>t ta. (ta::'a['u\<^sub>2]) = t \<or> mag (fromQ ta) \<noteq> mag (fromQ t)"
    by (simp add: magQ_def unit_eq_iff_mag_eq)
  then show ?thesis
    by (metis (full_types) qequiv.rep_eq coerceQuant_eq_iff2 qeq magQ_def)
qed

lemma unit_le_iff_magn_le [si_transfer]:
  "x \<le> y \<longleftrightarrow> \<lbrakk>x\<rbrakk>\<^sub>Q \<le> \<lbrakk>y\<rbrakk>\<^sub>Q"
  by (auto simp add: magQ_def; (transfer, simp))

lemma magQ_zero [si_eq]: "\<lbrakk>0\<rbrakk>\<^sub>Q = 0"
  by (simp add: magQ_def, transfer, simp)

lemma magQ_one [si_eq]: "\<lbrakk>1\<rbrakk>\<^sub>Q = 1"
  by (simp add: magQ_def, transfer, simp)

lemma magQ_plus [si_eq]: "\<lbrakk>x + y\<rbrakk>\<^sub>Q = \<lbrakk>x\<rbrakk>\<^sub>Q + \<lbrakk>y\<rbrakk>\<^sub>Q"
  by (simp add: magQ_def, transfer, simp)

lemma magQ_minus [si_eq]: "\<lbrakk>x - y\<rbrakk>\<^sub>Q = \<lbrakk>x\<rbrakk>\<^sub>Q - \<lbrakk>y\<rbrakk>\<^sub>Q"
  by (simp add: magQ_def, transfer, simp)

lemma magQ_uminus [si_eq]: "\<lbrakk>- x\<rbrakk>\<^sub>Q = - \<lbrakk>x\<rbrakk>\<^sub>Q"
  by (simp add: magQ_def, transfer, simp)

lemma magQ_scaleQ [si_eq]: "\<lbrakk>x *\<^sub>Q y\<rbrakk>\<^sub>Q = x * \<lbrakk>y\<rbrakk>\<^sub>Q"
  by (simp add: magQ_def, transfer, simp)

lemma magQ_qtimes [si_eq]: "\<lbrakk>x \<^bold>\<cdot> y\<rbrakk>\<^sub>Q = \<lbrakk>x\<rbrakk>\<^sub>Q \<cdot> \<lbrakk>y\<rbrakk>\<^sub>Q"
  by (simp add: magQ_def, transfer, simp)

lemma magQ_qinverse [si_eq]: "\<lbrakk>x\<^sup>-\<^sup>\<one>\<rbrakk>\<^sub>Q = inverse \<lbrakk>x\<rbrakk>\<^sub>Q"
  by (simp add: magQ_def, transfer, simp)

lemma magQ_qdivivide [si_eq]: "\<lbrakk>(x::('a::field)[_]) \<^bold>/ y\<rbrakk>\<^sub>Q = \<lbrakk>x\<rbrakk>\<^sub>Q / \<lbrakk>y\<rbrakk>\<^sub>Q"
  by (simp add: magQ_def, transfer, simp add: field_class.field_divide_inverse)

lemma magQ_numeral [si_eq]: "\<lbrakk>numeral n\<rbrakk>\<^sub>Q = numeral n"
  apply (induct n, simp_all add: si_def)
  apply (metis magQ_def magQ_one)
  apply (metis magQ_def magQ_plus numeral_code(2))
  apply (metis magQ_def magQ_one magQ_plus numeral_code(3))
  done

text \<open> The following tactic breaks an SI conjecture down to numeric and unit properties \<close>

method si_simp uses add =
  (simp add: add si_transfer si_eq field_simps)

text \<open> The next tactic additionally compiles the semantics of the underlying units \<close>

method si_calc uses add = 
  (si_simp add: add; simp add: si_def add)

lemma "QD(N \<cdot> \<Theta> \<cdot> N) = QD(\<Theta> \<cdot> N\<^sup>2)" by (simp add: si_eq si_def)

end