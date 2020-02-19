section \<open> Tactic Support for SI type expressions. \<close>

theory SI_Proof
  imports SI_Quantities
begin

definition magnQuant :: "'a['u::si_type] \<Rightarrow> 'a" ("\<lbrakk>_\<rbrakk>\<^sub>Q") where
[si_def]: "magnQuant x = magn (fromQ x)"

lemma unit_eq_iff_magn_eq:
  "x = y \<longleftrightarrow> \<lbrakk>x\<rbrakk>\<^sub>Q = \<lbrakk>y\<rbrakk>\<^sub>Q"
  by (auto simp add: magnQuant_def, transfer, simp)

lemma unit_equiv_iff:
  fixes x :: "'a['u\<^sub>1::si_type]" and y :: "'a['u\<^sub>2::si_type]"
  shows "x \<cong>\<^sub>Q y \<longleftrightarrow> \<lbrakk>x\<rbrakk>\<^sub>Q = \<lbrakk>y\<rbrakk>\<^sub>Q \<and> SI('u\<^sub>1) = SI('u\<^sub>2)"
proof -
  have "\<forall>t ta. (ta::'a['u\<^sub>2]) = t \<or> magn (fromQ ta) \<noteq> magn (fromQ t)"
    by (simp add: magnQuant_def unit_eq_iff_magn_eq)
  then show ?thesis
    by (metis (full_types) qequiv.rep_eq coerceQuant_eq_iff2 eq_ magnQuant_def)
qed

lemma unit_le_iff_magn_le:
  "x \<le> y \<longleftrightarrow> \<lbrakk>x\<rbrakk>\<^sub>Q \<le> \<lbrakk>y\<rbrakk>\<^sub>Q"
  by (auto simp add: magnQuant_def; (transfer, simp))

lemma magnQuant_zero [si_eq]: "\<lbrakk>0\<rbrakk>\<^sub>Q = 0"
  by (simp add: magnQuant_def, transfer, simp)

lemma magnQuant_one [si_eq]: "\<lbrakk>1\<rbrakk>\<^sub>Q = 1"
  by (simp add: magnQuant_def, transfer, simp)

lemma magnQuant_plus [si_eq]: "\<lbrakk>x + y\<rbrakk>\<^sub>Q = \<lbrakk>x\<rbrakk>\<^sub>Q + \<lbrakk>y\<rbrakk>\<^sub>Q"
  by (simp add: magnQuant_def, transfer, simp)

lemma magnQuant_scaleQ [si_eq]: "\<lbrakk>x *\<^sub>Q y\<rbrakk>\<^sub>Q = x * \<lbrakk>y\<rbrakk>\<^sub>Q"
  by (simp add: magnQuant_def, transfer, simp)

lemma magnQuant_qtimes [si_eq]: "\<lbrakk>x \<^bold>\<cdot> y\<rbrakk>\<^sub>Q = \<lbrakk>x\<rbrakk>\<^sub>Q \<cdot> \<lbrakk>y\<rbrakk>\<^sub>Q"
  by (simp add: magnQuant_def, transfer, simp)

lemma magnQuant_qinverse [si_eq]: "\<lbrakk>x\<^sup>-\<^sup>\<one>\<rbrakk>\<^sub>Q = inverse \<lbrakk>x\<rbrakk>\<^sub>Q"
  by (simp add: magnQuant_def, transfer, simp)

lemma magnQuant_qdivivide [si_eq]: "\<lbrakk>(x::('a::field)[_]) \<^bold>/ y\<rbrakk>\<^sub>Q = \<lbrakk>x\<rbrakk>\<^sub>Q / \<lbrakk>y\<rbrakk>\<^sub>Q"
  by (simp add: magnQuant_def, transfer, simp add: field_class.field_divide_inverse)

lemma magnQuant_numeral [si_eq]: "\<lbrakk>numeral n\<rbrakk>\<^sub>Q = numeral n"
  apply (induct n, simp_all add: si_def)
  apply (metis magnQuant_def magnQuant_one)
  apply (metis magnQuant_def magnQuant_plus numeral_code(2))
  apply (metis magnQuant_def magnQuant_one magnQuant_plus numeral_code(3))
  done

lemma magnQuant_mk [si_eq]: "\<lbrakk>UNIT(n, 'u::si_type)\<rbrakk>\<^sub>Q = n"
  by (simp add: magnQuant_def, transfer, simp)

method si_calc uses simps = 
  (simp add: unit_equiv_iff unit_eq_iff_magn_eq unit_le_iff_magn_le si_eq simps)

lemmas [si_eq] = si_sem_Length_def si_sem_Mass_def si_sem_Time_def 
                   si_sem_Current_def si_sem_Temperature_def si_sem_Amount_def
                   si_sem_Intensity_def si_sem_NoDimension_def
                   si_sem_UnitTimes_def si_sem_UnitInv_def
                   inverse_Unit_ext_def times_Unit_ext_def one_Unit_ext_def

lemmas [si_def] =  si_sem_Length_def si_sem_Mass_def si_sem_Time_def 
                   si_sem_Current_def si_sem_Temperature_def si_sem_Amount_def
                   si_sem_Intensity_def si_sem_NoDimension_def

                   si_sem_UnitTimes_def si_sem_UnitInv_def
                   times_Unit_ext_def one_Unit_ext_def
                   
(* renaming and putting defs into the rewrite set (which is usually not a good idea) *)
lemma "SI(L)  = 1\<lparr>Meters := 1\<rparr>"     by(simp add: si_def)
lemma "SI(M)  = 1\<lparr>Kilograms := 1\<rparr>"  by(simp add: si_def)
lemma "SI(T)  = 1\<lparr>Seconds := 1\<rparr> "   by(simp add: si_def)
lemma "SI(I)  = 1\<lparr>Amperes := 1\<rparr>"    by(simp add: si_def)
lemma "SI(\<Theta>)  = 1\<lparr>Kelvins := 1\<rparr> "   by(simp add: si_def)
lemma "SI(N)  = 1\<lparr>Moles := 1\<rparr>"      by(simp add: si_def)
lemma "SI(J)  = 1\<lparr>Candelas := 1\<rparr>"   by(simp add: si_def)
lemma "SI(\<one>)  = 1"                 by(simp add: si_def)

lemma "SI(N \<cdot> \<Theta> \<cdot> N) = SI(\<Theta> \<cdot> N\<^sup>2)" by(simp add: si_def)

end