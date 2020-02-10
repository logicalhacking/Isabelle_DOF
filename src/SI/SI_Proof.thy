theory SI_Proof
  imports SI_Derived
begin

section \<open> Tactic Support for SI type expressions. \<close>

lemmas [si_def] =  si_sem_meter_def si_sem_kilogram_def si_sem_second_def 
                   si_sem_ampere_def si_sem_kelvin_def si_sem_mole_def
                   si_sem_candela_def 

                   si_sem_UnitTimes_def si_sem_UnitInv_def
                   times_Unit_ext_def one_Unit_ext_def
                   
(* renaming and putting defs into the rewrite set (which is usually not a good idea) *)
lemma "SI(meter)   = 1\<lparr>Meters := 1\<rparr>"     by(simp add: si_def)
lemma "SI(kilogram)= 1\<lparr>Kilograms := 1\<rparr>"  by(simp add: si_def)
lemma "SI(second)  = 1\<lparr>Seconds := 1\<rparr> "   by(simp add: si_def)
lemma "SI(ampere)  = 1\<lparr>Amperes := 1\<rparr>"    by(simp add: si_def)
lemma "SI(kelvin)  = 1\<lparr>Kelvins := 1\<rparr> "   by(simp add: si_def)
lemma "SI(mole)    = 1\<lparr>Moles := 1\<rparr>"      by(simp add: si_def)
lemma "SI(candela) = 1\<lparr>Candelas := 1\<rparr>"   by(simp add: si_def)

lemma "SI(mole \<cdot> kelvin \<cdot> mole) = SI(kelvin \<cdot> (mole)\<^sup>2)" by(simp add: si_def)

lemma [si_def]:"fromUnit UNIT(x::'a::one, second) = 
                  \<lparr>magn = x,
                   unit = \<lparr>Seconds = 1, Meters = 0, Kilograms = 0, Amperes = 0, 
                           Kelvins = 0, Moles = 0, Candelas = 0\<rparr>\<rparr>"
  by (simp add: mk_unit.rep_eq one_Unit_ext_def si_sem_second_def)

lemma [si_def]:"fromUnit UNIT(x::'a::one, meter) = 
                  \<lparr>magn = x,
                   unit = \<lparr>Seconds = 0, Meters = 1, Kilograms = 0, Amperes = 0, 
                           Kelvins = 0, Moles = 0, Candelas = 0\<rparr>\<rparr>"
  by (simp add: mk_unit.rep_eq one_Unit_ext_def si_sem_meter_def)

lemma [si_def]:"fromUnit UNIT(x::'a::one, kilogram) = 
                  \<lparr>magn = x,
                   unit = \<lparr>Seconds = 0, Meters = 0, Kilograms = 1, Amperes = 0, 
                           Kelvins = 0, Moles = 0, Candelas = 0\<rparr>\<rparr>"
  by (simp add: mk_unit.rep_eq one_Unit_ext_def si_sem_kilogram_def)

lemma [si_def]:"fromUnit UNIT(x::'a::one, ampere) = 
                  \<lparr>magn = x,
                   unit = \<lparr>Seconds = 0, Meters = 0, Kilograms = 0, Amperes = 1, 
                           Kelvins = 0, Moles = 0, Candelas = 0\<rparr>\<rparr>"
  by (simp add: mk_unit.rep_eq one_Unit_ext_def si_sem_ampere_def)

lemma [si_def]:"fromUnit UNIT(x::'a::one, kelvin) = 
                  \<lparr>magn = x,
                   unit = \<lparr>Seconds = 0, Meters = 0, Kilograms = 0, Amperes = 0, 
                           Kelvins = 1, Moles = 0, Candelas = 0\<rparr>\<rparr>"
  by (simp add: mk_unit.rep_eq one_Unit_ext_def si_sem_kelvin_def)

lemma [si_def]:"fromUnit UNIT(x::'a::one, mole) = 
                  \<lparr>magn = x,
                   unit = \<lparr>Seconds = 0, Meters = 0, Kilograms = 0, Amperes = 0, 
                           Kelvins = 0, Moles = 1, Candelas = 0\<rparr>\<rparr>"
  by (simp add: mk_unit.rep_eq one_Unit_ext_def si_sem_mole_def)

lemma [si_def]:"fromUnit UNIT(x::'a::one, candela) = 
                  \<lparr>magn = x,
                   unit = \<lparr>Seconds = 0, Meters = 0, Kilograms = 0, Amperes = 0, 
                           Kelvins = 0, Moles = 0, Candelas = 1\<rparr>\<rparr>"
  by (simp add: mk_unit.rep_eq one_Unit_ext_def si_sem_candela_def)

lemma Unit_times_commute:
  fixes X::"'a::{one,ab_semigroup_mult}['b::si_type]"and Y::"'a['c::si_type]"
  shows "X \<^bold>\<cdot> Y  \<approx>\<^sub>Q  Y \<^bold>\<cdot> X"
  by (transfer, simp add: mult.commute times_Quantity_ext_def)

text\<open>Observe that this commutation law also commutes the types.\<close>
 
(* just a check that instantiation works for special cases ... *)
lemma "    (UNIT(x, candela) \<^bold>\<cdot> UNIT(y::'a::{one,ab_semigroup_mult}, mole))
        \<approx>\<^sub>Q (UNIT(y, mole) \<^bold>\<cdot> UNIT(x, candela)) "
  by(simp add: Unit_times_commute)


lemma Unit_times_assoc:
  fixes X::"'a::{one,ab_semigroup_mult}['b::si_type]"
    and Y::"'a['c::si_type]"
    and Z::"'a['d::si_type]"
  shows  "(X \<^bold>\<cdot> Y) \<^bold>\<cdot> Z  \<approx>\<^sub>Q  X \<^bold>\<cdot> (Y \<^bold>\<cdot> Z)"
  by (transfer, simp add: mult.commute mult.left_commute times_Quantity_ext_def)

text\<open>The following weak congruences will allow for replacing equivalences in contexts
     built from product and inverse. \<close>
lemma Unit_times_weak_cong_left:
  fixes X::"'a::{one,ab_semigroup_mult}['b::si_type]"
    and Y::"'a['c::si_type]"
    and Z::"'a['d::si_type]"
  assumes "X \<approx>\<^sub>Q Y"
  shows  "(X \<^bold>\<cdot> Z)  \<approx>\<^sub>Q  (Y \<^bold>\<cdot> Z)"
  using assms by (transfer, simp)

lemma Unit_times_weak_cong_right:
  fixes X::"'a::{one,ab_semigroup_mult}['b::si_type]"
    and Y::"'a['c::si_type]"
    and Z::"'a['d::si_type]"
  assumes "X \<approx>\<^sub>Q Y"
  shows  "(Z \<^bold>\<cdot> X)  \<approx>\<^sub>Q  (Z \<^bold>\<cdot> Y)"
  using assms by (transfer, simp)

lemma Unit_inverse_weak_cong:
  fixes   X::"'a::{field}['b::si_type]"
    and   Y::"'a['c::si_type]"
  assumes "X  \<approx>\<^sub>Q Y"
  shows   "(X)\<^sup>-\<^sup>\<one>  \<approx>\<^sub>Q  (Y)\<^sup>-\<^sup>\<one>"
  using assms by (transfer, simp)

text\<open>In order to compute a normal form, we would additionally need these three:\<close>
(* field ? *)
lemma Unit_inverse_distrib:
  fixes X::"'a::{field}['b::si_type]"
    and Y::"'a['c::si_type]"
  shows "(X \<^bold>\<cdot> Y)\<^sup>-\<^sup>\<one>  \<approx>\<^sub>Q  X\<^sup>-\<^sup>\<one> \<^bold>\<cdot> Y\<^sup>-\<^sup>\<one>"
  apply (transfer)
  sorry

(* field ? *)
lemma Unit_inverse_inverse:
  fixes X::"'a::{field}['b::si_type]"
  shows "((X)\<^sup>-\<^sup>\<one>)\<^sup>-\<^sup>\<one>  \<approx>\<^sub>Q  X"
  apply transfer
  sorry

(* field ? *)
lemma Unit_mult_cancel:
  fixes  X::"'a::{field}['b::si_type]"
  shows  "X \<^bold>/ X  \<approx>\<^sub>Q  1"
  apply transfer
  sorry


lemma Unit_mult_mult_Left_cancel:
  fixes  X::"'a::{field}['b::si_type]"
  shows  "(1::'a['b/'b]) \<^bold>\<cdot> X  \<approx>\<^sub>Q  X"
  apply transfer
  sorry


lemma "watt \<^bold>\<cdot> hour \<approx>\<^sub>Q 3600 \<^bold>\<cdot> joule"
  apply (transfer)
  unfolding Unit_equiv_def hour_def
  apply(simp add: Units.Unit_times.rep_eq si_def 
                 zero_SI_tagged_domain_ext_def times_SI_tagged_domain_ext_def 
                 inverse_SI_tagged_domain_ext_def 
                 Unit_inverse_def Unit_times_def)
  find_theorems fromUnit
  oops

  thm Units.Unit.toUnit_inverse


lemma "watt \<^bold>\<cdot> hour \<approx>\<^sub>Q 3.6 \<^bold>\<cdot> kilo \<^bold>\<cdot> joule"
  oops


end