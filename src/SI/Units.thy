section \<open> SI Units \<close>

theory Units
  imports Groups_mult HOL.Transcendental "HOL-Eisbach.Eisbach"
begin

subsection \<open> Data-level Units \<close>

text \<open> We first specify the seven base units \<close>

datatype SIBaseUnit = Second | Meter | Kilogram | Ampere | Kelvin | Mole | Candela

text \<open> An SI unit associates with each base unit an integer that denotes the 
  power to which it is raised. \<close>

typedef SIUnit = "UNIV :: (SIBaseUnit \<Rightarrow> int) set" ..

setup_lifting type_definition_SIUnit

text \<open> We define a commutative monoid for SI units. \<close>

instantiation SIUnit :: comm_monoid_mult
begin
  \<comment> \<open> Here, $1$ is the dimensionless unit \<close>
  lift_definition one_SIUnit :: "SIUnit" is "\<lambda> u. 0" .
  \<comment> \<open> Multiplication is defined by adding together the powers \<close>
  lift_definition times_SIUnit :: "SIUnit \<Rightarrow> SIUnit \<Rightarrow> SIUnit" is
  "\<lambda> f g u. f u + g u" .
  instance proof
    fix a b c :: "SIUnit"
    show "a * b * c = a * (b * c)"
      by (transfer, simp add: fun_eq_iff)
    show "a * b = b * a"
      by (transfer, simp add: fun_eq_iff)
    show "1 * a = a"
      by (transfer, simp add: fun_eq_iff)
  qed
end

text \<open> We also define the inverse and division operations, and an abelian group. \<close>

instantiation SIUnit :: ab_group_mult
begin
  lift_definition inverse_SIUnit :: "SIUnit \<Rightarrow> SIUnit" is "\<lambda> f u. - (f u)" .
  definition divide_SIUnit :: "SIUnit \<Rightarrow> SIUnit \<Rightarrow> SIUnit" where
    "divide_SIUnit x y = x * (inverse y)"
  instance proof
    fix a b :: SIUnit
    show "inverse a \<cdot> a  = 1"
      by (transfer, simp add: fun_eq_iff)
    show "a \<cdot> inverse b = a div b"
      by (simp add: divide_SIUnit_def)
  qed
end

text \<open> A base unit is an SI unit here precisely one unit has power 1. \<close>

lift_definition mk_BaseUnit :: "SIBaseUnit \<Rightarrow> SIUnit" is "\<lambda> u. (\<lambda> i. 0)(u := 1)" .

lift_definition is_BaseUnit :: "SIUnit \<Rightarrow> bool" is "\<lambda> x. (\<exists> u::SIBaseUnit. x = (\<lambda> i. 0)(u := 1))" .

lemma is_BaseUnit_mk [simp]: "is_BaseUnit (mk_BaseUnit u)"
  by (transfer, auto simp add: mk_BaseUnit_def is_BaseUnit_def)

record 'a SI =
  factor :: 'a
  unit   :: SIUnit

instantiation unit :: comm_monoid_add
begin
  definition "zero_unit = ()"
  definition "plus_unit (x::unit) (y::unit) = ()"
  instance proof qed (simp_all)
end

instantiation unit :: comm_monoid_mult
begin
  definition "one_unit = ()"
  definition "times_unit (x::unit) (y::unit) = ()"
  instance proof qed (simp_all)
end

instantiation unit :: inverse
begin
  definition "inverse_unit (x::unit) = ()"
  definition "divide_unit (x::unit) (y::unit) = ()"
  instance ..
end

instantiation SI_ext :: (times, times) times
begin
  definition "times_SI_ext x y = \<lparr> factor = factor x \<cdot> factor y, unit = unit x \<cdot> unit y, \<dots> = more x \<cdot> more y \<rparr>"
instance ..
end

instantiation SI_ext :: (zero, zero) zero
begin
  definition "zero_SI_ext = \<lparr> factor = 0, unit = 1, \<dots> = 0 \<rparr>"
instance ..
end

instantiation SI_ext :: (one, one) one
begin
  definition "one_SI_ext = \<lparr> factor = 1, unit = 1, \<dots> = 1 \<rparr>"
instance ..
end

instantiation SI_ext :: (inverse, inverse) inverse
begin
  definition "inverse_SI_ext x = \<lparr> factor = inverse (factor x), unit = inverse (unit x), \<dots> = inverse (more x) \<rparr>"
  definition "divide_SI_ext x y = \<lparr> factor = factor x / factor y, unit = unit x / unit y, \<dots> = more x / more y \<rparr>"
instance ..
end

instance SI_ext :: (comm_monoid_mult, comm_monoid_mult) comm_monoid_mult
  by (intro_classes, simp_all add: one_SI_ext_def times_SI_ext_def mult.assoc, simp add: mult.commute)

subsection \<open> Type-level Units \<close>

subsubsection \<open> Classes \<close>

text \<open> A type class for unit denoting types. A type-level unit is a singleton type that associates
  with an value-level SI unit. \<close>

class siunit = finite +
  fixes siunit_of :: "'a itself \<Rightarrow> SIUnit"
  assumes unitary_unit_pres: "card (UNIV::'a set) = 1"

syntax
  "_SI" :: "type \<Rightarrow> logic" ("SI'(_')")

translations
  "SI('a)" == "CONST siunit_of TYPE('a)"

text \<open> An SI base unit type has a value-level base unit. \<close>

class sibaseunit = siunit +
  assumes is_BaseUnit: "is_BaseUnit SI('a)"

text \<open> Two SI types are equivalent if they have the same value-level units. \<close>

definition unit_equiv :: "'a::siunit \<Rightarrow> 'b::siunit \<Rightarrow> bool" (infix "=\<^sub>U" 50) where
"a =\<^sub>U b \<longleftrightarrow> SI('a) = SI('b)"

lemma unit_equiv_refl [simp]: "a =\<^sub>U a"
  by (simp add: unit_equiv_def)

lemma unit_equiv_sym [simp]: "a =\<^sub>U b \<Longrightarrow> b =\<^sub>U a"
  by (simp add: unit_equiv_def)

subsubsection \<open> Arithmetic \<close>

text \<open> We define multiplication at the SI type level \<close>

typedef ('a::siunit, 'b::siunit) UnitTimes (infixl "\<cdot>" 69) = "UNIV :: unit set" ..
setup_lifting type_definition_UnitTimes

text \<open> We can prove that multiplication of two SI types yields an SI type. \<close>

instantiation UnitTimes :: (siunit, siunit) siunit
begin
  definition siunit_of_UnitTimes :: "('a \<cdot> 'b) itself \<Rightarrow> SIUnit" where
  "siunit_of_UnitTimes x = SI('a) * SI('b)"
  instance by (intro_classes, simp_all add: siunit_of_UnitTimes_def, (transfer, simp)+)
end

text \<open> Similarly, we define division of two SI types and prove that SI types are closed under this. \<close>

typedef 'a UnitInv ("(_\<^sup>-\<^sup>1)" [999] 999) = "UNIV :: unit set" ..
setup_lifting type_definition_UnitInv
instantiation UnitInv :: (siunit) siunit
begin
  definition siunit_of_UnitInv :: "('a\<^sup>-\<^sup>1) itself \<Rightarrow> SIUnit" where
  "siunit_of_UnitInv x = inverse SI('a)"
  instance by (intro_classes, simp_all add: siunit_of_UnitInv_def, (transfer, simp)+)
end

type_synonym ('a, 'b) UnitDiv = "'a \<cdot> ('b\<^sup>-\<^sup>1)" (infixl "'/" 69)

type_synonym 'a UnitSquare = "'a \<cdot> 'a" ("(_)\<^sup>2" [999] 999)
type_synonym 'a UnitCube = "'a \<cdot> 'a \<cdot> 'a" ("(_)\<^sup>3" [999] 999)
type_synonym 'a UnitInvSquare = "('a\<^sup>2)\<^sup>-\<^sup>1" ("(_)\<^sup>-\<^sup>2" [999] 999)
type_synonym 'a UnitInvCube = "('a\<^sup>3)\<^sup>-\<^sup>1" ("(_)\<^sup>-\<^sup>3" [999] 999)

translations (type) "'a\<^sup>-\<^sup>2" <= (type) "('a\<^sup>2)\<^sup>-\<^sup>1"
translations (type) "'a\<^sup>-\<^sup>3" <= (type) "('a\<^sup>3)\<^sup>-\<^sup>1"

print_translation \<open>
  [(@{type_syntax UnitTimes}, 
    fn ctx => fn [a, b] => 
      if (a = b) 
          then Const (@{type_syntax UnitSquare}, dummyT) $ a
          else case a of
            Const (@{type_syntax UnitTimes}, _) $ a1 $ a2 =>
              if (a1 = a2 andalso a2 = b) 
                then Const (@{type_syntax UnitCube}, dummyT) $ a1 
                else raise Match |
            Const (@{type_syntax UnitSquare}, _) $ a' =>
              if (@{print} a' = b) 
                then Const (@{type_syntax UnitCube}, dummyT) $ a'
                else raise Match |
            _ => raise Match)]
\<close>

subsubsection \<open> SI base type constructors \<close>

typedef meter = "UNIV :: unit set" .. setup_lifting type_definition_meter
instantiation meter :: sibaseunit
begin
  definition siunit_of_meter :: "meter itself \<Rightarrow> SIUnit" where "siunit_of_meter x = mk_BaseUnit Meter"
instance by (intro_classes, simp_all add: siunit_of_meter_def, (transfer, simp)+)
end

typedef kilogram = "UNIV :: unit set" .. setup_lifting type_definition_kilogram
instantiation kilogram :: sibaseunit
begin
  definition siunit_of_kilogram :: "kilogram itself \<Rightarrow> SIUnit" where "siunit_of_kilogram x = mk_BaseUnit Kilogram"
instance by (intro_classes, simp_all add: siunit_of_kilogram_def, (transfer, simp)+)
end

typedef second = "UNIV :: unit set" .. setup_lifting type_definition_second
instantiation second :: sibaseunit
begin
  definition siunit_of_second :: "second itself \<Rightarrow> SIUnit" where "siunit_of_second x = mk_BaseUnit Second"
instance by (intro_classes, simp_all add: siunit_of_second_def, (transfer, simp)+)
end

typedef ampere = "UNIV :: unit set" .. setup_lifting type_definition_ampere
instantiation ampere :: sibaseunit
begin
  definition siunit_of_ampere :: "ampere itself \<Rightarrow> SIUnit" where "siunit_of_ampere x = mk_BaseUnit Second"
instance by (intro_classes, simp_all add: siunit_of_ampere_def, (transfer, simp)+)
end

typedef kelvin = "UNIV :: unit set" .. setup_lifting type_definition_kelvin
instantiation kelvin :: sibaseunit
begin
  definition siunit_of_kelvin :: "kelvin itself \<Rightarrow> SIUnit" where "siunit_of_kelvin x = mk_BaseUnit Second"
instance by (intro_classes, simp_all add: siunit_of_kelvin_def, (transfer, simp)+)
end

typedef mole = "UNIV :: unit set" .. setup_lifting type_definition_mole
instantiation mole :: sibaseunit
begin
  definition siunit_of_mole :: "mole itself \<Rightarrow> SIUnit" where "siunit_of_mole x = mk_BaseUnit Second"
instance by (intro_classes, simp_all add: siunit_of_mole_def, (transfer, simp)+)
end

typedef candela = "UNIV :: unit set" .. setup_lifting type_definition_candela
instantiation candela :: sibaseunit
begin
  definition siunit_of_candela :: "candela itself \<Rightarrow> SIUnit" where "siunit_of_candela x = mk_BaseUnit Second"
instance by (intro_classes, simp_all add: siunit_of_candela_def, (transfer, simp)+)
end

subsection \<open> SI tagged types \<close>

typedef (overloaded) ('n, 'u::siunit) Unit ("_[_]" [999,0] 999) = "{x :: 'n SI. unit x = SI('u)}"
  morphisms fromUnit toUnit by (rule_tac x="\<lparr> factor = undefined, unit = SI('u) \<rparr>" in exI, simp)

text \<open> Coerce values when their units are equivalent \<close>

definition coerceUnit :: "'a['u\<^sub>1::siunit] \<Rightarrow> 'u\<^sub>2 itself \<Rightarrow> 'a['u\<^sub>2::siunit]" where
"coerceUnit x t = (if SI('u\<^sub>1) = SI('u\<^sub>2) then toUnit (fromUnit x) else undefined)"

setup_lifting type_definition_Unit

lift_definition 
  Unit_times :: "('n::times)['a::siunit] \<Rightarrow> 'n['b::siunit] \<Rightarrow> 'n['a\<cdot>'b]" (infixl "*\<^sub>U" 69) is "(*)"
  by (simp add: siunit_of_UnitTimes_def times_SI_ext_def)
  
lift_definition 
  Unit_inverse :: "('n::inverse)['a::siunit] \<Rightarrow> 'n['a\<^sup>-\<^sup>1]" ("(_\<^sup>-\<^sup>\<one>)" [999] 999) is "inverse"
  by (simp add: inverse_SI_ext_def siunit_of_UnitInv_def)

abbreviation 
  Unit_divide :: "('n::{times,inverse})['a::siunit] \<Rightarrow> 'n['b::siunit] \<Rightarrow> 'n['a/'b]" (infixl "'/\<^sub>U" 70) where
"Unit_divide x y \<equiv> x *\<^sub>U y\<^sup>-\<^sup>\<one>"

abbreviation Unit_sq ("(_)\<^sup>\<two>" [999] 999) where "u\<^sup>\<two> \<equiv> u *\<^sub>U u"
abbreviation Unit_cube ("(_)\<^sup>\<three>" [999] 999) where "u\<^sup>\<three> \<equiv> u *\<^sub>U u *\<^sub>U u"

abbreviation Unit_neq_sq ("(_)\<^sup>-\<^sup>\<two>" [999] 999) where "u\<^sup>-\<^sup>\<two> \<equiv> (u\<^sup>\<two>)\<^sup>-\<^sup>\<one>"
abbreviation Unit_neq_cube ("(_)\<^sup>-\<^sup>\<three>" [999] 999) where "u\<^sup>-\<^sup>\<three> \<equiv> (u\<^sup>\<three>)\<^sup>-\<^sup>\<one>"

instantiation Unit :: (zero,siunit) zero
begin
lift_definition zero_Unit :: "('a, 'b) Unit" is "\<lparr> factor = 0, unit = SI('b) \<rparr>" 
  by simp
instance ..
end

instantiation Unit :: (one,siunit) one
begin
lift_definition one_Unit :: "('a, 'b) Unit" is "\<lparr> factor = 1, unit = SI('b) \<rparr>"
  by simp
instance ..
end

instantiation Unit :: (plus,siunit) plus
begin
lift_definition plus_Unit :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> 'a['b]"
  is "\<lambda> x y. \<lparr> factor = factor x + factor y, unit = SI('b) \<rparr>"
  by (simp)
instance ..
end

instance Unit :: (semigroup_add,siunit) semigroup_add
  by (intro_classes, transfer, simp add: add.assoc)

instance Unit :: (ab_semigroup_add,siunit) ab_semigroup_add
  by (intro_classes, transfer, simp add: add.commute)

instance Unit :: (monoid_add,siunit) monoid_add
  by (intro_classes; (transfer, simp))
  
instance Unit :: (comm_monoid_add,siunit) comm_monoid_add
  by (intro_classes; transfer, simp)

instantiation Unit :: (uminus,siunit) uminus
begin
lift_definition uminus_Unit :: "'a['b] \<Rightarrow> 'a['b]" 
  is "\<lambda> x. \<lparr> factor = - factor x, unit = unit x \<rparr>" by (simp)
instance ..
end

instantiation Unit :: (minus,siunit) minus
begin
lift_definition minus_Unit :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> 'a['b]"
  is "\<lambda> x y. \<lparr> factor = factor x - factor y, unit = unit x \<rparr>" by (simp)

instance ..
end

instance Unit :: (numeral,siunit) numeral ..

instantiation Unit :: (times,siunit) times
begin
lift_definition times_Unit :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> 'a['b]" 
  is "\<lambda> x y. \<lparr> factor = factor x * factor y, unit = SI('b) \<rparr>"
  by simp
instance ..
end

instance Unit :: (power,siunit) power ..

instance Unit :: (semigroup_mult,siunit) semigroup_mult
  by (intro_classes, transfer, simp add: mult.assoc)

instance Unit :: (ab_semigroup_mult,siunit) ab_semigroup_mult
  by (intro_classes, (transfer, simp add: mult.commute))

instance Unit :: (comm_semiring,siunit) comm_semiring
  by (intro_classes, transfer, simp add: linordered_field_class.sign_simps(18) mult.commute)

instance Unit :: (comm_semiring_0,siunit) comm_semiring_0
  by (intro_classes, (transfer, simp)+)

instance Unit :: (comm_monoid_mult,siunit) comm_monoid_mult
  by (intro_classes, (transfer, simp add: mult.commute)+)

instance Unit :: (comm_semiring_1,siunit) comm_semiring_1
  by (intro_classes; (transfer, simp add: semiring_normalization_rules(1-8,24)))

instantiation Unit :: (divide,siunit) divide
begin
lift_definition divide_Unit :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> 'a['b]" 
  is "\<lambda> x y. \<lparr> factor = factor x div factor y, unit = SI('b) \<rparr>" by simp
instance ..
end

instantiation Unit :: (inverse,siunit) inverse
begin
lift_definition inverse_Unit :: "'a['b] \<Rightarrow> 'a['b]" 
  is "\<lambda> x. \<lparr> factor = inverse (factor x), unit = SI('b) \<rparr>" by simp
instance ..
end

instantiation Unit :: (order,siunit) order
begin
  lift_definition less_eq_Unit :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> bool" is "\<lambda> x y. factor x \<le> factor y" .
  lift_definition less_Unit :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> bool" is "\<lambda> x y. factor x < factor y" .
  instance by (intro_classes, (transfer, simp add: less_le_not_le)+)
end

lift_definition mk_unit :: "'a \<Rightarrow> 'u itself \<Rightarrow> ('a::one)['u::siunit]" 
  is "\<lambda> n u. \<lparr> factor = n, unit = SI('u) \<rparr>" by simp

syntax "_mk_unit" :: "logic \<Rightarrow> type \<Rightarrow> logic" ("UNIT'(_, _')")
translations "UNIT(n, 'a)" == "CONST mk_unit n TYPE('a)"

named_theorems si_def

definition [si_def]: "meter = UNIT(1, meter)"
definition [si_def]: "second = UNIT(1, second)"
definition [si_def]: "kilogram = UNIT(1, kilogram)"
definition [si_def]: "ampere = UNIT(1, ampere)"
definition [si_def]: "kelvin = UNIT(1, kelvin)"
definition [si_def]: "mole = UNIT(1, mole)"
definition [si_def]: "candela = UNIT(1, candela)"

definition factorUnit :: "'a['u::siunit] \<Rightarrow> 'a" ("\<lbrakk>_\<rbrakk>\<^sub>U") where
"factorUnit x = factor (fromUnit x)"

lemma unit_eq_iff_factor_eq:
  "x = y \<longleftrightarrow> \<lbrakk>x\<rbrakk>\<^sub>U = \<lbrakk>y\<rbrakk>\<^sub>U"
  by (auto simp add: factorUnit_def, transfer, simp)

lemma unit_le_iff_factor_le:
  "x \<le> y \<longleftrightarrow> \<lbrakk>x\<rbrakk>\<^sub>U \<le> \<lbrakk>y\<rbrakk>\<^sub>U"
  by (auto simp add: factorUnit_def; (transfer, simp))

lemma factorUnit_zero [si_def]: "\<lbrakk>0\<rbrakk>\<^sub>U = 0"
  by (simp add: factorUnit_def, transfer, simp)

lemma factorUnit_one [si_def]: "\<lbrakk>1\<rbrakk>\<^sub>U = 1"
  by (simp add: factorUnit_def, transfer, simp)

lemma factorUnit_plus [si_def]: "\<lbrakk>x + y\<rbrakk>\<^sub>U = \<lbrakk>x\<rbrakk>\<^sub>U + \<lbrakk>y\<rbrakk>\<^sub>U"
  by (simp add: factorUnit_def, transfer, simp)

lemma factorUnit_times [si_def]: "\<lbrakk>x * y\<rbrakk>\<^sub>U = \<lbrakk>x\<rbrakk>\<^sub>U * \<lbrakk>y\<rbrakk>\<^sub>U"
  by (simp add: factorUnit_def, transfer, simp)

lemma factorUnit_numeral [si_def]: "\<lbrakk>numeral n\<rbrakk>\<^sub>U = numeral n"
  apply (induct n, simp_all add: si_def)
  apply (metis factorUnit_plus numeral_code(2))
  apply (metis factorUnit_one factorUnit_plus numeral_code(3))
  done

lemma factorUnit_mk [si_def]: "\<lbrakk>UNIT(n, 'u::siunit)\<rbrakk>\<^sub>U = n"
  by (simp add: factorUnit_def, transfer, simp)

method si_calc = 
  (simp add: unit_eq_iff_factor_eq unit_le_iff_factor_le si_def 
             zero_Unit.rep_eq less_eq_Unit_def less_Unit_def)

subsubsection \<open> Derived Units \<close>

definition "radian = 1 \<cdot> (meter *\<^sub>U meter\<^sup>-\<^sup>\<one>)"

definition degree :: "real[meter / meter]" where
[si_def]: "degree = (2\<cdot>(UNIT(pi,_)) / 180)\<cdot>radian"

abbreviation degrees ("_\<degree>" [999] 999) where "n\<degree> \<equiv> n\<cdot>degree" 

definition [si_def]: "litre = 1/1000 \<cdot> meter\<^sup>\<two>"

definition [si_def]: "pint = 0.56826125 \<cdot> litre"

definition [si_def]: "milli = UNIT(0.001, _)"

definition [si_def]: "centi = UNIT(0.01, _)"

definition [si_def]: "kilo = UNIT(1000, _)"

abbreviation "tonne \<equiv> kilo\<cdot>kilogram"

abbreviation "newton \<equiv> (kilogram *\<^sub>U meter) /\<^sub>U second\<^sup>\<two>"

abbreviation "volt \<equiv> kilogram *\<^sub>U meter\<^sup>\<two> *\<^sub>U second\<^sup>-\<^sup>\<three> *\<^sub>U ampere\<^sup>-\<^sup>\<one>"

end