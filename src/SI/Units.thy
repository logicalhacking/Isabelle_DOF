section \<open> SI Units \<close>

theory Units
  imports Groups_mult 
          (* HOL.Fields *)
          HOL.Transcendental 
          "HOL-Eisbach.Eisbach"
begin

text\<open>
The International System of Units (SI, abbreviated from the French 
Système international (d'unités)) is the modern form of the metric 
system and is the most widely used system of measurement. It comprises
a coherent system of units of measurement built on seven base units, 
which are the second, metre, kilogram, ampere, kelvin, mole, candela, 
and a set of twenty prefixes to the unit names and unit symbols that
may be used when specifying multiples and fractions of the units. 
The system also specifies names for 22 derived units, such as lumen and 
watt, for other common physical quantities.

(cited from \<^url>\<open>https://en.wikipedia.org/wiki/International_System_of_Units\<close>).\<close>

text\<open> This is an attempt to model the system and its derived entities (cf.
\<^url>\<open>https://www.quora.com/What-are-examples-of-SI-units\<close>) in Isabelle/HOL.
The design objective are twofold (and for the case of Isabelle somewhat
contradictory, see below)

The construction proceeds in three phases:
\<^enum> We construct a generic type \<^theory_text>\<open>SI_domain\<close> which is basically an "inner representation" or
  "semantic domain" of all SI types. Since SI-types have an interpretation in this domain, 
  it serves to give semantics to type-constructors by operations on this domain, too.
  We construct a multiplicative group on it.
\<^enum> From \<^theory_text>\<open>SI_domain\<close> we build a  \<^theory_text>\<open>'a SI_tagged_domain\<close> types, i.e. a polymorphic family of values
  tagged with values from \<^theory_text>\<open>SI_domain\<close>. We construct multiplicative and additive 
  groups over it.
\<^enum> We construct a type-class characterizing SI - type expressions
  and types tagged with SI - type expressions; this construction paves the
  way to overloaded interpretation functions from SI type-expressions to   

\<close>

section\<open>The Domains of SI types and SI-tagged types\<close>

subsection \<open> The \<^theory_text>\<open>SI_domain\<close>-type and its operations \<close>

text \<open> An SI unit associates with each of the seven base unit an integer that denotes the power 
  to which it is raised. We use a record to represent this 7-tuple, to enable code generation. \<close>

record SI_domain = 
  Seconds   :: int 
  Meters    :: int 
  Kilograms :: int 
  Amperes   :: int 
  Kelvins   :: int 
  Moles     :: int
  Candelas  :: int

text \<open> We define a commutative monoid for SI units. \<close>

instantiation SI_domain_ext :: (one) one
begin
  \<comment> \<open> Here, $1$ is the dimensionless unit \<close>
definition one_SI_domain_ext :: "'a SI_domain_ext" 
  where  [code_unfold]:  "1 = \<lparr> Seconds = 0, Meters = 0, Kilograms = 0, Amperes = 0
                               , Kelvins = 0, Moles = 0, Candelas = 0, \<dots> = 1 \<rparr>"
  instance ..
end

instantiation SI_domain_ext :: (times) times
begin
  \<comment> \<open> Multiplication is defined by adding together the powers \<close>
definition times_SI_domain_ext :: "'a SI_domain_ext \<Rightarrow> 'a SI_domain_ext \<Rightarrow> 'a SI_domain_ext" 
  where [code_unfold]:
  "x * y = \<lparr> Seconds = Seconds x + Seconds y, Meters = Meters x + Meters y
           , Kilograms = Kilograms x + Kilograms y, Amperes = Amperes x + Amperes y
           , Kelvins = Kelvins x + Kelvins y, Moles = Moles x + Moles y
           , Candelas = Candelas x + Candelas y, \<dots> = more x * more y \<rparr>"
  instance ..
end

instance SI_domain_ext :: (comm_monoid_mult) comm_monoid_mult
proof
  fix a b c :: "'a SI_domain_ext"
  show "a * b * c = a * (b * c)"
    by (simp add: times_SI_domain_ext_def mult.assoc)
  show "a * b = b * a"
    by (simp add: times_SI_domain_ext_def mult.commute)
  show "1 * a = a"
    by (simp add: times_SI_domain_ext_def one_SI_domain_ext_def)
qed

text \<open> We also define the inverse and division operations, and an abelian group. \<close>

instantiation SI_domain_ext :: ("{times,inverse}") inverse
begin
definition inverse_SI_domain_ext :: "'a SI_domain_ext \<Rightarrow> 'a SI_domain_ext" 
  where [code_unfold]:
  "inverse x = \<lparr> Seconds = - Seconds x , Meters = - Meters x
               , Kilograms = - Kilograms x, Amperes = - Amperes x
               , Kelvins = - Kelvins x, Moles = - Moles x
               , Candelas = - Candelas x, \<dots> = inverse (more x) \<rparr>"

definition divide_SI_domain_ext :: "'a SI_domain_ext \<Rightarrow> 'a SI_domain_ext \<Rightarrow> 'a SI_domain_ext" 
  where [code_unfold]: 
  "divide_SI_domain_ext x y = x * (inverse y)"
  instance ..
end

print_classes 

instance SI_domain_ext :: (ab_group_mult) ab_group_mult
proof
  fix a b :: "'a SI_domain_ext"
  show "inverse a \<cdot> a  = 1"
    by (simp add: inverse_SI_domain_ext_def times_SI_domain_ext_def one_SI_domain_ext_def)
  show "a \<cdot> inverse b = a div b"
    by (simp add: divide_SI_domain_ext_def)
qed



instance SI_domain_ext :: (field) field
proof
  fix a b :: "'a SI_domain_ext"
  show "inverse a \<cdot> a  = 1"
    sledgehammer
    by (simp add: inverse_SI_domain_ext_def times_SI_domain_ext_def one_SI_domain_ext_def)
  show "a \<cdot> inverse b = a div b"
    by (simp add: divide_SI_domain_ext_def)
qed




subsection \<open> The \<^theory_text>\<open>SI_tagged_domain\<close>-type and its operations \<close>

record 'a SI_tagged_domain =
  factor :: 'a
  unit   :: SI_domain

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

instantiation SI_tagged_domain_ext :: (times, times) times
begin
  definition "times_SI_tagged_domain_ext x y = \<lparr> factor = factor x \<cdot> factor y, unit = unit x \<cdot> unit y, \<dots> = more x \<cdot> more y \<rparr>"
instance ..
end

instantiation SI_tagged_domain_ext :: (zero, zero) zero
begin
  definition "zero_SI_tagged_domain_ext = \<lparr> factor = 0, unit = 1, \<dots> = 0 \<rparr>"
instance ..
end

instantiation SI_tagged_domain_ext :: (one, one) one
begin
  definition "one_SI_tagged_domain_ext = \<lparr> factor = 1, unit = 1, \<dots> = 1 \<rparr>"
instance ..
end

instantiation SI_tagged_domain_ext :: (inverse, inverse) inverse
begin
  definition "inverse_SI_tagged_domain_ext x = \<lparr> factor = inverse (factor x), unit = inverse (unit x), \<dots> = inverse (more x) \<rparr>"
  definition "divide_SI_tagged_domain_ext x y = \<lparr> factor = factor x / factor y, unit = unit x / unit y, \<dots> = more x / more y \<rparr>"
instance ..
end

instance SI_tagged_domain_ext :: (comm_monoid_mult, comm_monoid_mult) comm_monoid_mult
  by (intro_classes, simp_all add: one_SI_tagged_domain_ext_def 
                                   times_SI_tagged_domain_ext_def mult.assoc, simp add: mult.commute)

text \<open> A base unit is an SI_tagged_domain unit here precisely one unit has power 1. \<close>

definition is_BaseUnit :: "SI_domain \<Rightarrow> bool" where
"is_BaseUnit u = (\<exists> n. u = 1\<lparr>Meters := n\<rparr> \<or> u = 1\<lparr>Kilograms := n\<rparr> \<or> u = 1\<lparr>Seconds := n\<rparr>
                     \<or> u = 1\<lparr>Amperes := n\<rparr> \<or> u = 1\<lparr>Kelvins := n\<rparr> \<or> u = 1\<lparr>Moles := n\<rparr>
                     \<or> u = 1\<lparr>Candelas := n\<rparr>)"


section\<open>The Syntax and Semantics of SI types and SI-tagged types\<close>

subsection \<open> Basic SI-types \<close>

text \<open> We provide a syntax for type-expressions; The definition of
the basic type constructors is straight-forward via a one-elementary set. \<close>

typedef meter    = "UNIV :: unit set" .. setup_lifting type_definition_meter
typedef kilogram = "UNIV :: unit set" .. setup_lifting type_definition_kilogram
typedef second   = "UNIV :: unit set" .. setup_lifting type_definition_second
typedef ampere   = "UNIV :: unit set" .. setup_lifting type_definition_ampere
typedef kelvin   = "UNIV :: unit set" .. setup_lifting type_definition_kelvin
typedef mole     = "UNIV :: unit set" .. setup_lifting type_definition_mole
typedef candela  = "UNIV :: unit set" .. setup_lifting type_definition_candela


subsection \<open> SI-type expressions and SI-type interpretation \<close>

text \<open> The case for the construction of the multiplicative and inverse operators requires ---
thus, the unary and binary operators on our SI type language --- require that their arguments
are restricted to the set of SI-type expressions.

The mechanism in Isabelle to characterize a certain sub-class of Isabelle-type expressions 
are \<^emph>\<open>type classes\<close>. We therefore need such a sub-class; for reasons of convenience,
we combine its construction also with the "semantics" of SI types in terms of  
@{typ SI_domain}. \<close>

subsubsection \<open> SI-type expression definition as type-class \<close>

class si_type = finite +
  fixes   si_sem :: "'a itself \<Rightarrow> SI_domain"
  assumes unitary_unit_pres: "card (UNIV::'a set) = 1"

syntax
  "_SI" :: "type \<Rightarrow> logic" ("SI'(_')")

translations
  "SI('a)" == "CONST si_sem TYPE('a)"

text \<open> The sub-set of basic SI type expressions can be characterized by the following
operation: \<close>

class si_baseunit = si_type +
  assumes is_BaseUnit: "is_BaseUnit SI('a)"

subsubsection \<open> SI base type constructors \<close>

text\<open>We embed the basic SI types into the SI type expressions: \<close>
declare [[show_sorts]]

instantiation meter :: si_baseunit
begin
  definition si_sem_meter :: "meter itself \<Rightarrow> SI_domain" where "si_sem_meter x = 1\<lparr>Meters := 1\<rparr>"
instance by (intro_classes, auto simp add: si_sem_meter_def is_BaseUnit_def, (transfer, simp)+)
end

instantiation kilogram :: si_baseunit
begin
  definition si_sem_kilogram :: "kilogram itself \<Rightarrow> SI_domain" where "si_sem_kilogram x = 1\<lparr>Kilograms := 1\<rparr>"
instance by (intro_classes, auto simp add: si_sem_kilogram_def is_BaseUnit_def, (transfer, simp)+)
end

instantiation second :: si_baseunit
begin
  definition si_sem_second :: "second itself \<Rightarrow> SI_domain" where "si_sem_second x = 1\<lparr>Seconds := 1\<rparr>"
instance by (intro_classes, auto simp add: si_sem_second_def is_BaseUnit_def, (transfer, simp)+)
end

instantiation ampere :: si_baseunit
begin
  definition si_sem_ampere :: "ampere itself \<Rightarrow> SI_domain" where "si_sem_ampere x = 1\<lparr>Amperes := 1\<rparr>"
instance by (intro_classes, auto simp add: si_sem_ampere_def is_BaseUnit_def, (transfer, simp)+)
end

instantiation kelvin :: si_baseunit
begin
  definition si_sem_kelvin :: "kelvin itself \<Rightarrow> SI_domain" where "si_sem_kelvin x = 1\<lparr>Kelvins := 1\<rparr>"
instance by (intro_classes, auto simp add: si_sem_kelvin_def is_BaseUnit_def, (transfer, simp)+)
end

instantiation mole :: si_baseunit
begin
  definition si_sem_mole :: "mole itself \<Rightarrow> SI_domain" where "si_sem_mole x = 1\<lparr>Moles := 1\<rparr>"
instance by (intro_classes, auto simp add: si_sem_mole_def is_BaseUnit_def, (transfer, simp)+)
end   

instantiation candela :: si_baseunit
begin
  definition si_sem_candela :: "candela itself \<Rightarrow> SI_domain" where "si_sem_candela x = 1\<lparr>Candelas := 1\<rparr>"
instance by (intro_classes, auto simp add: si_sem_candela_def is_BaseUnit_def, (transfer, simp)+)
end

lemma [simp] : "is_BaseUnit SI(meter)"    by(simp add: Units.si_baseunit_class.is_BaseUnit)
lemma [simp] : "is_BaseUnit SI(kilogram)" by(simp add: Units.si_baseunit_class.is_BaseUnit)
lemma [simp] : "is_BaseUnit SI(second)"   by(simp add: Units.si_baseunit_class.is_BaseUnit)
lemma [simp] : "is_BaseUnit SI(ampere)"   by(simp add: Units.si_baseunit_class.is_BaseUnit)
lemma [simp] : "is_BaseUnit SI(kelvin)"   by(simp add: Units.si_baseunit_class.is_BaseUnit)
lemma [simp] : "is_BaseUnit SI(mole)"     by(simp add: Units.si_baseunit_class.is_BaseUnit)
lemma [simp] : "is_BaseUnit SI(candela)"  by(simp add: Units.si_baseunit_class.is_BaseUnit)


subsubsection \<open> Higher SI Type Constructors: Inner Product and Inverse \<close>
text\<open>On the class of SI-types (in which we have already inserted the base SI types), 
the definitions of the type constructors for inner product and inverse is straight) forward.\<close>

typedef ('a::si_type, 'b::si_type) UnitTimes (infixl "\<cdot>" 69) = "UNIV :: unit set" ..
setup_lifting type_definition_UnitTimes

text \<open> We can prove that multiplication of two SI types yields an SI type. \<close>

instantiation UnitTimes :: (si_type, si_type) si_type
begin
  definition si_sem_UnitTimes :: "('a \<cdot> 'b) itself \<Rightarrow> SI_domain" where
  "si_sem_UnitTimes x = SI('a) * SI('b)"
  instance by (intro_classes, simp_all add: si_sem_UnitTimes_def, (transfer, simp)+)
end

text \<open> Similarly, we define division of two SI types and prove that SI types are closed under this. \<close>

typedef 'a UnitInv ("(_\<^sup>-\<^sup>1)" [999] 999) = "UNIV :: unit set" ..
setup_lifting type_definition_UnitInv
instantiation UnitInv :: (si_type) si_type
begin
  definition si_sem_UnitInv :: "('a\<^sup>-\<^sup>1) itself \<Rightarrow> SI_domain" where
  "si_sem_UnitInv x = inverse SI('a)"
  instance by (intro_classes, simp_all add: si_sem_UnitInv_def, (transfer, simp)+)
end


subsubsection \<open> Syntactic Support for SI type expressions. \<close>

text\<open>A number of type-synonyms allow for more compact notation: \<close>
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



subsection \<open> SI Tagged Types \<close>
text\<open>We 'lift' SI type expressions to SI tagged type expressions as follows:\<close>

typedef (overloaded) ('n, 'u::si_type) Unit ("_[_]" [999,0] 999) 
                     = "{x :: 'n SI_tagged_domain. unit x = SI('u)}"
  morphisms fromUnit toUnit by (rule_tac x="\<lparr> factor = undefined, unit = SI('u) \<rparr>" in exI, simp)

text \<open> Coerce values when their units are equivalent \<close>

definition coerceUnit :: "'u\<^sub>2 itself \<Rightarrow> 'a['u\<^sub>1::si_type] \<Rightarrow> 'a['u\<^sub>2::si_type]" where
"SI('u\<^sub>1) = SI('u\<^sub>2) \<Longrightarrow> coerceUnit t x = (toUnit (fromUnit x))"


section\<open>Operations SI-tagged types via their Semantic Domains\<close>

subsection\<open>Predicates on SI-tagged types\<close>

text \<open> Two SI types are equivalent if they have the same value-level units. \<close>

definition Unit_equiv :: "'n['a::si_type] \<Rightarrow> 'n['b::si_type] \<Rightarrow> bool" (infix "\<approx>\<^sub>U" 50) where
"a \<approx>\<^sub>U b \<longleftrightarrow> fromUnit a = fromUnit b"

text\<open>This gives us an equivalence, but, unfortunately, not a congruence.\<close>

lemma Unit_equiv_refl [simp]: "a \<approx>\<^sub>U a"
  by (simp add: Unit_equiv_def)

lemma Unit_equiv_sym: "a \<approx>\<^sub>U b \<Longrightarrow> b \<approx>\<^sub>U a"
  by (simp add: Unit_equiv_def)

lemma Unit_equiv_trans: "\<lbrakk> a \<approx>\<^sub>U b; b \<approx>\<^sub>U c \<rbrakk> \<Longrightarrow> a \<approx>\<^sub>U c"
  by (simp add: Unit_equiv_def)

(* the following series of equivalent statements ... *)

lemma coerceUnit_eq_iff:
  fixes x :: "'a['u\<^sub>1::si_type]"
  assumes "SI('u\<^sub>1) = SI('u\<^sub>2::si_type)"
  shows "(coerceUnit TYPE('u\<^sub>2) x) \<approx>\<^sub>U x"
  by (metis Unit_equiv_def assms coerceUnit_def fromUnit toUnit_inverse)

(* or equivalently *)

lemma coerceUnit_eq_iff2:
  fixes x :: "'a['u\<^sub>1::si_type]"
  assumes "SI('u\<^sub>1) = SI('u\<^sub>2::si_type)" and "y = (coerceUnit TYPE('u\<^sub>2) x)"
  shows "x \<approx>\<^sub>U y"
  by (metis Unit_equiv_def assms coerceUnit_def fromUnit toUnit_inverse)

lemma updown_eq_iff:
  fixes x :: "'a['u\<^sub>1::si_type]" fixes y :: "'a['u\<^sub>2::si_type]"
  assumes "SI('u\<^sub>1) = SI('u\<^sub>2::si_type)" and "y = (toUnit (fromUnit x))"
  shows "x \<approx>\<^sub>U y"
  by (metis Unit_equiv_def assms fromUnit toUnit_inverse)

text\<open>This is more general that \<open>y = x \<Longrightarrow> x \<approx>\<^sub>U y\<close>, since x and y may have different type.\<close>

find_theorems "(toUnit (fromUnit _))"


lemma eq_ : 
  fixes x :: "'a['u\<^sub>1::si_type]" fixes y :: "'a['u\<^sub>2::si_type]"
  assumes  "x \<approx>\<^sub>U y"
  shows "SI('u\<^sub>1) = SI('u\<^sub>2::si_type)"
  by (metis (full_types) Unit_equiv_def assms fromUnit mem_Collect_eq)


subsection\<open>Operations on SI-tagged types\<close>

setup_lifting type_definition_Unit

lift_definition 
  Unit_times :: "('n::times)['a::si_type] \<Rightarrow> 'n['b::si_type] \<Rightarrow> 'n['a \<cdot>'b]" (infixl "*\<^sub>U" 69) is "(*)"
  by (simp add: si_sem_UnitTimes_def times_SI_tagged_domain_ext_def)
  
lift_definition 
  Unit_inverse :: "('n::inverse)['a::si_type] \<Rightarrow> 'n['a\<^sup>-\<^sup>1]" ("(_\<^sup>-\<^sup>\<one>)" [999] 999) is "inverse"
  by (simp add: inverse_SI_tagged_domain_ext_def si_sem_UnitInv_def)

abbreviation 
  Unit_divide :: "('n::{times,inverse})['a::si_type] \<Rightarrow> 'n['b::si_type] \<Rightarrow> 'n['a/'b]" (infixl "'/\<^sub>U" 70) where
"Unit_divide x y \<equiv> x *\<^sub>U y\<^sup>-\<^sup>\<one>"

abbreviation Unit_sq ("(_)\<^sup>\<two>" [999] 999) where "u\<^sup>\<two> \<equiv> u *\<^sub>U u"
abbreviation Unit_cube ("(_)\<^sup>\<three>" [999] 999) where "u\<^sup>\<three> \<equiv> u *\<^sub>U u *\<^sub>U u"

abbreviation Unit_neq_sq ("(_)\<^sup>-\<^sup>\<two>" [999] 999) where "u\<^sup>-\<^sup>\<two> \<equiv> (u\<^sup>\<two>)\<^sup>-\<^sup>\<one>"
abbreviation Unit_neq_cube ("(_)\<^sup>-\<^sup>\<three>" [999] 999) where "u\<^sup>-\<^sup>\<three> \<equiv> (u\<^sup>\<three>)\<^sup>-\<^sup>\<one>"

instantiation Unit :: (zero,si_type) zero
begin
lift_definition zero_Unit :: "('a, 'b) Unit" is "\<lparr> factor = 0, unit = SI('b) \<rparr>" 
  by simp
instance ..
end

instantiation Unit :: (one,si_type) one
begin
lift_definition one_Unit :: "('a, 'b) Unit" is "\<lparr> factor = 1, unit = SI('b) \<rparr>"
  by simp
instance ..
end

instantiation Unit :: (plus,si_type) plus
begin
lift_definition plus_Unit :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> 'a['b]"
  is "\<lambda> x y. \<lparr> factor = factor x + factor y, unit = SI('b) \<rparr>"
  by (simp)
instance ..
end

instance Unit :: (semigroup_add,si_type) semigroup_add
  by (intro_classes, transfer, simp add: add.assoc)

instance Unit :: (ab_semigroup_add,si_type) ab_semigroup_add
  by (intro_classes, transfer, simp add: add.commute)

instance Unit :: (monoid_add,si_type) monoid_add
  by (intro_classes; (transfer, simp))
  
instance Unit :: (comm_monoid_add,si_type) comm_monoid_add
  by (intro_classes; transfer, simp)

instantiation Unit :: (uminus,si_type) uminus
begin
lift_definition uminus_Unit :: "'a['b] \<Rightarrow> 'a['b]" 
  is "\<lambda> x. \<lparr> factor = - factor x, unit = unit x \<rparr>" by (simp)
instance ..
end

instantiation Unit :: (minus,si_type) minus
begin
lift_definition minus_Unit :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> 'a['b]"
  is "\<lambda> x y. \<lparr> factor = factor x - factor y, unit = unit x \<rparr>" by (simp)

instance ..
end

instance Unit :: (numeral,si_type) numeral ..

instantiation Unit :: (times,si_type) times
begin
lift_definition times_Unit :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> 'a['b]" 
  is "\<lambda> x y. \<lparr> factor = factor x * factor y, unit = SI('b) \<rparr>"
  by simp
instance ..
end

instance Unit :: (power,si_type) power ..

instance Unit :: (semigroup_mult,si_type) semigroup_mult
  by (intro_classes, transfer, simp add: mult.assoc)

instance Unit :: (ab_semigroup_mult,si_type) ab_semigroup_mult
  by (intro_classes, (transfer, simp add: mult.commute))

instance Unit :: (comm_semiring,si_type) comm_semiring
  by (intro_classes, transfer, simp add: linordered_field_class.sign_simps(18) mult.commute)

instance Unit :: (comm_semiring_0,si_type) comm_semiring_0
  by (intro_classes, (transfer, simp)+)

instance Unit :: (comm_monoid_mult,si_type) comm_monoid_mult
  by (intro_classes, (transfer, simp add: mult.commute)+)

instance Unit :: (comm_semiring_1,si_type) comm_semiring_1
  by (intro_classes; (transfer, simp add: semiring_normalization_rules(1-8,24)))

instantiation Unit :: (divide,si_type) divide
begin
lift_definition divide_Unit :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> 'a['b]" 
  is "\<lambda> x y. \<lparr> factor = factor x div factor y, unit = SI('b) \<rparr>" by simp
instance ..
end

instantiation Unit :: (inverse,si_type) inverse
begin
lift_definition inverse_Unit :: "'a['b] \<Rightarrow> 'a['b]" 
  is "\<lambda> x. \<lparr> factor = inverse (factor x), unit = SI('b) \<rparr>" by simp
instance ..
end

instantiation Unit :: (order,si_type) order
begin
  lift_definition less_eq_Unit :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> bool" is "\<lambda> x y. factor x \<le> factor y" .
  lift_definition less_Unit :: "'a['b] \<Rightarrow> 'a['b] \<Rightarrow> bool" is "\<lambda> x y. factor x < factor y" .
  instance by (intro_classes, (transfer, simp add: less_le_not_le)+)
end

lift_definition mk_unit :: "'a \<Rightarrow> 'u itself \<Rightarrow> ('a::one)['u::si_type]" 
  is "\<lambda> n u. \<lparr> factor = n, unit = SI('u) \<rparr>" by simp

syntax "_mk_unit" :: "logic \<Rightarrow> type \<Rightarrow> logic" ("UNIT'(_, _')")
translations "UNIT(n, 'a)" == "CONST mk_unit n TYPE('a)"

subsection \<open>Polymorphic Operations for Elementary SI Units \<close>

named_theorems si_def

definition [si_def]: "meter    = UNIT(1, meter)"
definition [si_def]: "second   = UNIT(1, second)"
definition [si_def]: "kilogram = UNIT(1, kilogram)"
definition [si_def]: "ampere   = UNIT(1, ampere)"
definition [si_def]: "kelvin   = UNIT(1, kelvin)"
definition [si_def]: "mole     = UNIT(1, mole)"
definition [si_def]: "candela  = UNIT(1, candela)"

subsubsection \<open>The Projection: Stripping the SI-Tags \<close>

definition factorUnit :: "'a['u::si_type] \<Rightarrow> 'a" ("\<lbrakk>_\<rbrakk>\<^sub>U") where
"factorUnit x = factor (fromUnit x)"


subsubsection \<open>More Operations \<close>

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

lemma factorUnit_div [si_def]: "\<lbrakk>x / y\<rbrakk>\<^sub>U = \<lbrakk>x\<rbrakk>\<^sub>U / \<lbrakk>y\<rbrakk>\<^sub>U"
  by (simp add: factorUnit_def, transfer, simp)

lemma factorUnit_numeral [si_def]: "\<lbrakk>numeral n\<rbrakk>\<^sub>U = numeral n"
  apply (induct n, simp_all add: si_def)
  apply (metis factorUnit_plus numeral_code(2))
  apply (metis factorUnit_one factorUnit_plus numeral_code(3))
  done

lemma factorUnit_mk [si_def]: "\<lbrakk>UNIT(n, 'u::si_type)\<rbrakk>\<^sub>U = n"
  by (simp add: factorUnit_def, transfer, simp)

method si_calc = 
  (simp add: unit_eq_iff_factor_eq unit_le_iff_factor_le si_def)

section \<open> Some Derived Units \<close>

definition "radian = 1 \<cdot> (meter *\<^sub>U meter\<^sup>-\<^sup>\<one>)"                                  

definition degree :: "real[meter / meter]" where
[si_def]: "degree = (2\<cdot>(UNIT(pi,_)) / 180)\<cdot>radian"

abbreviation degrees ("_\<degree>" [999] 999) where "n\<degree> \<equiv> n\<cdot>degree" 

definition [si_def]: "litre = 1/1000 \<cdot> meter\<^sup>\<three>"

definition [si_def]: "pint = 0.56826125 \<cdot> litre"

definition [si_def]: "milli = UNIT(0.001, _)"

definition [si_def]: "kilo = UNIT(1000, _)"

definition [si_def]: "hour = 3600 \<cdot> second"

abbreviation "tonne \<equiv> kilo\<cdot>kilogram"

abbreviation "newton \<equiv> (kilogram *\<^sub>U meter) /\<^sub>U second\<^sup>\<two>"

abbreviation "volt \<equiv> kilogram *\<^sub>U meter\<^sup>\<two> *\<^sub>U second\<^sup>-\<^sup>\<three> *\<^sub>U ampere\<^sup>-\<^sup>\<one>"

abbreviation "watt \<equiv> kilogram *\<^sub>U meter\<^sup>\<two> *\<^sub>U second\<^sup>-\<^sup>\<three>"

abbreviation "joule \<equiv> kilogram *\<^sub>U meter\<^sup>\<two> *\<^sub>U  second\<^sup>-\<^sup>\<two>"

text\<open>The full beauty of the approach is perhaps revealed here, with the 
     type of a classical three-dimensional gravitation field:\<close>
type_synonym gravitation_field = "(real\<^sup>3 \<Rightarrow> real\<^sup>3)[meter \<cdot> (second)\<^sup>-\<^sup>2]"

section \<open> Tactic Support for SI type expressions. \<close>

lemmas [si_def] =  Units.si_sem_meter_def Units.si_sem_kilogram_def Units.si_sem_second_def 
                   Units.si_sem_ampere_def Units.si_sem_kelvin_def Units.si_sem_mole_def
                   Units.si_sem_candela_def 

                   si_sem_UnitTimes_def si_sem_UnitInv_def
                   times_SI_domain_ext_def one_SI_domain_ext_def
                   
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
                  \<lparr>factor = x,
                   unit = \<lparr>Seconds = 1, Meters = 0, Kilograms = 0, Amperes = 0, 
                           Kelvins = 0, Moles = 0, Candelas = 0\<rparr>\<rparr>"
  by (simp add: mk_unit.rep_eq one_SI_domain_ext_def si_sem_second_def)

lemma [si_def]:"fromUnit UNIT(x::'a::one, meter) = 
                  \<lparr>factor = x,
                   unit = \<lparr>Seconds = 0, Meters = 1, Kilograms = 0, Amperes = 0, 
                           Kelvins = 0, Moles = 0, Candelas = 0\<rparr>\<rparr>"
  by (simp add: mk_unit.rep_eq one_SI_domain_ext_def si_sem_meter_def)

lemma [si_def]:"fromUnit UNIT(x::'a::one, kilogram) = 
                  \<lparr>factor = x,
                   unit = \<lparr>Seconds = 0, Meters = 0, Kilograms = 1, Amperes = 0, 
                           Kelvins = 0, Moles = 0, Candelas = 0\<rparr>\<rparr>"
  by (simp add: mk_unit.rep_eq one_SI_domain_ext_def si_sem_kilogram_def)

lemma [si_def]:"fromUnit UNIT(x::'a::one, ampere) = 
                  \<lparr>factor = x,
                   unit = \<lparr>Seconds = 0, Meters = 0, Kilograms = 0, Amperes = 1, 
                           Kelvins = 0, Moles = 0, Candelas = 0\<rparr>\<rparr>"
  by (simp add: mk_unit.rep_eq one_SI_domain_ext_def si_sem_ampere_def)

lemma [si_def]:"fromUnit UNIT(x::'a::one, kelvin) = 
                  \<lparr>factor = x,
                   unit = \<lparr>Seconds = 0, Meters = 0, Kilograms = 0, Amperes = 0, 
                           Kelvins = 1, Moles = 0, Candelas = 0\<rparr>\<rparr>"
  by (simp add: mk_unit.rep_eq one_SI_domain_ext_def si_sem_kelvin_def)

lemma [si_def]:"fromUnit UNIT(x::'a::one, mole) = 
                  \<lparr>factor = x,
                   unit = \<lparr>Seconds = 0, Meters = 0, Kilograms = 0, Amperes = 0, 
                           Kelvins = 0, Moles = 1, Candelas = 0\<rparr>\<rparr>"
  by (simp add: mk_unit.rep_eq one_SI_domain_ext_def si_sem_mole_def)

lemma [si_def]:"fromUnit UNIT(x::'a::one, candela) = 
                  \<lparr>factor = x,
                   unit = \<lparr>Seconds = 0, Meters = 0, Kilograms = 0, Amperes = 0, 
                           Kelvins = 0, Moles = 0, Candelas = 1\<rparr>\<rparr>"
  by (simp add: mk_unit.rep_eq one_SI_domain_ext_def si_sem_candela_def)




lemma Unit_times_commute:
  fixes X::"'a::{one,ab_semigroup_mult}['b::si_type]"and Y::"'a['c::si_type]"
  shows "X *\<^sub>U Y  \<approx>\<^sub>U  Y *\<^sub>U X"
  unfolding Unit_equiv_def
  by (simp add: Unit_times.rep_eq linordered_field_class.sign_simps(5) times_SI_tagged_domain_ext_def)

text\<open>Observe that this commutation law also commutes the types.\<close>
 
(* just a check that instantiation works for special cases ... *)
lemma "    (UNIT(x, candela) *\<^sub>U UNIT(y::'a::{one,ab_semigroup_mult}, mole))
        \<approx>\<^sub>U (UNIT(y, mole) *\<^sub>U UNIT(x, candela)) "
  by(simp add: Unit_times_commute)


lemma Unit_times_assoc:
  fixes X::"'a::{one,ab_semigroup_mult}['b::si_type]"
    and Y::"'a['c::si_type]"
    and Z::"'a['d::si_type]"
  shows  "(X *\<^sub>U Y) *\<^sub>U Z  \<approx>\<^sub>U  X *\<^sub>U (Y *\<^sub>U Z)"
  unfolding Unit_equiv_def
  by (simp add: Unit_times.rep_eq mult.assoc times_SI_tagged_domain_ext_def)

text\<open>The following weak congruences will allow for replacing equivalences in contexts
     built from product and inverse. \<close>
lemma Unit_times_weak_cong_left:
  fixes X::"'a::{one,ab_semigroup_mult}['b::si_type]"
    and Y::"'a['c::si_type]"
    and Z::"'a['d::si_type]"
  assumes "X \<approx>\<^sub>U Y"
  shows  "(X *\<^sub>U Z)  \<approx>\<^sub>U  (Y *\<^sub>U Z)"
  by (metis Unit_equiv_def Unit_times.rep_eq assms)

lemma Unit_times_weak_cong_right:
  fixes X::"'a::{one,ab_semigroup_mult}['b::si_type]"
    and Y::"'a['c::si_type]"
    and Z::"'a['d::si_type]"
  assumes "X \<approx>\<^sub>U Y"
  shows  "(Z *\<^sub>U X)  \<approx>\<^sub>U  (Z *\<^sub>U Y)"
  by (metis Unit_equiv_def Unit_times.rep_eq assms)

lemma Unit_inverse_weak_cong:
  fixes   X::"'a::{field}['b::si_type]"
    and   Y::"'a['c::si_type]"
  assumes "X  \<approx>\<^sub>U Y"
  shows   "(X)\<^sup>-\<^sup>\<one>  \<approx>\<^sub>U  (Y)\<^sup>-\<^sup>\<one>"
  unfolding Unit_equiv_def
  by (metis Unit_equiv_def Unit_inverse.rep_eq assms)


text\<open>In order to compute a normal form, we would additionally need these three:\<close>
(* field ? *)
lemma Unit_inverse_distrib:
  fixes X::"'a::{field}['b::si_type]"
    and Y::"'a['c::si_type]"
  shows "(X *\<^sub>U Y)\<^sup>-\<^sup>\<one>  \<approx>\<^sub>U  X\<^sup>-\<^sup>\<one> *\<^sub>U Y\<^sup>-\<^sup>\<one>"
  sorry

(* field ? *)
lemma Unit_inverse_inverse:
  fixes X::"'a::{field}['b::si_type]"
  shows "((X)\<^sup>-\<^sup>\<one>)\<^sup>-\<^sup>\<one>  \<approx>\<^sub>U  X"
  unfolding Unit_equiv_def
  sorry

(* field ? *)
lemma Unit_mult_cancel:
  fixes  X::"'a::{field}['b::si_type]"
  shows  "X /\<^sub>U X  \<approx>\<^sub>U  1"
  unfolding Unit_equiv_def
  sorry


lemma Unit_mult_mult_Left_cancel:
  fixes  X::"'a::{field}['b::si_type]"
  shows  "(1::'a['b/'b]) *\<^sub>U X  \<approx>\<^sub>U  X"
  unfolding Unit_equiv_def
  apply transfer
  unfolding Unit_equiv_def
  sorry


lemma "watt *\<^sub>U hour \<approx>\<^sub>U 3600 *\<^sub>U joule"
  unfolding Unit_equiv_def hour_def
  apply(simp add: Units.Unit_times.rep_eq si_def 
                 zero_SI_tagged_domain_ext_def times_SI_tagged_domain_ext_def 
                 inverse_SI_tagged_domain_ext_def 
                 Unit_inverse_def Unit_times_def)
  find_theorems fromUnit
  oops

  thm Units.Unit.toUnit_inverse


lemma "watt *\<^sub>U hour \<approx>\<^sub>U 3.6 *\<^sub>U kilo *\<^sub>U joule"
  oops

end
