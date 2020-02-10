section \<open> SI Units \<close>

theory SI_Units
  imports Groups_mult 
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
\<^enum> We construct a generic type \<^theory_text>\<open>Unit\<close> which is basically an "inner representation" or
  "semantic domain" of all SI types. Since SI-types have an interpretation in this domain, 
  it serves to give semantics to type-constructors by operations on this domain, too.
  We construct a multiplicative group on it.
\<^enum> From \<^theory_text>\<open>Unit\<close> we build a  \<^theory_text>\<open>'a SI_tagged_domain\<close> types, i.e. a polymorphic family of values
  tagged with values from \<^theory_text>\<open>Unit\<close>. We construct multiplicative and additive 
  groups over it.
\<^enum> We construct a type-class characterizing SI - type expressions
  and types tagged with SI - type expressions; this construction paves the
  way to overloaded interpretation functions from SI type-expressions to   

\<close>

section\<open>The Domains of SI types and SI-tagged types\<close>

subsection \<open> The \<^theory_text>\<open>Unit\<close>-type and its operations \<close>

text \<open> An SI unit associates with each of the seven base unit an integer that denotes the power 
  to which it is raised. We use a record to represent this 7-tuple, to enable code generation. \<close>

record Unit = 
  Seconds   :: int 
  Meters    :: int 
  Kilograms :: int 
  Amperes   :: int 
  Kelvins   :: int 
  Moles     :: int
  Candelas  :: int

text \<open> We define a commutative monoid for SI units. \<close>

instantiation Unit_ext :: (one) one
begin
  \<comment> \<open> Here, $1$ is the dimensionless unit \<close>
definition one_Unit_ext :: "'a Unit_ext" 
  where  [code_unfold]:  "1 = \<lparr> Seconds = 0, Meters = 0, Kilograms = 0, Amperes = 0
                               , Kelvins = 0, Moles = 0, Candelas = 0, \<dots> = 1 \<rparr>"
  instance ..
end

instantiation Unit_ext :: (times) times
begin
  \<comment> \<open> Multiplication is defined by adding together the powers \<close>
definition times_Unit_ext :: "'a Unit_ext \<Rightarrow> 'a Unit_ext \<Rightarrow> 'a Unit_ext" 
  where [code_unfold]:
  "x * y = \<lparr> Seconds = Seconds x + Seconds y, Meters = Meters x + Meters y
           , Kilograms = Kilograms x + Kilograms y, Amperes = Amperes x + Amperes y
           , Kelvins = Kelvins x + Kelvins y, Moles = Moles x + Moles y
           , Candelas = Candelas x + Candelas y, \<dots> = more x * more y \<rparr>"
  instance ..
end

instance Unit_ext :: (comm_monoid_mult) comm_monoid_mult
proof
  fix a b c :: "'a Unit_ext"
  show "a * b * c = a * (b * c)"
    by (simp add: times_Unit_ext_def mult.assoc)
  show "a * b = b * a"
    by (simp add: times_Unit_ext_def mult.commute)
  show "1 * a = a"
    by (simp add: times_Unit_ext_def one_Unit_ext_def)
qed

text \<open> We also define the inverse and division operations, and an abelian group. \<close>

instantiation Unit_ext :: ("{times,inverse}") inverse
begin
definition inverse_Unit_ext :: "'a Unit_ext \<Rightarrow> 'a Unit_ext" 
  where [code_unfold]:
  "inverse x = \<lparr> Seconds = - Seconds x , Meters = - Meters x
               , Kilograms = - Kilograms x, Amperes = - Amperes x
               , Kelvins = - Kelvins x, Moles = - Moles x
               , Candelas = - Candelas x, \<dots> = inverse (more x) \<rparr>"

definition divide_Unit_ext :: "'a Unit_ext \<Rightarrow> 'a Unit_ext \<Rightarrow> 'a Unit_ext" 
  where [code_unfold]: 
  "divide_Unit_ext x y = x * (inverse y)"
  instance ..
end
 
instance Unit_ext :: (ab_group_mult) ab_group_mult
proof
  fix a b :: "'a Unit_ext"
  show "inverse a \<cdot> a  = 1"
    by (simp add: inverse_Unit_ext_def times_Unit_ext_def one_Unit_ext_def)
  show "a \<cdot> inverse b = a div b"
    by (simp add: divide_Unit_ext_def)
qed

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

text \<open> A base unit is an SI_tagged_domain unit here precisely one unit has power 1. \<close>

definition is_BaseUnit :: "Unit \<Rightarrow> bool" where
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
@{typ Unit}. \<close>

subsubsection \<open> SI-type expression definition as type-class \<close>

class si_type = finite +
  fixes   si_sem :: "'a itself \<Rightarrow> Unit"
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
  definition si_sem_meter :: "meter itself \<Rightarrow> Unit" where "si_sem_meter x = 1\<lparr>Meters := 1\<rparr>"
instance by (intro_classes, auto simp add: si_sem_meter_def is_BaseUnit_def, (transfer, simp)+)
end

instantiation kilogram :: si_baseunit
begin
  definition si_sem_kilogram :: "kilogram itself \<Rightarrow> Unit" where "si_sem_kilogram x = 1\<lparr>Kilograms := 1\<rparr>"
instance by (intro_classes, auto simp add: si_sem_kilogram_def is_BaseUnit_def, (transfer, simp)+)
end

instantiation second :: si_baseunit
begin
  definition si_sem_second :: "second itself \<Rightarrow> Unit" where "si_sem_second x = 1\<lparr>Seconds := 1\<rparr>"
instance by (intro_classes, auto simp add: si_sem_second_def is_BaseUnit_def, (transfer, simp)+)
end

instantiation ampere :: si_baseunit
begin
  definition si_sem_ampere :: "ampere itself \<Rightarrow> Unit" where "si_sem_ampere x = 1\<lparr>Amperes := 1\<rparr>"
instance by (intro_classes, auto simp add: si_sem_ampere_def is_BaseUnit_def, (transfer, simp)+)
end

instantiation kelvin :: si_baseunit
begin
  definition si_sem_kelvin :: "kelvin itself \<Rightarrow> Unit" where "si_sem_kelvin x = 1\<lparr>Kelvins := 1\<rparr>"
instance by (intro_classes, auto simp add: si_sem_kelvin_def is_BaseUnit_def, (transfer, simp)+)
end

instantiation mole :: si_baseunit
begin
  definition si_sem_mole :: "mole itself \<Rightarrow> Unit" where "si_sem_mole x = 1\<lparr>Moles := 1\<rparr>"
instance by (intro_classes, auto simp add: si_sem_mole_def is_BaseUnit_def, (transfer, simp)+)
end   

instantiation candela :: si_baseunit
begin
  definition si_sem_candela :: "candela itself \<Rightarrow> Unit" where "si_sem_candela x = 1\<lparr>Candelas := 1\<rparr>"
instance by (intro_classes, auto simp add: si_sem_candela_def is_BaseUnit_def, (transfer, simp)+)
end

lemma base_units [simp]: 
  "is_BaseUnit SI(meter)" "is_BaseUnit SI(kilogram)" "is_BaseUnit SI(second)"
  "is_BaseUnit SI(ampere)" "is_BaseUnit SI(kelvin)" "is_BaseUnit SI(mole)"
  "is_BaseUnit SI(candela)" by (simp_all add: is_BaseUnit)

subsubsection \<open> Higher SI Type Constructors: Inner Product and Inverse \<close>
text\<open>On the class of SI-types (in which we have already inserted the base SI types), 
the definitions of the type constructors for inner product and inverse is straight) forward.\<close>

typedef ('a::si_type, 'b::si_type) UnitTimes (infixl "\<cdot>" 69) = "UNIV :: unit set" ..
setup_lifting type_definition_UnitTimes

text \<open> We can prove that multiplication of two SI types yields an SI type. \<close>

instantiation UnitTimes :: (si_type, si_type) si_type
begin
  definition si_sem_UnitTimes :: "('a \<cdot> 'b) itself \<Rightarrow> Unit" where
  "si_sem_UnitTimes x = SI('a) * SI('b)"
  instance by (intro_classes, simp_all add: si_sem_UnitTimes_def, (transfer, simp)+)
end

text \<open> Similarly, we define division of two SI types and prove that SI types are closed under this. \<close>

typedef 'a UnitInv ("(_\<^sup>-\<^sup>1)" [999] 999) = "UNIV :: unit set" ..
setup_lifting type_definition_UnitInv
instantiation UnitInv :: (si_type) si_type
begin
  definition si_sem_UnitInv :: "('a\<^sup>-\<^sup>1) itself \<Rightarrow> Unit" where
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

end