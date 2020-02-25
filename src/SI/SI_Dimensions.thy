section \<open> SI Dimensions \<close>

theory SI_Dimensions
  imports Groups_mult 
          HOL.Transcendental 
          "HOL-Eisbach.Eisbach"
begin

named_theorems si_def and si_eq

section\<open>The Semantic Domain of Dimensions\<close>

subsection \<open> The Dimension-type and its operations \<close>

text \<open> An SI unit associates with each of the seven base unit an integer that denotes the power 
  to which it is raised. We use a record to represent this 7-tuple, to enable code generation. \<close>

record Dimension = 
  Length      :: int
  Mass        :: int
  Time        :: int
  Current     :: int 
  Temperature :: int 
  Amount      :: int
  Intensity   :: int

text \<open> We define a commutative monoid for SI units. \<close>

instantiation Dimension_ext :: (one) one
begin
  \<comment> \<open> Here, $1$ is the dimensionless unit \<close>
definition one_Dimension_ext :: "'a Dimension_ext" 
  where  [code_unfold, si_def]:  "1 = \<lparr> Length = 0, Mass = 0, Time = 0, Current = 0
                               , Temperature = 0, Amount = 0, Intensity = 0, \<dots> = 1 \<rparr>"
  instance ..
end

instantiation Dimension_ext :: (times) times
begin
  \<comment> \<open> Multiplication is defined by adding together the powers \<close>
definition times_Dimension_ext :: "'a Dimension_ext \<Rightarrow> 'a Dimension_ext \<Rightarrow> 'a Dimension_ext" 
  where [code_unfold, si_def]:
  "x * y = \<lparr> Length = Length x + Length y, Mass = Mass x + Mass y
           , Time = Time x + Time y, Current = Current x + Current y
           , Temperature = Temperature x + Temperature y, Amount = Amount x + Amount y
           , Intensity = Intensity x + Intensity y, \<dots> = more x * more y \<rparr>"
  instance ..
end

instance Dimension_ext :: (comm_monoid_mult) comm_monoid_mult
proof
  fix a b c :: "'a Dimension_ext"
  show "a * b * c = a * (b * c)"
    by (simp add: times_Dimension_ext_def mult.assoc)
  show "a * b = b * a"
    by (simp add: times_Dimension_ext_def mult.commute)
  show "1 * a = a"
    by (simp add: times_Dimension_ext_def one_Dimension_ext_def)
qed

text \<open> We also define the inverse and division operations, and an abelian group. \<close>

instantiation Dimension_ext :: ("{times,inverse}") inverse
begin
definition inverse_Dimension_ext :: "'a Dimension_ext \<Rightarrow> 'a Dimension_ext" 
  where [code_unfold, si_def]:
  "inverse x = \<lparr> Length = - Length x, Mass = - Mass x
               , Time = - Time x, Current = - Current x
               , Temperature = - Temperature x, Amount = - Amount x
               , Intensity = - Intensity x, \<dots> = inverse (more x) \<rparr>"

definition divide_Dimension_ext :: "'a Dimension_ext \<Rightarrow> 'a Dimension_ext \<Rightarrow> 'a Dimension_ext" 
  where [code_unfold, si_def]: 
  "divide_Dimension_ext x y = x * (inverse y)"
  instance ..
end
 
instance Dimension_ext :: (ab_group_mult) ab_group_mult
proof
  fix a b :: "'a Dimension_ext"
  show "inverse a \<cdot> a  = 1"
    by (simp add: inverse_Dimension_ext_def times_Dimension_ext_def one_Dimension_ext_def)
  show "a \<cdot> inverse b = a div b"
    by (simp add: divide_Dimension_ext_def)
qed

text \<open> It makes no sense to define a plus operator for SI units because we can only add together
  identical units, and this makes for a useless function. \<close>

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

instance unit :: ab_group_mult
  by (intro_classes, simp_all)

text \<open> A base unit is an unit where precisely one component has power 1. \<close>

definition is_BaseDim :: "Dimension \<Rightarrow> bool" where
"is_BaseDim u = (\<exists> n. u = 1\<lparr>Length := n\<rparr> \<or> u = 1\<lparr>Mass := n\<rparr> \<or> u = 1\<lparr>Time := n\<rparr>
                     \<or> u = 1\<lparr>Current := n\<rparr> \<or> u = 1\<lparr>Temperature := n\<rparr> \<or> u = 1\<lparr>Amount := n\<rparr>
                     \<or> u = 1\<lparr>Intensity := n\<rparr>)"

section\<open>The Syntax and Semantics of Dimension Types\<close>

subsection \<open> Basic Dimensions as Types (Basic SI-types)\<close>

text \<open> We provide a syntax for type-expressions; The definition of
the basic type constructors is straight-forward via a one-elementary set. 
The latter is adequate since we need just an abstract syntax for type-expressions,
so just one value for the \<^verbatim>\<open>dimension\<close>-type symbols. 
\<close>

typedef Length      = "UNIV :: unit set" .. setup_lifting type_definition_Length
typedef Mass        = "UNIV :: unit set" .. setup_lifting type_definition_Mass
typedef Time        = "UNIV :: unit set" .. setup_lifting type_definition_Time
typedef Current     = "UNIV :: unit set" .. setup_lifting type_definition_Current
typedef Temperature = "UNIV :: unit set" .. setup_lifting type_definition_Temperature
typedef Amount      = "UNIV :: unit set" .. setup_lifting type_definition_Amount
typedef Intensity   = "UNIV :: unit set" .. setup_lifting type_definition_Intensity
typedef NoDimension = "UNIV :: unit set" .. setup_lifting type_definition_NoDimension

type_synonym M = Mass
type_synonym L = Length
type_synonym T = Time
type_synonym I = Current
type_synonym \<Theta> = Temperature
type_synonym N = Amount
type_synonym J = Intensity
type_notation NoDimension ("\<one>")

translations
  (type) "M" <= (type) "Mass"
  (type) "L" <= (type) "Length"
  (type) "T" <= (type) "Time"
  (type) "I" <= (type) "Current"
  (type) "\<Theta>" <= (type) "Temperature"
  (type) "N" <= (type) "Amount"
  (type) "J" <= (type) "Intensity"

subsection \<open>Dimension Type Expressions and their Interpretation \<close>

text \<open> The case for the construction of the multiplicative and inverse operators requires ---
thus, the unary and binary operators on our SI type language --- require that their arguments
are restricted to the set of SI-type expressions.

The mechanism in Isabelle to characterize a certain sub-class of Isabelle-type expressions 
are \<^emph>\<open>type classes\<close>. We therefore need such a sub-class; for reasons of convenience,
we combine its construction also with the "semantics" of SI types in terms of  
@{typ Dimension}. \<close>

subsubsection \<open> SI-type expression definition as type-class \<close>

class dim_type = finite +
  fixes   dim_ty_sem :: "'a itself \<Rightarrow> Dimension"
  assumes unitary_unit_pres: "card (UNIV::'a set) = 1"


syntax
  "_SI" :: "type \<Rightarrow> logic" ("SI'(_')")

translations
  "SI('a)" == "CONST dim_ty_sem TYPE('a)"

text \<open> The sub-set of basic SI type expressions can be characterized by the following
operation: \<close>

class si_basedim = dim_type +
  assumes is_BaseDim: "is_BaseDim SI('a)"

subsubsection \<open> SI base type constructors \<close>

text\<open>We embed the basic SI types into the SI type expressions: \<close>

instantiation Length :: si_basedim
begin
definition dim_ty_sem_Length :: "Length itself \<Rightarrow> Dimension" 
  where [si_def]: "dim_ty_sem_Length x = 1\<lparr>Length := 1\<rparr>"
instance by (intro_classes, auto simp add: dim_ty_sem_Length_def is_BaseDim_def, (transfer, simp)+)
end

instantiation Mass :: si_basedim
begin
definition dim_ty_sem_Mass :: "Mass itself \<Rightarrow> Dimension" 
  where [si_def]: "dim_ty_sem_Mass x = 1\<lparr>Mass := 1\<rparr>"
instance by (intro_classes, auto simp add: dim_ty_sem_Mass_def is_BaseDim_def, (transfer, simp)+)
end

instantiation Time :: si_basedim
begin
definition dim_ty_sem_Time :: "Time itself \<Rightarrow> Dimension" 
  where [si_def]: "dim_ty_sem_Time x = 1\<lparr>Time := 1\<rparr>"
instance by (intro_classes, auto simp add: dim_ty_sem_Time_def is_BaseDim_def, (transfer, simp)+)
end

instantiation Current :: si_basedim
begin
definition dim_ty_sem_Current :: "Current itself \<Rightarrow> Dimension" 
  where [si_def]: "dim_ty_sem_Current x = 1\<lparr>Current := 1\<rparr>"
instance by (intro_classes, auto simp add: dim_ty_sem_Current_def is_BaseDim_def, (transfer, simp)+)
end

instantiation Temperature :: si_basedim
begin
definition dim_ty_sem_Temperature :: "Temperature itself \<Rightarrow> Dimension" 
  where [si_def]: "dim_ty_sem_Temperature x = 1\<lparr>Temperature := 1\<rparr>"
instance by (intro_classes, auto simp add: dim_ty_sem_Temperature_def is_BaseDim_def, (transfer, simp)+)
end

instantiation Amount :: si_basedim
begin
definition dim_ty_sem_Amount :: "Amount itself \<Rightarrow> Dimension" 
  where [si_def]: "dim_ty_sem_Amount x = 1\<lparr>Amount := 1\<rparr>"
instance by (intro_classes, auto simp add: dim_ty_sem_Amount_def is_BaseDim_def, (transfer, simp)+)
end   

instantiation Intensity :: si_basedim
begin
definition dim_ty_sem_Intensity :: "Intensity itself \<Rightarrow> Dimension" 
  where [si_def]: "dim_ty_sem_Intensity x = 1\<lparr>Intensity := 1\<rparr>"
instance by (intro_classes, auto simp add: dim_ty_sem_Intensity_def is_BaseDim_def, (transfer, simp)+)
end

instantiation NoDimension :: dim_type
begin
definition dim_ty_sem_NoDimension :: "NoDimension itself \<Rightarrow> Dimension" 
  where [si_def]: "dim_ty_sem_NoDimension x = 1"
instance by (intro_classes, auto simp add: dim_ty_sem_NoDimension_def is_BaseDim_def, (transfer, simp)+)
end

lemma base_units [simp]: 
  "is_BaseDim SI(Length)" "is_BaseDim SI(Mass)" "is_BaseDim SI(Time)"
  "is_BaseDim SI(Current)" "is_BaseDim SI(Temperature)" "is_BaseDim SI(Amount)"
  "is_BaseDim SI(Intensity)" by (simp_all add: is_BaseDim)

subsubsection \<open> Higher SI Type Constructors: Inner Product and Inverse \<close>
text\<open>On the class of SI-types (in which we have already inserted the base SI types), 
the definitions of the type constructors for inner product and inverse is straight forward.\<close>

typedef ('a::dim_type, 'b::dim_type) DimTimes (infixl "\<cdot>" 69) = "UNIV :: unit set" ..
setup_lifting type_definition_DimTimes

text \<open> We can prove that multiplication of two dimension types yields a dimension type. \<close>

instantiation DimTimes :: (dim_type, dim_type) dim_type
begin
  definition dim_ty_sem_DimTimes :: "('a \<cdot> 'b) itself \<Rightarrow> Dimension" where
  [si_eq]: "dim_ty_sem_DimTimes x = SI('a) * SI('b)"
  instance by (intro_classes, simp_all add: dim_ty_sem_DimTimes_def, (transfer, simp)+)
end

text \<open> Similarly, we define inversion of dimension types and prove that dimension types are 
  closed under this. \<close>

typedef 'a DimInv ("(_\<^sup>-\<^sup>1)" [999] 999) = "UNIV :: unit set" ..
setup_lifting type_definition_DimInv
instantiation DimInv :: (dim_type) dim_type
begin
  definition dim_ty_sem_DimInv :: "('a\<^sup>-\<^sup>1) itself \<Rightarrow> Dimension" where
  [si_eq]: "dim_ty_sem_DimInv x = inverse SI('a)"
  instance by (intro_classes, simp_all add: dim_ty_sem_DimInv_def, (transfer, simp)+)
end

subsection \<open> Syntactic Support for dim-type expressions. \<close>

text \<open> A division is expressed, as usual, by multiplication with an inverted dimension. \<close>

type_synonym ('a, 'b) DimDiv = "'a \<cdot> ('b\<^sup>-\<^sup>1)" (infixl "'/" 69)

text \<open> A number of further type-synonyms allow for more compact notation: \<close>

type_synonym 'a DimSquare = "'a \<cdot> 'a" ("(_)\<^sup>2" [999] 999)
type_synonym 'a DimCube = "'a \<cdot> 'a \<cdot> 'a" ("(_)\<^sup>3" [999] 999)
type_synonym 'a DimQuart = "'a \<cdot> 'a \<cdot> 'a \<cdot> 'a" ("(_)\<^sup>4" [999] 999)
type_synonym 'a DimInvSquare = "('a\<^sup>2)\<^sup>-\<^sup>1" ("(_)\<^sup>-\<^sup>2" [999] 999)
type_synonym 'a DimInvCube = "('a\<^sup>3)\<^sup>-\<^sup>1" ("(_)\<^sup>-\<^sup>3" [999] 999)
type_synonym 'a DimInvQuart = "('a\<^sup>4)\<^sup>-\<^sup>1" ("(_)\<^sup>-\<^sup>4" [999] 999)

translations (type) "'a\<^sup>-\<^sup>2" <= (type) "('a\<^sup>2)\<^sup>-\<^sup>1"
translations (type) "'a\<^sup>-\<^sup>3" <= (type) "('a\<^sup>3)\<^sup>-\<^sup>1"
translations (type) "'a\<^sup>-\<^sup>4" <= (type) "('a\<^sup>4)\<^sup>-\<^sup>1"

print_translation \<open>
  [(@{type_syntax DimTimes}, 
    fn ctx => fn [a, b] => 
      if (a = b) 
          then Const (@{type_syntax DimSquare}, dummyT) $ a
          else case a of
            Const (@{type_syntax DimTimes}, _) $ a1 $ a2 =>
              if (a1 = a2 andalso a2 = b) 
                then Const (@{type_syntax DimCube}, dummyT) $ a1 
                else case a1 of
                  Const (@{type_syntax DimTimes}, _) $ a11 $ a12 =>
                    if (a11 = a12 andalso a12 = a2 andalso a2 = b)
                      then Const (@{type_syntax DimQuart}, dummyT) $ a11
                      else raise Match |
            _ => raise Match)]
\<close>

subsection \<open> Derived Dimensions \<close>

type_synonym Area = "L\<^sup>2"
type_synonym Volume = "L\<^sup>3"
type_synonym Acceleration = "L\<cdot>T\<^sup>-\<^sup>1"
type_synonym Frequency = "T\<^sup>-\<^sup>1"
type_synonym Energy = "L\<^sup>2\<cdot>M\<cdot>T\<^sup>-\<^sup>2"
type_synonym Power = "L\<^sup>2\<cdot>M\<cdot>T\<^sup>-\<^sup>3"
type_synonym Force = "L\<cdot>M\<cdot>T\<^sup>-\<^sup>2"
type_synonym Pressure = "L\<^sup>-\<^sup>1\<cdot>M\<cdot>T\<^sup>-\<^sup>2"
type_synonym Charge = "I\<cdot>T"
type_synonym PotentialDifference = "L\<^sup>2\<cdot>M\<cdot>T\<^sup>-\<^sup>3\<cdot>I\<^sup>-\<^sup>1"
type_synonym Capacitance = "L\<^sup>-\<^sup>2\<cdot>M\<^sup>-\<^sup>1\<cdot>T\<^sup>4\<cdot>I\<^sup>2"

end