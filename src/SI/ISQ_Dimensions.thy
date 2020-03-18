chapter \<open> International System of Quantities \<close>

section \<open> Quantity Dimensions \<close>

theory ISQ_Dimensions
  imports Groups_mult 
          HOL.Transcendental 
          "HOL-Eisbach.Eisbach"
begin

subsection \<open> Preliminaries \<close>

named_theorems si_def and si_eq

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

subsection \<open> Dimensions Semantic Domain \<close>

text \<open> Quantity dimensions are used to distinguish quantities of different kinds. Only quantities
  of the same kind can be compared and combined: it is a mistake to add a length to a mass, for
  example. Dimensions are expressed in terms of seven base quantities, which can be combined to form 
  derived quantities. Consequently, a dimension associates with each of the seven base quantities an 
  integer that denotes the power to which it is raised. We use a record to represent this 7-tuple, 
  to enable code generation and thus efficient proof. \<close>

record Dimension = 
  Length      :: int
  Mass        :: int
  Time        :: int
  Current     :: int 
  Temperature :: int 
  Amount      :: int
  Intensity   :: int

text \<open> Next, we define dimension multiplication, and its unit, which corresponds to a dimensionless
  quantity. These are then shown to form a commutative monoid. \<close>

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

text \<open> We also define the inverse and division operations, and an abelian group, which will allow
  us to perform dimensional analysis. \<close>

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


text \<open> A base dimension is a dimension where precisely one component has power 1: it is the 
  dimension of a base quantity. Here we define the seven base dimensions. \<close>

definition LengthBD      ("\<^bold>L") where [si_def]: "\<^bold>L = (1::Dimension)\<lparr>Length := 1\<rparr>"
definition MassBD        ("\<^bold>M") where [si_def]: "\<^bold>M = (1::Dimension)\<lparr>Mass := 1\<rparr>"
definition TimeBD        ("\<^bold>T") where [si_def]: "\<^bold>T = (1::Dimension)\<lparr>Time := 1\<rparr>"
definition CurrentBD     ("\<^bold>I") where [si_def]: "\<^bold>I = (1::Dimension)\<lparr>Current := 1\<rparr>"
definition TemperatureBD ("\<^bold>\<Theta>") where [si_def]: "\<^bold>\<Theta> = (1::Dimension)\<lparr>Temperature := 1\<rparr>"
definition AmountBD      ("\<^bold>N") where [si_def]: "\<^bold>N = (1::Dimension)\<lparr>Amount := 1\<rparr>"
definition IntensityBD   ("\<^bold>J") where [si_def]: "\<^bold>J = (1::Dimension)\<lparr>Intensity := 1\<rparr>"

abbreviation "BaseDimensions \<equiv> {\<^bold>L, \<^bold>M, \<^bold>T, \<^bold>I, \<^bold>\<Theta>, \<^bold>N, \<^bold>J}"

text \<open> The following lemma confirms that there are indeed seven unique base dimensions. \<close>

lemma seven_BaseDimensions: "card BaseDimensions = 7"
  by (simp add: si_def)

definition is_BaseDim :: "Dimension \<Rightarrow> bool" where [si_def]: "is_BaseDim x \<equiv> x \<in> BaseDimensions"

text \<open> We can use the base dimensions and algebra to form dimension expressions. Some examples
  are shown below. \<close>

term "\<^bold>L\<cdot>\<^bold>M\<cdot>\<^bold>T\<^sup>-\<^sup>2"
term "\<^bold>M\<cdot>\<^bold>L\<^sup>-\<^sup>3"

subsection \<open> Dimensions Type Expressions \<close>

subsubsection \<open> Classification \<close>

text \<open> We provide a syntax for dimension type expressions, which allows representation of 
  dimensions as types in Isabelle. This will allow us to represent quantities that are parametrised 
  by a particular dimension type. We first must characterise the subclass of types that represent a 
  dimension.

  The mechanism in Isabelle to characterize a certain subclass of Isabelle type expressions
  are \<^emph>\<open>type classes\<close>. The following type class is used to link particular Isabelle types
  to an instance of the type \<^typ>\<open>Dimension\<close>. It requires that any such type has the cardinality
  \<^term>\<open>1\<close>, since a dimension type is used only to mark a quantity.
  \<close>

class dim_type = finite +
  fixes   dim_ty_sem :: "'a itself \<Rightarrow> Dimension"
  assumes unitary_unit_pres: "card (UNIV::'a set) = 1"

syntax
  "_QD" :: "type \<Rightarrow> logic" ("QD'(_')")

translations
  "QD('a)" == "CONST dim_ty_sem TYPE('a)"

text \<open> The notation \<^term>\<open>QD('a::dim_type)\<close> allows to obtain the dimension of a dimension type
  \<^typ>\<open>'a\<close>. 

  The subset of basic dimension types can be characterized by the following type class: \<close>

class basedim_type = dim_type +
  assumes is_BaseDim: "is_BaseDim QD('a)"

subsubsection \<open> Base Dimension Type Expressions \<close>

text \<open> The definition of the basic dimension type constructors is straightforward via a
  one-elementary set, \<^typ>\<open>unit set\<close>. The latter is adequate since we need just an abstract syntax 
  for type expressions, so just one value for the \<^verbatim>\<open>dimension\<close>-type symbols. We define types for
  each of the seven base dimensions, and also for dimensionless quantities. \<close>

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

text\<open> Next, we embed the base dimensions into the dimension type expressions by instantiating the 
  class \<^class>\<open>basedim_type\<close> with each of the base dimension types. \<close>

instantiation Length :: basedim_type
begin
definition [si_def]: "dim_ty_sem_Length (_::Length itself) = \<^bold>L"
instance by (intro_classes, auto simp add: dim_ty_sem_Length_def is_BaseDim_def, (transfer, simp)+)
end

instantiation Mass :: basedim_type
begin
definition [si_def]: "dim_ty_sem_Mass (_::Mass itself) = \<^bold>M"
instance by (intro_classes, auto simp add: dim_ty_sem_Mass_def is_BaseDim_def, (transfer, simp)+)
end

instantiation Time :: basedim_type
begin
definition [si_def]: "dim_ty_sem_Time (_::Time itself) = \<^bold>T"
instance by (intro_classes, auto simp add: dim_ty_sem_Time_def is_BaseDim_def, (transfer, simp)+)
end

instantiation Current :: basedim_type
begin
definition [si_def]: "dim_ty_sem_Current (_::Current itself) = \<^bold>I"
instance by (intro_classes, auto simp add: dim_ty_sem_Current_def is_BaseDim_def, (transfer, simp)+)
end

instantiation Temperature :: basedim_type
begin
definition [si_def]: "dim_ty_sem_Temperature (_::Temperature itself) = \<^bold>\<Theta>"
instance by (intro_classes, auto simp add: dim_ty_sem_Temperature_def is_BaseDim_def, (transfer, simp)+)
end

instantiation Amount :: basedim_type
begin
definition [si_def]: "dim_ty_sem_Amount (_::Amount itself) = \<^bold>N"
instance by (intro_classes, auto simp add: dim_ty_sem_Amount_def is_BaseDim_def, (transfer, simp)+)
end   

instantiation Intensity :: basedim_type
begin
definition [si_def]: "dim_ty_sem_Intensity (_::Intensity itself) = \<^bold>J"
instance by (intro_classes, auto simp add: dim_ty_sem_Intensity_def is_BaseDim_def, (transfer, simp)+)
end

instantiation NoDimension :: dim_type
begin
definition [si_def]: "dim_ty_sem_NoDimension (_::NoDimension itself) = (1::Dimension)"
instance by (intro_classes, auto simp add: dim_ty_sem_NoDimension_def is_BaseDim_def, (transfer, simp)+)
end

lemma base_dimension_types [simp]: 
  "is_BaseDim QD(Length)" "is_BaseDim QD(Mass)" "is_BaseDim QD(Time)" "is_BaseDim QD(Current)" 
  "is_BaseDim QD(Temperature)" "is_BaseDim QD(Amount)" "is_BaseDim QD(Intensity)" 
  by (simp_all add: is_BaseDim)

subsubsection \<open> Dimension Type Constructors: Inner Product and Inverse \<close>

text\<open> Dimension type expressions can be constructed by multiplication and division of the base
  dimension types above. Consequently, we need to define multiplication and inverse operators
  at the type level as well. On the class of dimension types (in which we have already inserted 
  the base dimension types), the definitions of the type constructors for inner product and inverse is 
  straightforward. \<close>

typedef ('a::dim_type, 'b::dim_type) DimTimes (infixl "\<cdot>" 69) = "UNIV :: unit set" ..
setup_lifting type_definition_DimTimes

text \<open> The type \<^typ>\<open>('a,'b) DimTimes\<close> is parameterised by two types, \<^typ>\<open>'a\<close> and \<^typ>\<open>'b\<close> that must
  both be elements of the \<^class>\<open>dim_type\<close> class. As with the base dimensions, it is a unitary type
  as its purpose is to represent dimension type expressions. We instantiate \<^class>\<open>dim_type\<close> with
  this type, where the semantics of a product dimension expression is the product of the underlying
  dimensions. This means that multiplication of two dimension types yields a dimension type. \<close>

instantiation DimTimes :: (dim_type, dim_type) dim_type
begin
  definition dim_ty_sem_DimTimes :: "('a \<cdot> 'b) itself \<Rightarrow> Dimension" where
  [si_eq]: "dim_ty_sem_DimTimes x = QD('a) * QD('b)"
  instance by (intro_classes, simp_all add: dim_ty_sem_DimTimes_def, (transfer, simp)+)
end

text \<open> Similarly, we define inversion of dimension types and prove that dimension types are 
  closed under this. \<close>

typedef 'a DimInv ("(_\<^sup>-\<^sup>1)" [999] 999) = "UNIV :: unit set" ..
setup_lifting type_definition_DimInv
instantiation DimInv :: (dim_type) dim_type
begin
  definition dim_ty_sem_DimInv :: "('a\<^sup>-\<^sup>1) itself \<Rightarrow> Dimension" where
  [si_eq]: "dim_ty_sem_DimInv x = inverse QD('a)"
  instance by (intro_classes, simp_all add: dim_ty_sem_DimInv_def, (transfer, simp)+)
end

subsubsection \<open> Dimension Type Syntax \<close>

text \<open> A division is expressed, as usual, by multiplication with an inverted dimension. \<close>

type_synonym ('a, 'b) DimDiv = "'a \<cdot> ('b\<^sup>-\<^sup>1)" (infixl "'/" 69)

text \<open> A number of further type synonyms allow for more compact notation: \<close>

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

subsubsection \<open> Derived Dimension Types \<close>

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