chapter \<open> International System of Units \<close>

section \<open> SI Units Semantics \<close>

theory SI_Units
  imports ISQ
begin

text \<open> An SI unit is simply a particular kind of quantity. \<close>

type_synonym ('n, 'd) UnitT = "('n, 'd) QuantT"

text \<open> Parallel to the seven base quantities, there are seven base units. In the implementation of
  the SI unit system, we fix these to be precisely those quantities that have a base dimension
  and a magnitude of \<^term>\<open>1\<close>. Consequently, a base unit corresponds to a unit in the algebraic
  sense. \<close>

lift_definition is_base_unit :: "'a::one['d::dim_type] \<Rightarrow> bool" 
  is "\<lambda> x. mag x = 1 \<and> is_BaseDim (dim x)" . 

definition mk_base_unit :: "'u itself \<Rightarrow> ('a::one)['u::basedim_type]" 
  where [si_eq]: "mk_base_unit t = 1"

syntax "_mk_base_unit" :: "type \<Rightarrow> logic" ("BUNIT'(_')")
translations "BUNIT('a)" == "CONST mk_base_unit TYPE('a)"

lemma mk_base_unit: "is_base_unit (mk_base_unit a)"
  by (simp add: si_eq, transfer, simp add: is_BaseDim)

lemma magQ_mk [si_eq]: "\<lbrakk>BUNIT('u::basedim_type)\<rbrakk>\<^sub>Q = 1"
  by (simp add: magQ_def si_eq, transfer, simp)

text \<open> We now define the seven base units. Effectively, these definitions axiomatise given names
  for the \<^term>\<open>1\<close> elements of the base quantities. \<close>

definition [si_eq]: "meter    = BUNIT(L)"
definition [si_eq]: "second   = BUNIT(T)"
definition [si_eq]: "kilogram = BUNIT(M)"
definition [si_eq]: "ampere   = BUNIT(I)"
definition [si_eq]: "kelvin   = BUNIT(\<Theta>)"
definition [si_eq]: "mole     = BUNIT(N)"
definition [si_eq]: "candela  = BUNIT(J)"

text\<open>Note that as a consequence of our construction, the term \<^term>\<open>meter\<close> is a SI Unit constant of 
SI-type \<^typ>\<open>'a[L]\<close>, so a unit of dimension \<^typ>\<open>Length\<close> with the magnitude of type \<^typ>\<open>'a\<close>.
A magnitude instantiation can be, e.g., an integer, a rational number, a real number, or a vector of 
type \<^typ>\<open>real\<^sup>3\<close>. Note than when considering vectors, dimensions refer to the \<^emph>\<open>norm\<close> of the vector,
not to its components. \<close>

lemma BaseUnits: 
  "is_base_unit meter" "is_base_unit second" "is_base_unit kilogram" "is_base_unit ampere"
  "is_base_unit kelvin" "is_base_unit mole" "is_base_unit candela"
  by (simp add: si_eq, transfer, simp)+

text \<open> The effect of the above encoding is that we can use the SI base units as synonyms for their
  corresponding dimensions at the type level. \<close>

type_synonym meter = Length
type_synonym second = Time
type_synonym kilogram = Mass
type_synonym ampere = Current
type_synonym kelvin = Temperature
type_synonym mole = Amount
type_synonym candela = Intensity

text \<open> We can therefore construct a quantity such as \<^term>\<open>5 :: rat[meter]\<close>, which unambiguously 
  identifies that the unit of $5$ is meters using the type system. This works because each base
  unit it the one element. \<close>

subsection \<open> Example Unit Equations \<close>

lemma "(meter \<^bold>\<cdot> second\<^sup>-\<^sup>\<one>) \<^bold>\<cdot> second \<cong>\<^sub>Q meter"
  by (si_calc)

end