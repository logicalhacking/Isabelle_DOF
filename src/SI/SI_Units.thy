section \<open> SI Units \<close>

theory SI_Units
  imports SI_Proof
begin

lift_definition mk_base_unit :: "'u itself \<Rightarrow> ('a::one)['u::dim_type]" 
  is "\<lambda> u. \<lparr> mag = 1, dim = QD('u) \<rparr>" by simp

syntax "_mk_base_unit" :: "type \<Rightarrow> logic" ("BUNIT'(_')")
translations "BUNIT('a)" == "CONST mk_base_unit TYPE('a)"

lemma magQuant_mk [si_eq]: "\<lbrakk>BUNIT('u::dim_type)\<rbrakk>\<^sub>Q = 1"
  by (simp add: magQuant_def, transfer, simp)

subsection \<open>Polymorphic Operations for SI Base Units \<close>

definition [si_eq]: "meter    = BUNIT(L)"
definition [si_eq]: "second   = BUNIT(T)"
definition [si_eq]: "kilogram = BUNIT(M)"
definition [si_eq]: "ampere   = BUNIT(I)"
definition [si_eq]: "kelvin   = BUNIT(\<Theta>)"
definition [si_eq]: "mole     = BUNIT(N)"
definition [si_eq]: "candela  = BUNIT(J)"

text\<open>Note that as a consequence of our construction, the term @{term meter} is a SI Unit constant of 
SI-type @{typ "'a[L]"}, so a unit of dimension @{typ "Length"} with the magnitude of type @{typ"'a"}.
A magnitude instantiation can be, e.g., an integer, a rational number, a real number, or a vector of 
type @{typ "real\<^sup>3"}. Note than when considering vectors, dimensions refer to the \<^emph>\<open>norm\<close> of the vector,
not to its components.
\<close>

lift_definition is_BaseUnit :: "'a::one['d::dim_type] \<Rightarrow> bool" 
  is "\<lambda> x. mag x = 1 \<and> is_BaseDim (dim x)" .

lemma meter_is_BaseUnit: "is_BaseUnit meter"
  by (simp add: si_eq, transfer, simp)

subsection \<open> Example Unit Equations \<close>

lemma "(meter \<^bold>\<cdot> second\<^sup>-\<^sup>\<one>) \<^bold>\<cdot> second \<cong>\<^sub>Q meter"
  by (si_calc)

end