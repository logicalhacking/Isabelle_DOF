section \<open> Derived Units\<close>

theory SI_Derived
  imports SI_Prefix
begin                                  

subsection \<open> Definitions \<close>

abbreviation "newton \<equiv> kilogram \<^bold>\<cdot> meter \<^bold>\<cdot> second\<^sup>-\<^sup>\<two>"

abbreviation "pascal \<equiv> kilogram \<^bold>\<cdot> meter\<^sup>-\<^sup>\<one> \<^bold>\<cdot> second\<^sup>-\<^sup>\<two>"

abbreviation "volt \<equiv> kilogram \<^bold>\<cdot> meter\<^sup>\<two> \<^bold>\<cdot> second\<^sup>-\<^sup>\<three> \<^bold>\<cdot> ampere\<^sup>-\<^sup>\<one>"

abbreviation "farad \<equiv> kilogram\<^sup>-\<^sup>\<one> \<^bold>\<cdot> meter\<^sup>-\<^sup>\<two> \<^bold>\<cdot> second\<^sup>\<four> \<^bold>\<cdot> ampere\<^sup>\<two>"

abbreviation "ohm \<equiv> kilogram \<^bold>\<cdot> meter\<^sup>\<two> \<^bold>\<cdot> second\<^sup>-\<^sup>\<three> \<^bold>\<cdot> ampere\<^sup>-\<^sup>\<two>"

abbreviation "siemens \<equiv> kilogram\<^sup>-\<^sup>\<one> \<^bold>\<cdot> meter\<^sup>-\<^sup>\<two> \<^bold>\<cdot> second\<^sup>\<three> \<^bold>\<cdot> ampere\<^sup>\<two>"

abbreviation "weber \<equiv> kilogram \<^bold>\<cdot> meter\<^sup>\<two> \<^bold>\<cdot> second\<^sup>-\<^sup>\<two> \<^bold>\<cdot> ampere\<^sup>-\<^sup>\<one>"

abbreviation "tesla \<equiv> kilogram \<^bold>\<cdot> meter\<^sup>-\<^sup>\<two> \<^bold>\<cdot> ampere\<^sup>-\<^sup>\<one>"

abbreviation "henry \<equiv> kilogram \<^bold>\<cdot> meter\<^sup>\<two> \<^bold>\<cdot> second\<^sup>-\<^sup>\<two> \<^bold>\<cdot> ampere\<^sup>-\<^sup>\<two>"

definition degrees_celcius :: "'a::field_char_0 \<Rightarrow> 'a[\<Theta>]" ("_\<degree>C" [999] 999) 
  where [si_eq]: "degrees_celcius x = x + 273.151 \<odot> kelvin"

definition [si_eq]: "gram = milli \<odot> kilogram"

text\<open>The full beauty of the approach is perhaps revealed here, with the 
     type of a classical three-dimensional gravitation field:\<close>
type_synonym gravitation_field = "(real\<^sup>3 \<Rightarrow> real\<^sup>3)[L \<cdot> T\<^sup>-\<^sup>2]"

subsection \<open> Properties \<close>

lemma kilogram: "kilo \<odot> gram = kilogram"
  by (si_simp)

end