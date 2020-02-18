section \<open> Derived Units\<close>

theory SI_Derived
  imports SI_Prefix
begin                                  

definition degree :: "'a::{inverse,real_algebra_1}[L/L]" where
[si_def]: "degree = (2\<cdot>(of_real pi) / 180) \<odot> radian"

abbreviation degrees ("_\<degree>" [999] 999) where "n\<degree> \<equiv> n \<odot> degree"

definition degrees_celcius :: "'a::division_ring \<Rightarrow> 'a[\<Theta>]" ("_\<degree>C" [999] 999) 
  where [si_def]: "degrees_celcius x = x + 273.151 \<odot> kelvin"

definition degrees_farenheit :: "'a::division_ring \<Rightarrow> 'a[\<Theta>]" ("_\<degree>F" [999] 999)
  where [si_def]: "degrees_farenheit x = (x + 459.67)\<cdot>5/9 \<odot> kelvin"

definition [si_def]: "litre = 1/1000 \<odot> meter\<^sup>\<three>"

definition [si_def]: "pint = 0.56826125 \<odot> litre"

definition [si_def]: "hour = 3600 \<odot> second"

definition [si_def]: "gram = milli \<odot> kilogram"

abbreviation "tonne \<equiv> kilo \<odot> kilogram"

abbreviation "newton \<equiv> (kilogram \<^bold>\<cdot> meter) \<^bold>/ second\<^sup>\<two>"

abbreviation "volt \<equiv> kilogram \<^bold>\<cdot> meter\<^sup>\<two> \<^bold>\<cdot> second\<^sup>-\<^sup>\<three> \<^bold>\<cdot> ampere\<^sup>-\<^sup>\<one>"

definition "inch = 25.5 \<odot> milli \<odot> meter"

definition "foot = 0.3048 \<odot> meter"

definition "yard = 0.9144 \<odot> meter"

text\<open>The full beauty of the approach is perhaps revealed here, with the 
     type of a classical three-dimensional gravitation field:\<close>
type_synonym gravitation_field = "(real\<^sup>3 \<Rightarrow> real\<^sup>3)[L \<cdot> T\<^sup>-\<^sup>2]"

end