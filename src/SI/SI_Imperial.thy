section \<open> Imperial Units via SI-Units\<close>

theory SI_Imperial
  imports SI_Accepted
begin

subsection \<open> Definitions \<close>

default_sort field_char_0

definition degrees_farenheit :: "'a \<Rightarrow> 'a[\<Theta>]" ("_\<degree>F" [999] 999)
  where [si_eq]: "degrees_farenheit x = (x + 459.67)\<cdot>5/9 \<odot> kelvin"

definition pint :: "'a[Volume]" where
[si_def, si_eq]: "pint = 0.56826125 \<odot> litre"

definition inch :: "'a[L]" where
[si_def, si_eq]: "inch = 25.5 \<odot> milli \<odot> meter"

definition foot :: "'a[L]" where
[si_def, si_eq]: "foot = 0.3048 \<odot> meter"

definition yard :: "'a[L]" where
[si_def, si_eq]: "yard = 0.9144 \<odot> meter"

definition mile :: "'a[L]" where
[si_def, si_eq]: "mile = 1609.344 \<odot> meter"

default_sort type

subsection \<open> Unit Equations \<close>

lemma miles_to_yards: "mile = 1760 \<odot> yard"
  by si_simp
  
lemma miles_to_feet: "mile = 5280 \<odot> foot"
  by si_simp

lemma mph_to_kmh: "1 \<odot> (mile \<^bold>/ hour) = 1.609344 \<odot> ((kilo \<odot> meter) \<^bold>/ hour)"
  by si_simp

lemma farenheit_to_celcius: "T\<degree>F = ((T - 32) \<cdot> 5/9)\<degree>C"
  by si_simp

end