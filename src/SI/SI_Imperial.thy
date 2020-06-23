section \<open> Imperial Units via SI-Units\<close>

theory SI_Imperial
  imports SI_Accepted
begin

subsection \<open> Definitions \<close>

default_sort field_char_0

definition inch :: "'a[L]" where
[si_eq]: "inch = 25.5 \<odot> milli \<odot> meter"

definition foot :: "'a[L]" where
[si_eq]: "foot = 0.3048 \<odot> meter"

definition yard :: "'a[L]" where
[si_eq]: "yard = 0.9144 \<odot> meter"

definition mile :: "'a[L]" where
[si_eq]: "mile = 1609.344 \<odot> meter"

definition nautical_mile :: "'a[L]" where
[si_eq]: "nautical_mile = 1852 \<odot> meter"

definition knot :: "'a[L \<cdot> T\<^sup>-\<^sup>1]" where
[si_eq]: "knot = 1 \<odot> (nautical_mile \<^bold>/ hour)"

definition pint :: "'a[Volume]" where
[si_eq]: "pint = 0.56826125 \<odot> litre"

definition gallon :: "'a[Volume]" where
[si_eq]: "gallon = 8 \<odot> pint"

definition pound :: "'a[M]" where
[si_eq]: "pound = 0.45359237 \<odot> kilogram"

definition ounce :: "'a[M]" where
[si_eq]: "ounce = 1/16 \<odot> pound"

definition stone :: "'a[M]" where
[si_eq]: "stone = 14 \<odot> pound"

definition degrees_farenheit :: "'a \<Rightarrow> 'a[\<Theta>]" ("_\<degree>F" [999] 999)
  where [si_eq]: "degrees_farenheit x = (x + 459.67)\<cdot>5/9 \<odot> kelvin"

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