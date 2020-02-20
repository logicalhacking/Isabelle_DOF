section \<open> Imperial Units via SI \<close>

theory SI_Imperial
  imports SI_Accepted
begin

subsection \<open> Definition \<close>

definition degrees_farenheit :: "'a::field_char_0 \<Rightarrow> 'a[\<Theta>]" ("_\<degree>F" [999] 999)
  where [si_eq]: "degrees_farenheit x = (x + 459.67)\<cdot>5/9 \<odot> kelvin"

definition [si_def, si_eq]: "pint = 0.56826125 \<odot> litre"

definition [si_def, si_eq]: "inch = 25.5 \<odot> milli \<odot> meter"

definition [si_def, si_eq]: "foot = 0.3048 \<odot> meter"

definition [si_def, si_eq]: "yard = 0.9144 \<odot> meter"

subsection \<open> Properties \<close>

lemma celcius_to_farenheit: "(T::rat)\<degree>C = ((T - 32) \<cdot> 5/9)\<degree>F"
  oops

end