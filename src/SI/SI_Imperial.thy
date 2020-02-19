section \<open> Imperial Units via SI \<close>

theory SI_Imperial
  imports SI_Accepted
begin

definition [si_def, si_eq]: "pint = 0.56826125 \<odot> litre"

definition [si_def, si_eq]: "inch = 25.5 \<odot> milli \<odot> meter"

definition [si_def, si_eq]: "foot = 0.3048 \<odot> meter"

definition [si_def, si_eq]: "yard = 0.9144 \<odot> meter"

end