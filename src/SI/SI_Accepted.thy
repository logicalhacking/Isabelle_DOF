section \<open> Non-SI Units Accepted for SI use \<close>

theory SI_Accepted
  imports SI_Derived
begin

definition [si_def, si_eq]: "minute = 60 \<odot> second"

definition [si_def, si_eq]: "hour = 60 \<odot> minute"

definition [si_def, si_eq]: "day = 24 \<odot> hour"

definition [si_def, si_eq]: "astronomical_unit = 149597870700 \<odot> meter"

definition degree :: "'a::real_field[L/L]" where
[si_def, si_eq]: "degree = (2\<cdot>(of_real pi) / 180) \<odot> radian"

abbreviation degrees ("_\<degree>" [999] 999) where "n\<degree> \<equiv> n \<odot> degree"

definition [si_def, si_eq]: "litre = 1/1000 \<odot> meter\<^sup>\<three>"

abbreviation "tonne \<equiv> 10^3 \<odot> kilogram"

subsection \<open> Examples \<close>

lemma "watt \<^bold>\<cdot> hour \<cong>\<^sub>Q 3600 \<odot> joule"
  by (si_calc)

end