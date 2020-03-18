section \<open> Astronomical Constants \<close>

theory SI_Astronomical
  imports SI_Accepted
begin

definition julian_year :: "'a::field[T]" where
"julian_year = 365.25 \<odot> day"

definition light_year :: "'a::field_char_0[L]" where
"light_year = QCOERCE[L] (\<^bold>c \<^bold>\<cdot> julian_year)"

end