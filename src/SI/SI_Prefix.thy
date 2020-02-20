section \<open> SI Prefixes \<close>

theory SI_Prefix
  imports SI_Constants
begin

default_sort ring_char_0

definition deca :: "'a" where [si_eq]: "deca = 10^1"

definition hecto :: "'a" where [si_eq]: "hecto = 10^2"

definition kilo :: "'a" where [si_eq]: "kilo = 10^3"

definition mega :: "'a" where [si_eq]: "mega = 10^6"

definition giga :: "'a" where [si_eq]: "giga = 10^9"

definition tera :: "'a" where [si_eq]: "tera = 10^12"

definition peta :: "'a" where [si_eq]: "peta = 10^15"

default_sort field_char_0

definition deci :: "'a" where [si_eq]: "deci = 1/10^1"

definition centi :: "'a" where [si_eq]: "centi = 1/10^2"

definition milli :: "'a" where [si_eq]: "milli = 1/10^3"

definition micro :: "'a" where [si_eq]: "micro = 1/10^6"

definition nano :: "'a" where [si_eq]: "nano = 1/10^9"

default_sort type

end