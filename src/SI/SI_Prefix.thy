section \<open> SI Prefixes \<close>

theory SI_Prefix
  imports SI_Quantities
begin

definition [si_def]: "giga = UNIT(1000000000, _)"

definition [si_def]: "mega = UNIT(1000000, _)"

definition [si_def]: "kilo = UNIT(1000, _)"

definition [si_def]: "hecto = UNIT(100, _)"

definition [si_def]: "deca = UNIT(10, _)"

definition [si_def]: "deci = UNIT(0.1, _)"

definition [si_def]: "centi = UNIT(0.01, _)"

definition [si_def]: "milli = UNIT(0.001, _)"

definition [si_def]: "micro = UNIT(0.000001, _)"

definition [si_def]: "nano = UNIT(0.000000001, _)"

end