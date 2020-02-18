section \<open> Physical Constants \<close>

theory SI_Constants
  imports SI_Proof
begin

abbreviation "hertz \<equiv> second\<^sup>-\<^sup>\<one>"

abbreviation "radian \<equiv> meter \<^bold>\<cdot> meter\<^sup>-\<^sup>\<one>"

abbreviation "steradian \<equiv> meter\<^sup>\<two> \<^bold>\<cdot> meter\<^sup>-\<^sup>\<two>"

abbreviation "joule \<equiv> kilogram \<^bold>\<cdot> meter\<^sup>\<two> \<^bold>\<cdot>  second\<^sup>-\<^sup>\<two>"

abbreviation "watt \<equiv> kilogram \<^bold>\<cdot> meter\<^sup>\<two> \<^bold>\<cdot> second\<^sup>-\<^sup>\<three>"

abbreviation "coulomb \<equiv> ampere \<^bold>\<cdot> second"

abbreviation "lumen \<equiv> candela \<^bold>\<cdot> steradian"

text \<open> The most general types we support must form a field into which the natural numbers can 
  be injected. \<close>

default_sort field_char_0

abbreviation (input) caesium_frequency:: "'a[T\<^sup>-\<^sup>1]" ("\<Delta>v\<^sub>C\<^sub>s") where
  "caesium_frequency \<equiv> 9192631770\<cdot>hertz"

abbreviation speed_of_light :: "'a[L \<cdot> T\<^sup>-\<^sup>1]" where
  "speed_of_light \<equiv> 299792458\<cdot>(meter\<^bold>\<cdot>second\<^sup>-\<^sup>\<one>)"

abbreviation Planck :: "'a[M \<cdot> L\<^sup>2 \<cdot> T\<^sup>-\<^sup>2 \<cdot> T]" where
  "Planck \<equiv> (6.62607015 \<cdot> 1/(10^34))\<cdot>(joule\<^bold>\<cdot>second)"

abbreviation elementary_charge :: "'a[I \<cdot> T]" where
  "elementary_charge \<equiv> (1.602176634 \<cdot> 1/(10^19))\<cdot>coulomb"

abbreviation Boltzmann :: "'a[M \<cdot> L\<^sup>2 \<cdot> T\<^sup>-\<^sup>2 \<cdot> \<Theta>\<^sup>-\<^sup>1]" where
  "Boltzmann \<equiv> (1.380649\<cdot>1/(10^23))\<cdot>(joule \<^bold>/ kelvin)"

abbreviation Avogadro :: "'a[N\<^sup>-\<^sup>1]" where
"Avogadro \<equiv> 6.02214076\<cdot>(10^23)\<cdot>(mole\<^sup>-\<^sup>\<one>)"

abbreviation max_luminous_frequency :: "'a[T\<^sup>-\<^sup>1]" where
"max_luminous_frequency \<equiv> (540\<cdot>10^12)\<cdot>hertz"

abbreviation luminous_efficacy :: "'a[J \<cdot> (L\<^sup>2 \<cdot> L\<^sup>-\<^sup>2) \<cdot> (M \<cdot> L\<^sup>2 \<cdot> T\<^sup>-\<^sup>3)\<^sup>-\<^sup>1]" where
"luminous_efficacy \<equiv> 683\<cdot>(lumen\<^bold>/watt)"

abbreviation gravitational_constant :: "'a[L\<^sup>3 \<cdot> M\<^sup>-\<^sup>1 \<cdot> T\<^sup>-\<^sup>2]" where
  "gravitational_constant \<equiv> (6.6743015 \<cdot> 1/(10 ^ 11)) \<cdot> (meter\<^sup>\<three>\<^bold>\<cdot>kilogram\<^sup>-\<^sup>\<one>\<^bold>\<cdot>second\<^sup>-\<^sup>\<two>)"

thm si_def

theorem Quant_eq_iff_same_dim:
  "x \<approx>\<^sub>Q y \<longleftrightarrow> x = y"
  by (transfer, simp)

theorem hertz_definition: "1\<cdot>hertz = \<Delta>v\<^sub>C\<^sub>s / 9192631770"
  by (simp add: unit_eq_iff_magn_eq si_def)

theorem second_definition: "1\<cdot>second \<approx>\<^sub>Q (9192631770::_[\<one>]) \<^bold>/ \<Delta>v\<^sub>C\<^sub>s"
  by (simp add: unit_equiv_iff, simp add: Quant_equiv_def unit_eq_iff_magn_eq si_def)

default_sort type

end