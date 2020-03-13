section \<open> Physical Constants \<close>

theory SI_Constants
  imports SI_Units
begin

subsection \<open> Core Derived Units \<close>

abbreviation "hertz \<equiv> second\<^sup>-\<^sup>\<one>"

abbreviation "radian \<equiv> meter \<^bold>\<cdot> meter\<^sup>-\<^sup>\<one>"

abbreviation "steradian \<equiv> meter\<^sup>\<two> \<^bold>\<cdot> meter\<^sup>-\<^sup>\<two>"

abbreviation "joule \<equiv> kilogram \<^bold>\<cdot> meter\<^sup>\<two> \<^bold>\<cdot>  second\<^sup>-\<^sup>\<two>"

abbreviation "watt \<equiv> kilogram \<^bold>\<cdot> meter\<^sup>\<two> \<^bold>\<cdot> second\<^sup>-\<^sup>\<three>"

abbreviation "coulomb \<equiv> ampere \<^bold>\<cdot> second"

abbreviation "lumen \<equiv> candela \<^bold>\<cdot> steradian"

subsection \<open> Constants \<close>

text \<open> The most general types we support must form a field into which the natural numbers can 
  be injected. \<close>

default_sort field_char_0

text \<open> Hyperfine transition frequency of frequency of Cs \<close>

abbreviation caesium_frequency:: "'a[T\<^sup>-\<^sup>1]" ("\<Delta>v\<^sub>C\<^sub>s") where
  "caesium_frequency \<equiv> 9192631770 \<odot> hertz"

text \<open> Speed of light in vacuum \<close>

abbreviation speed_of_light :: "'a[L \<cdot> T\<^sup>-\<^sup>1]" ("\<^bold>c") where
  "speed_of_light \<equiv> 299792458 \<odot> (meter\<^bold>\<cdot>second\<^sup>-\<^sup>\<one>)"

text \<open> Planck constant \<close>

abbreviation Planck :: "'a[M \<cdot> L\<^sup>2 \<cdot> T\<^sup>-\<^sup>2 \<cdot> T]" ("\<^bold>h") where
  "Planck \<equiv> (6.62607015 \<cdot> 1/(10^34)) \<odot> (joule\<^bold>\<cdot>second)"

text \<open> Elementary charge \<close>

abbreviation elementary_charge :: "'a[I \<cdot> T]" ("\<^bold>e") where
  "elementary_charge \<equiv> (1.602176634 \<cdot> 1/(10^19)) \<odot> coulomb"

text \<open> The Boltzmann constant \<close>

abbreviation Boltzmann :: "'a[M \<cdot> L\<^sup>2 \<cdot> T\<^sup>-\<^sup>2 \<cdot> \<Theta>\<^sup>-\<^sup>1]" ("\<^bold>k") where
  "Boltzmann \<equiv> (1.380649\<cdot>1/(10^23)) \<odot> (joule \<^bold>/ kelvin)"

text \<open> The Avogadro number \<close>

abbreviation Avogadro :: "'a[N\<^sup>-\<^sup>1]" ("N\<^sub>A") where
"Avogadro \<equiv> 6.02214076\<cdot>(10^23) \<odot> (mole\<^sup>-\<^sup>\<one>)"

abbreviation max_luminous_frequency :: "'a[T\<^sup>-\<^sup>1]" where
"max_luminous_frequency \<equiv> (540\<cdot>10^12) \<odot> hertz"

text \<open> The luminous efficacy of monochromatic radiation of frequency \<^const>\<open>max_luminous_frequency\<close>. \<close>

abbreviation luminous_efficacy :: "'a[J \<cdot> (L\<^sup>2 \<cdot> L\<^sup>-\<^sup>2) \<cdot> (M \<cdot> L\<^sup>2 \<cdot> T\<^sup>-\<^sup>3)\<^sup>-\<^sup>1]" ("K\<^sub>c\<^sub>d") where
"luminous_efficacy \<equiv> 683 \<odot> (lumen\<^bold>/watt)"

subsection \<open> Basis Theorems \<close>

theorem second_definition: 
  "1 \<odot> second \<cong>\<^sub>Q (9192631770 \<odot> \<one>) \<^bold>/ \<Delta>v\<^sub>C\<^sub>s"
  by si_calc

theorem meter_definition: 
  "1 \<odot> meter \<cong>\<^sub>Q (\<^bold>c \<^bold>/ (299792458 \<odot> \<one>))\<^bold>\<cdot>second"
  "1 \<odot> meter \<cong>\<^sub>Q (9192631770 / 299792458) \<odot> (\<^bold>c \<^bold>/ \<Delta>v\<^sub>C\<^sub>s)"
  by si_calc+

theorem kilogram_definition:
  "1 \<odot> kilogram \<cong>\<^sub>Q (\<^bold>h \<^bold>/ (6.62607015 \<cdot> 1/(10^34) \<odot> \<one>))\<^bold>\<cdot>meter\<^sup>-\<^sup>\<two>\<^bold>\<cdot>second" 
  by si_calc

abbreviation "approx_ice_point \<equiv> 273.15 \<odot> kelvin"

default_sort type

end