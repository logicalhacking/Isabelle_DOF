section \<open> Physical Constants \<close>

theory SI_Constants
  imports SI_Quantities
begin

abbreviation speed_of_light :: "'a::division_ring[L \<cdot> T\<^sup>-\<^sup>1]" where
  "speed_of_light \<equiv> 299792458\<cdot>(meter\<^bold>\<cdot>second\<^sup>-\<^sup>\<one>)"

abbreviation gravitational_constant where
  "gravitational_constant \<equiv> (6.6743015 \<cdot> 1/(10 ^ 11)) \<cdot> (meter\<^sup>\<three>\<^bold>\<cdot>kilogram\<^sup>-\<^sup>\<one>\<^bold>\<cdot>second\<^sup>-\<^sup>\<two>)"

end