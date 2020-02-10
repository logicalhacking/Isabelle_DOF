section \<open> Derived Units\<close>

theory SI_Derived
  imports SI_Prefix
begin

definition "radian = 1 \<cdot> (meter \<^bold>\<cdot> meter\<^sup>-\<^sup>\<one>)"                                  

definition degree :: "real[meter / meter]" where
[si_def]: "degree = (2\<cdot>(UNIT(pi,_)) / 180)\<cdot>radian"

abbreviation degrees ("_\<degree>" [999] 999) where "n\<degree> \<equiv> n\<cdot>degree" 

definition [si_def]: "litre = 1/1000 \<cdot> meter\<^sup>\<three>"

definition [si_def]: "pint = 0.56826125 \<cdot> litre"

definition [si_def]: "hour = 3600 \<cdot> second"

abbreviation "tonne \<equiv> kilo\<cdot>kilogram"

abbreviation "newton \<equiv> (kilogram \<^bold>\<cdot> meter) \<^bold>/ second\<^sup>\<two>"

abbreviation "volt \<equiv> kilogram \<^bold>\<cdot> meter\<^sup>\<two> \<^bold>\<cdot> second\<^sup>-\<^sup>\<three> \<^bold>\<cdot> ampere\<^sup>-\<^sup>\<one>"

abbreviation "watt \<equiv> kilogram \<^bold>\<cdot> meter\<^sup>\<two> \<^bold>\<cdot> second\<^sup>-\<^sup>\<three>"

abbreviation "joule \<equiv> kilogram \<^bold>\<cdot> meter\<^sup>\<two> \<^bold>\<cdot>  second\<^sup>-\<^sup>\<two>"

text\<open>The full beauty of the approach is perhaps revealed here, with the 
     type of a classical three-dimensional gravitation field:\<close>
type_synonym gravitation_field = "(real\<^sup>3 \<Rightarrow> real\<^sup>3)[meter \<cdot> (second)\<^sup>-\<^sup>2]"


end