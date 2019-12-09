theory SI 
  imports Main
begin

text\<open>
The International System of Units (SI, abbreviated from the French 
Système international (d'unités)) is the modern form of the metric 
system and is the most widely used system of measurement. It comprises
a coherent system of units of measurement built on seven base units, 
which are the second, metre, kilogram, ampere, kelvin, mole, candela, 
and a set of twenty prefixes to the unit names and unit symbols that
may be used when specifying multiples and fractions of the units. 
The system also specifies names for 22 derived units, such as lumen and 
watt, for other common physical quantities.

(cited from \<^url>\<open>https://en.wikipedia.org/wiki/International_System_of_Units\<close>).\<close>

text\<open> This is an attempt to model the system and its derived entities (cf.
\<^url>\<open>https://www.quora.com/What-are-examples-of-SI-units\<close>) in Isabelle/HOL.
The design objective are twofold (and for the case of Isabelle somewhat
contradictory, see below)
\<close>

section\<open>SI's as Values.\<close>

record SI = 
  Second   :: int 
  Meter    :: int 
  Kilogram :: int 
  Ampere   :: int 
  Kelvin   :: int 
  Mole     :: int
  Candela  :: int


definition ONE_SI::"SI" ("1\<^sub>S\<^sub>I") 
  where "1\<^sub>S\<^sub>I = (\<lparr> Second = 0::int, Meter = 0::int, Kilogram = 0::int,  
                 Ampere = 0::int,  Kelvin = 0::int, Mole  = 0::int, 
                 Candela  = 0::int, \<dots>       = () \<rparr>)" 


text\<open>Example: Watt is \<open>kg\<cdot>m\<^sup>2\<cdot>s\<^sup>−\<^sup>3\<close>. Joule is \<open>kg\<cdot>m\<^sup>2\<cdot>s\<^sup>−\<^sup>2\<close>. \<close>
definition "Watt \<equiv> \<lparr> Second = -3, Meter = 2,  Kilogram = 1, 
                      Ampere = 0,  Kelvin = 0, Mole = 0, Candela = 0 \<rparr>" 
definition "Joule\<equiv> \<lparr> Second = -2, Meter = 2,  Kilogram = 1, 
                      Ampere = 0,  Kelvin = 0, Mole = 0, Candela = 0 \<rparr>"
definition "Hertz\<equiv> 1\<^sub>S\<^sub>I\<lparr>Second := -1\<rparr>"

value " Watt =  \<lparr> Second = -2, Meter = 1, Kilogram = 7, 
                  Ampere = 0, Kelvin = 0, Mole = 0, Candela = 0\<rparr>"

class unit\<^sub>C = 
  fixes   id :: "'a \<Rightarrow> 'a"  (* hack *)
  assumes endo: "\<forall>x\<in>(UNIV::'a set). \<forall>y\<in>(UNIV::'a set). x = y"

instantiation unit :: unit\<^sub>C
begin
definition "id = (\<lambda>x::unit. x) "
instance  proof(intro_classes)
             show " \<forall>x\<in>(UNIV:: unit set). \<forall>y\<in>UNIV. x = y"
               by auto
          qed
end


instantiation SI_ext :: (unit\<^sub>C) one 
begin
definition "(1::('a::unit\<^sub>C)SI_ext) = 
                  \<lparr> Second = 0::int, Meter = 0::int, Kilogram = 0::int,  
                    Ampere = 0::int,  Kelvin = 0::int, Mole  = 0::int, 
                    Candela  = 0::int,
                    \<dots>       = undefined \<rparr>" 
instance ..
end


lemma XXX [code_unfold] : "(1::SI) = 1\<^sub>S\<^sub>I "
  by (simp add: one_SI_ext_def ONE_SI_def)

term "one ::('a::unit\<^sub>C)SI_ext "
term "1 ::('a::unit\<^sub>C)SI_ext "
term "(1::SI)\<lparr> more := () \<rparr> \<lparr>Second := -1\<rparr> "
value "1\<^sub>S\<^sub>I \<lparr>Second := -1\<rparr> "

instantiation SI_ext  :: (unit\<^sub>C) times 
begin 
definition "(X::('a::unit\<^sub>C)SI_ext) * Y = 
             \<lparr> Second   = Second X   + Second Y, 
               Meter    = Meter X    + Meter Y, 
               Kilogram = Kilogram X + Kilogram Y,
               Ampere   = Ampere X   + Ampere Y,
               Kelvin   = Kelvin X   + Kelvin Y,
               Mole     = Mole X     + Mole Y, 
               Candela  = Candela X  + Candela Y, 
               \<dots>       = undefined \<rparr>"
instance ..
end

term "set"
lemma YYY [code_unfold] : 
      "(X::SI) * Y  = \<lparr> Second   = Second X   + Second Y, 
                        Meter    = Meter X    + Meter Y, 
                        Kilogram = Kilogram X + Kilogram Y,
                        Ampere   = Ampere X   + Ampere Y,
                        Kelvin   = Kelvin X   + Kelvin Y,
                        Mole     = Mole X     + Mole Y, 
                        Candela  = Candela X  + Candela Y, 
                        \<dots>       = () \<rparr> "
  by (simp add: times_SI_ext_def)


instantiation SI_ext  :: (unit\<^sub>C) comm_monoid_mult
begin
instance proof(intro_classes)
  fix a b c  show "(a:: ('a)SI_ext) * b * c = a * (b * c)"
    unfolding times_SI_ext_def 
    by (auto simp: mult.assoc )
next
  fix a b show "(a:: ('a)SI_ext) * b = b * a"
    unfolding times_SI_ext_def 
    by (auto simp:  mult.commute )
next
  fix a::"('a::unit\<^sub>C)SI_ext" show "1 * a = a"
    unfolding times_SI_ext_def one_SI_ext_def
    apply (auto simp: mult.commute, rule sym)
    apply(subst  surjective)
    by (metis  UNIV_I endo)
  qed
end

value "Hertz * 1\<^sub>S\<^sub>I "
value "Watt = Joule * Hertz"


section\<open>SI's as Types.\<close>


class si = one + ab_semigroup_mult +
  fixes second   :: "'a \<Rightarrow> int"
  fixes meter    :: "'a \<Rightarrow> int" 
  fixes kilogram :: "'a \<Rightarrow> int" 
  fixes ampere   :: "'a \<Rightarrow> int" 
  fixes kelvin   :: "'a \<Rightarrow> int" 
  fixes mole     :: "'a \<Rightarrow> int"
  fixes candela  :: "'a \<Rightarrow> int"

definition si\<^sub>c\<^sub>o\<^sub>m\<^sub>p\<^sub>a\<^sub>t\<^sub>i\<^sub>b\<^sub>l\<^sub>e :: "'a::si \<Rightarrow> 'b::si \<Rightarrow> bool"
  where   "si\<^sub>c\<^sub>o\<^sub>m\<^sub>p\<^sub>a\<^sub>t\<^sub>i\<^sub>b\<^sub>l\<^sub>e X Y = (second X = second Y \<and> meter X = meter Y \<and>
                             kilogram X = kilogram Y \<and> ampere X = ampere Y \<and> 
                             kelvin X = kelvin Y \<and> mole X = mole Y \<and> candela X = candela Y )"

text\<open>SI's as Value are perfectly compatible with this type interface.\<close>
instantiation SI_ext  :: (unit\<^sub>C) si
begin
  definition second   where "second   = Second"
  definition meter    where "meter    = Meter"
  definition kilogram where "kilogram = Kilogram"
  definition ampere   where "ampere   = Ampere"
  definition kelvin   where "kelvin   = Kelvin"
  definition mole     where "mole     = Mole"
  definition candela  where "candela  = Candela"
instance ..
end


end