(*************************************************************************
 * Copyright (C) 
 *               2019      The University of Exeter 
 *               2018-2019 The University of Paris-Saclay
 *               2018      The University of Sheffield
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

section\<open>A conceptual introduction into DOF and its features:\<close>

theory Conceptual
  imports "../../DOF/Isa_DOF" "../../DOF/Isa_COL"
begin


doc_class A =
   level :: "int option"
   x :: int

subsection\<open>Excursion: On the semantic consequences of this definition: \<close>

text\<open>This class definition leads an implicit Isabelle/HOL  \<^theory_text>\<open>record\<close>  definition 
(cf. \<^url>\<open>https://isabelle.in.tum.de/dist/Isabelle2021/doc/isar-ref.pdf\<close>, chapter 11.6.).
Consequently, \<^theory_text>\<open>doc_class\<close>'es inherit the entire theory-infrastructure from Isabelle records:
\<^enum> there is a HOL-type \<^typ>\<open>A\<close> and its extensible version \<^typ>\<open>'a A_scheme\<close> 
\<^enum> there are HOL-terms representing \<^emph>\<open>doc_class instances\<close> with the high-level syntax:
    \<^enum> \<^term>\<open>undefined\<lparr>level := Some (1::int), x := 5::int \<rparr> :: A\<close>
      (Note that this way to construct an instance is not necessarily computable
    \<^enum> \<^term>\<open>\<lparr>tag_attribute = X, level = Y, x = Z\<rparr> :: A\<close>
    \<^enum> \<^term>\<open>\<lparr>tag_attribute = X, level = Y, x = Z, \<dots> = M\<rparr> :: ('a A_scheme)\<close>
\<^enum> there is an entire proof infra-structure allowing to reason about \<^emph>\<open>doc_class instances\<close>;
  this involves the constructor, the selectors (representing the  \<^emph>\<open>attributes\<close> in OO lingo)
  the update functions, the rules to establish equality and, if possible the code generator
  setups:
    \<^enum> \<^term>\<open>A.make :: int \<Rightarrow> int option \<Rightarrow> int \<Rightarrow> A\<close>
    \<^enum> \<^term>\<open>A.level :: 'a A_scheme \<Rightarrow> int option\<close>
    \<^enum> \<^term>\<open>A.level_update :: (int option \<Rightarrow> int option) \<Rightarrow> 'a A_scheme \<Rightarrow> 'a A_scheme\<close>
    \<^enum> ...
  together with the rules such as:
    \<^enum> @{thm [display] A.simps(2)}
    \<^enum> @{thm [display] A.simps(6)}
    \<^enum> ...
\<close>
(* the generated theory of the \<^theory_text>\<open>doc_class\<close> A can be inspected, of course, by *)
find_theorems (60) name:Conceptual name:A


text\<open>As a consequence of the theory of the \<^theory_text>\<open>doc_class\<close> \<open>A\<close>, the code-generator setup lets us 
evaluate statements such as: \<close>

value\<open> the(A.level (A.make 3 (Some 4) 5)) = 4\<close>

text\<open>And finally, as a consequence of the above semantic construction of \<^theory_text>\<open>doc_class\<close>'es, the internal
\<open>\<lambda>\<close>-calculus representation of class instances looks as follows:\<close>

ML\<open>
val tt = @{term \<open>the(A.level (A.make 3 (Some 4) 5))\<close>}
\<close>

text\<open>For the code-generation, we have the following access to values representing class instances:\<close>
ML\<open>
val A_make = @{code A.make};
val zero   = @{code "0::int"};
val one    = @{code "1::int"};
val add    = @{code "(+) :: int \<Rightarrow> int \<Rightarrow> int"};

A_make zero (SOME one) (add one one)
\<close>


subsection\<open>An independent class-tree root: \<close>


doc_class B =
   level :: "int option"
   x :: "string"                            (* attributes live in their own name-space *)
   y :: "string list"          <= "[]"      (* and can have arbitrary type constructors *)
                                            (* LaTeX may have problems with this, though *)

text\<open>We may even use type-synonyms for class synonyms ...\<close>
type_synonym XX = B


subsection\<open>Examples of inheritance \<close>

doc_class C = XX +                           
   z :: "A option"             <= None      (* A LINK, i.e. an attribute that has a type
                                               referring to a document class. Mathematical
                                               relations over document items can be modeled. *)
   g :: "thm"                               (* a reference to the proxy-type 'thm' allowing
                                               to denote references to theorems inside attributes *)

datatype enum = X1 | X2 | X3                (* we add an enumeration type ... *)
   
doc_class D = B +
   x  :: "string"              <= "\<open>def \<longrightarrow>\<close>" (* overriding default *)
   a1 :: enum                  <= "X2"      (* class - definitions may be mixed 
                                               with arbitrary HOL-commands, thus 
                                               also local definitions of enumerations *)
   a2 :: int                   <= 0

doc_class E = D +
   x :: "string"              <= "''qed''"  (* overriding default *)



doc_class F  =     
   properties  :: "term list"
   r           :: "thm list"
   u           :: "file"
   s           :: "typ list"
   b           :: "(A \<times> C) set"  <= "{}"       (* This is a relation link, roughly corresponding
                                                 to an association class. It can be used to track
                                                 claims to result - relations, for example.*) 
   b'          :: "(A \<times> C) list"  <= "[]"
   invariant br :: "r \<sigma> \<noteq> [] \<and> card(b \<sigma>) \<ge> 3"
        and  br':: "r \<sigma> \<noteq> [] \<and> length(b' \<sigma>) \<ge> 3"
        and  cr :: "properties \<sigma> \<noteq> []"

text\<open>The effect of the invariant declaration is to provide intern definitions for validation 
functions of this invariant. They can be referenced as follows:\<close>
thm br_inv_def
thm br'_inv_def
thm cr_inv_def

term "\<lparr>F.tag_attribute = 5, properties = [], r = [], u = undefined, s = [], b = {}, b' = []\<rparr>"

term "br' (\<lparr>F.tag_attribute = 5, properties = [], r = [], u = undefined, s = [], b = {}, b' = []\<rparr>) "

text\<open>Now, we can use these definitions in order to generate code for these validation functions.
Note, however, that not everything that we can write in an invariant (basically: HOL) is executable,
or even compilable by the code generator setup:\<close>

ML\<open> val cr_inv_code = @{code "cr_inv"} \<close> \<comment> \<open>works albeit thm is abstract ...\<close>
text\<open>while in :\<close>
(* ML\<open> val br_inv_code = @{code "br_inv"} \<close> \<comment>\<open>this does not work ...\<close> *)

text\<open>... the compilation fails due to the fact that nothing prevents the user 
     to define an infinite relation between \<^typ>\<open>A\<close> and  \<^typ>\<open>C\<close>. However, the alternative
variant: \<close>

ML\<open> val br'_inv_code = @{code "br'_inv"} \<close> \<comment> \<open>does work ...\<close>

text\<open>... is compilable ...\<close>



doc_class G = C +
   g :: "thm"  <= "@{thm \<open>HOL.refl\<close>}"

doc_class M = 
   ok :: "unit"
   accepts "A ~~ \<lbrace>C || D\<rbrace>\<^sup>* ~~ \<lbrakk>F\<rbrakk>"


(*
ML\<open> Document.state();\<close>
ML\<open> Session.get_keywords(); (* this looks to be really session global. *)
    Outer_Syntax.command; \<close>
ML\<open> Thy_Header.get_keywords @{theory};(* this looks to be really theory global. *) \<close>
*)

open_monitor*[aaa::M]
section*[test::A]\<open>Test and Validation\<close>
term\<open>Conceptual.M.make\<close>
text\<open>Defining some document elements to be referenced in later on in another theory: \<close>
text*[sdf]\<open> Lorem ipsum @{thm refl}\<close> 
text*[ sdfg :: F] \<open> Lorem ipsum @{thm refl}\<close>  
text*[ xxxy ] \<open> Lorem ipsum @{F \<open>sdfg\<close>} rate @{thm refl}\<close>  
close_monitor*[aaa]

end     
