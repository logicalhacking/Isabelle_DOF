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

chapter\<open>A conceptual introduction into DOF and its features:\<close>

theory 
  Conceptual
imports 
  "Isabelle_DOF.Isa_DOF" 
  "Isabelle_DOF.Isa_COL"
begin

section\<open>Excursion: On the semantic consequences of this definition: \<close>

text\<open>Consider the following document class definition and its consequences:\<close>

doc_class A =
   level :: "int option"
   x :: int


text\<open>This class definition leads an implicit Isabelle/HOL  \<^theory_text>\<open>record\<close>  definition 
(cf. \<^url>\<open>https://isabelle.in.tum.de/doc/isar-ref.pdf\<close>, chapter 11.6.).
Consequently, \<^theory_text>\<open>doc_class\<close>'es inherit the entire theory-infrastructure from Isabelle records:
\<^enum> there is a HOL-type \<^typ>\<open>A\<close> and its extensible version \<^typ>\<open>'a A_scheme\<close> 
\<^enum> there are HOL-terms representing \<^emph>\<open>doc\_class instances\<close> with the high-level syntax:
    \<^enum> \<^term>\<open>undefined\<lparr>level := Some (1::int), x := 5::int \<rparr> :: A\<close>
      (Note that this way to construct an instance is not necessarily computable
    \<^enum> \<^term>\<open>\<lparr>tag_attribute = X, level = Y, x = Z\<rparr> :: A\<close>
    \<^enum> \<^term>\<open>\<lparr>tag_attribute = X, level = Y, x = Z, \<dots> = M\<rparr> :: ('a A_scheme)\<close>
\<^enum> there is an entire proof infra-structure allowing to reason about \<^emph>\<open>doc\_class instances\<close>;
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

text\<open>The generated theory of the \<^theory_text>\<open>doc_class\<close> A can be inspected, of course, by:\<close>  
find_theorems (60) name:Conceptual name:A

text\<open>A more abstract view on the state of the DOF machine can be found here:\<close>

print_doc_classes

print_doc_items

text\<open>... and an ML-level output:\<close>

ML\<open>
val docitem_tab = DOF_core.get_instances \<^context>;
val isa_transformer_tab = DOF_core.get_isa_transformers \<^context>;
val docclass_tab = DOF_core.get_onto_classes \<^context>;

\<close>

ML\<open>
Name_Space.dest_table docitem_tab;
Name_Space.dest_table isa_transformer_tab;
Name_Space.dest_table docclass_tab;
\<close>
text\<open>... or as ML assertion: \<close>
ML\<open> 
@{assert} (Name_Space.dest_table docitem_tab = []);
fun match ("Conceptual.A", (* the long-name *)
            DOF_core.Onto_Class {params, name, virtual,inherits_from=NONE, 
                                 attribute_decl, rejectS=[],rex=[], invs=[]}) 
            = (Binding.name_of name = "A")
  | match _ = false;

@{assert} (exists match (Name_Space.dest_table docclass_tab))
\<close>

text\<open>As a consequence of the theory of the \<^theory_text>\<open>doc_class\<close> \<open>A\<close>, the code-generator setup lets us 
evaluate statements such as: \<close>

value\<open> the(A.level (A.make 3 (Some 4) 5)) = 4\<close>

text\<open>And further, as a consequence of the above semantic construction of \<^theory_text>\<open>doc_class\<close>'es, the internal
\<open>\<lambda>\<close>-calculus representation of class instances looks as follows:\<close>

ML\<open>
@{term \<open>the(A.level (A.make 3 (Some 4) 5))\<close>};
fun match (Const("Option.option.the",_) $ 
      (Const ("Conceptual.A.level",_) $  
         (Const ("Conceptual.A.make", _) $ u $ v $ w))) = true
   |match _ = false;
@{assert} (match @{term \<open>the(A.level (A.make 3 (Some 4) 5))\<close>})
\<close>

text\<open>And finally, via the code-generation, we have the following programmable 
     access to values representing class instances:\<close>
ML\<open>
val A_make = @{code A.make};
val zero   = @{code "0::int"};
val one    = @{code "1::int"};
val add    = @{code "(+) :: int \<Rightarrow> int \<Rightarrow> int"};

A_make zero (SOME one) (add one one)
\<close>

section\<open>Building up a conceptual class hierarchy:\<close>

text\<open>An independent class-tree root: \<close>

doc_class B =
   level :: "int option"
   x :: "string"                            (* attributes live in their own name-space *)
   y :: "string list"          <= "[]"      (* and can have arbitrary type constructors *)
                                            (* LaTeX may have problems with this, though *)

text\<open>We may even use type-synonyms for class synonyms ...\<close>
type_synonym XX = B


section\<open>Examples of inheritance \<close>

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

text\<open>The effect of the invariant declaration is to provide intern HOL definitions for validation 
functions of this invariant. They can be referenced as follows:\<close>
thm br_inv_def
thm br'_inv_def
thm cr_inv_def

term "\<lparr>F.tag_attribute = 5, properties = [], r = [], u = undefined, s = [], b = {}, b' = []\<rparr>"

term "br'_inv (\<lparr>F.tag_attribute = 5, properties = [], r = [], u = undefined, s = [], b = {}, b' = []\<rparr>) "

text\<open>Now, we can use these definitions in order to generate code for these validation functions.
Note, however, that not everything that we can write in an invariant (basically: HOL) is executable,
or even compilable by the code generator setup:\<close>

ML\<open> val cr_inv_code = @{code "cr_inv"} \<close> \<comment> \<open>works albeit thm is abstract ...\<close>
text\<open>while in :\<close>
ML\<open> val br_inv_code = @{code "br_inv"} \<close> \<comment>\<open>this does not work ...\<close> 

text\<open>... the compilation fails due to the fact that nothing prevents the user 
     to define an infinite relation between \<^typ>\<open>A\<close> and  \<^typ>\<open>C\<close>. However, the alternative
variant: \<close>

ML\<open> val br'_inv_code = @{code "br'_inv"} \<close> \<comment> \<open>does work ...\<close>

text\<open>... is compilable ...\<close>

doc_class G = C +
   g :: "thm"  <= "@{thm \<open>HOL.refl\<close>}"  (* warning overriding attribute expected*)

doc_class M = 
   ok :: "unit"
   accepts "A ~~ \<lbrace>C || D\<rbrace>\<^sup>* ~~ \<lbrakk>F\<rbrakk>"

text\<open>The final class and item tables look like this:\<close>
print_doc_classes
print_doc_items

ML\<open>
map fst (Name_Space.dest_table (DOF_core.get_onto_classes \<^context>));

let  val class_ids_so_far = ["Conceptual.A", "Conceptual.B", "Conceptual.C", "Conceptual.D", 
                             "Conceptual.E", "Conceptual.F", "Conceptual.G", "Conceptual.M", 
                             "Isa_COL.float", "Isa_COL.figure", "Isa_COL.chapter", "Isa_COL.section", 
                             "Isa_COL.paragraph", "Isa_COL.subsection", "Isa_COL.figure_group", 
                             "Isa_COL.text_element", "Isa_COL.subsubsection", 
                             "Isa_COL.side_by_side_figure"]
     val docclass_tab = map fst (Name_Space.dest_table (DOF_core.get_onto_classes \<^context>));
in @{assert} (class_ids_so_far = docclass_tab) end\<close>

section\<open>For Test and Validation\<close>

text*[sdf]         \<open> Lorem ipsum ... \<close>         \<comment> \<open>anonymous reference\<close>
text*[sdfg :: F]   \<open> Lorem ipsum ...\<close>          \<comment> \<open>some F instance \<close>  

end
