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

theory Conceptual
  imports "../../DOF/Isa_DOF" "../../DOF/Isa_COL"
begin


doc_class A =
   level :: "int option"
   x :: int  

doc_class B =
   level :: "int option"
   x :: "string"                            (* attributes live in their own name-space *)
   y :: "string list"          <= "[]"      (* and can have arbitrary type constructors *)
                                            (* LaTeX may have problems with this, though *)

text\<open>We may even use type-synonyms for class synonyms ...\<close>
type_synonym XX = B

doc_class C = XX +                           
   z :: "A option"             <= None      (* A LINK, i.e. an attribute that has a type
                                               referring to a document class. Mathematical
                                               relations over document items can be modeled. *)
   g :: "thm"

datatype enum = X1 | X2 | X3
   
doc_class D = B +
   x  :: "string"              <= "\<open>def \<longrightarrow>\<close>" (* overriding default *)
   a1 :: enum                  <= "X2"      (* class - definitions may be mixed 
                                               with arbitrary HOL-commands, thus 
                                               also local definitions of enumerations *)
   a2 :: int                   <= 0

doc_class E = D +
   x :: "string"              <= "''qed''"  (* overriding default *)



doc_class F  = 
   properties :: "term list"
   r          :: "thm list"
   u          :: "file"
   s          :: "typ list"
   b          :: "(A \<times> C) set"  <= "{}"       (* This is a relation link, roughly corresponding
                                                to an association class. It can be used to track
                                                claims to result - relations, for example.*) 
doc_class G = C +                                               
   g :: "thm"  <= "@{thm ''HOL.refl''}"

doc_class M = 
   trace :: "(A + C + D + F) list"
   accepts "A ~~ \<lbrace>C || D\<rbrace>\<^sup>* ~~ \<lbrakk>F\<rbrakk>"



(*
ML\<open> Document.state();\<close>
ML\<open> Session.get_keywords(); (* this looks to be really session global. *)
    Outer_Syntax.command; \<close>
ML\<open> Thy_Header.get_keywords @{theory};(* this looks to be really theory global. *) \<close>
*)

section*[test::A]\<open>Test and Validation\<close>
text\<open>Defining some document elements to be referenced in later on in another theory: \<close>
text*[sdf]\<open> Lorem ipsum @{thm refl}\<close> 
text*[ sdfg] \<open> Lorem ipsum @{thm refl}\<close>  
text*[ xxxy ] \<open> Lorem ipsum @{docitem \<open>sdfg\<close>} rate @{thm refl}\<close>  


end     
