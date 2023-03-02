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

theory 
  Attributes
  imports 
  "Isabelle_DOF-Unit-Tests_document"
  "Isabelle_DOF-Ontologies.Conceptual"
begin
ML\<open>@{assert} (1 = 1)\<close>
section\<open>Elementar Creation of Doc-items and Access of their Attibutes\<close>

text\<open>Current status:\<close>
print_doc_classes
print_doc_items

(* this corresponds to low-level accesses : *)
ML\<open>  
val docitem_tab = DOF_core.get_instances \<^context>
val isa_transformer_tab = DOF_core.get_isa_transformers \<^context>
val docclass_tab = DOF_core.get_onto_classes @{context};
\<close>
ML\<open>
map fst (Name_Space.dest_table docitem_tab);
Name_Space.dest_table docclass_tab;

\<close>

ML\<open>
val (oid, DOF_core.Instance {value, ...}) =
    Name_Space.check (Context.Proof \<^context>) (DOF_core.get_instances \<^context>) ("aaa", Position.none)
\<close>

find_theorems (60) name:"Conceptual.M." 

value [simp]"M.trace(M.make undefined [] ())"
value "M.ok(M.make undefined_AAA [] ())"
value "M.trace(M.make undefined_AAA [] ())"
value "M.tag_attribute(M.make undefined_AAA [] ())"


value "M.ok(M.make 0 [] ())"
(*
value "ok(M.make undefined [] ())"
value "ok(M.make 0 [] undefined)"
*)

value [simp] \<open> M.ok 
                   (Conceptual.M.trace_update (\<lambda>x. [])
                    (Conceptual.M.tag_attribute_update (\<lambda>x. 0)
                     (Conceptual.M.ok_update (\<lambda>x. ())
                   (undefined::M)) 
                   ))\<close>

value [simp] \<open> M.ok 
                   (Conceptual.M.trace_update (\<lambda>x. [])
                    (Conceptual.M.tag_attribute_update (\<lambda>x. 0)
                     (Conceptual.M.ok_update (\<lambda>x. ())
                   (undefined::M)) 
                   ))\<close>
value  \<open> M.ok 
                   (Conceptual.M.trace_update (\<lambda>x. [])
                    (Conceptual.M.tag_attribute_update (\<lambda>x. 0)
                     (Conceptual.M.ok_update (\<lambda>x. ())
                   (AAAA::M)) 
                   ))\<close>


value  \<open> M.ok 
                   (Conceptual.M.trace_update (\<lambda>x. [])
                    (Conceptual.M.tag_attribute_update (\<lambda>x. 0)
                     (Conceptual.M.ok_update (\<lambda>x. ())
                   (M.make XX1 XX2 XX3::M)) 
                   ))\<close>


text\<open>A text item containing standard theorem antiquotations and complex meta-information.\<close>
(* crashes in batch mode ... 
text*[dfgdfg::B, Conceptual.B.x ="''f''", y = "[''sdf'']"]\<open> Lorem ipsum ...  @{thm refl} \<close>
*)
text*[dfgdfg::B]\<open> Lorem ipsum ...  @{thm refl} \<close>

text\<open>document class declarations lead also HOL-type declarations (relevant for ontological links).\<close>
typ "C"
typ "D"
text\<open> ... as well as HOL-constant declarations (relevant for monitor rexps and tracres.).\<close>
term "C"

text\<open>Voila what happens on the ML level:\<close>
ML\<open>val Type("Conceptual.B.B_ext",[Type("Conceptual.C.C_ext",t)]) = @{typ "C"};
   val @{typ "D"} = Value_Command.Docitem_Parser.cid_2_cidType "Conceptual.D" @{theory};
   val @{typ "E"} = Value_Command.Docitem_Parser.cid_2_cidType "Conceptual.E" @{theory};
  \<close>

text*[dfgdfg2::C, z = "None"]\<open> Lorem ipsum ... @{thm refl} \<close> 

text*[omega::E, x = "''def''"]\<open> Lorem ipsum ... @{thm refl} \<close> 

text\<open> As mentioned in @{docitem \<open>dfgdfg\<close>} \<close>

text\<open>Here is a simulation what happens on the level of the (HOL)-term representation:\<close>
typ \<open>'a A_scheme\<close>
typ \<open>A\<close>
term "A.x (undefined\<lparr>A.x := 3\<rparr>)"
term "B.x ((undefined::C)\<lparr>B.y := [''sdf'']\<rparr>)"
term "C.z ((undefined::C)\<lparr>B.y := [''sdf''], z:= Some undefined\<rparr>)"

ML\<open>
val SOME {def_occurrence = "Conceptual.A", long_name = "Conceptual.A.x", typ = t, def_pos} 
    = DOF_core.get_attribute_info  "Conceptual.A" "x" @{theory};
DOF_core.get_attribute_info  "Conceptual.B" "x" @{theory};
DOF_core.get_attribute_info  "Conceptual.B" "y" @{theory};
DOF_core.get_attribute_info  "Conceptual.C" "x" @{theory};
val SOME {def_occurrence = "Conceptual.C", long_name = "Conceptual.B.y", typ = t', def_pos}
    = DOF_core.get_attribute_info  "Conceptual.C" "y" @{theory};
    (* this is the situation where an attribute is defined in C, but due to inheritance
       from B, where it is firstly declared which results in a different long_name. *)
DOF_core.get_attribute_info  "Conceptual.C" "z" @{theory};
\<close>


ML\<open>
DOF_core.get_value_local "sdf"   @{context};
DOF_core.get_value_local "sdfg"  @{context};
DOF_core.get_value_local "dfgdfg" @{context};
DOF_core.get_value_local "omega" @{context};
\<close>

text\<open>A not too trivial test: default y -> [].
     At creation :  x -> "f", y -> "sdf".
     The latter wins at access time.
     Then @{term "t"}: creation of a multi inheritance object omega,
     triple updates, the last one wins.\<close>
ML\<open>val s = map HOLogic.dest_string (HOLogic.dest_list @{docitem_attribute y::dfgdfg});
   val t = HOLogic.dest_string (@{docitem_attribute x::omega});  \<close>




section\<open>Mutation of Attibutes in DocItems\<close>

ML\<open> val Const("Groups.zero_class.zero", @{typ "int"}) =  @{docitem_attribute a2::omega} \<close>

update_instance*[omega::E, a2+="1"]

ML\<open> val (s as Const("Groups.one_class.one", @{typ "int"}))=  @{docitem_attribute a2 :: omega} \<close>

update_instance*[omega::E, a2+="6"]

ML\<open> @{docitem_attribute a2::omega};
    val s =  HOLogic.dest_number @{docitem_attribute a2::omega} \<close>

type_synonym ALFACENTAURI = E

update_instance*[omega::ALFACENTAURI, x+="''inition''"]

ML\<open> val s = HOLogic.dest_string ( @{docitem_attribute x::omega}) \<close>
                            
update_instance*[omega::E, y+="[''defini'',''tion'']"]

update_instance*[omega::E, y+="[''en'']"]

ML\<open> val s =  map HOLogic.dest_string (HOLogic.dest_list @{docitem_attribute y::omega}); \<close>

subsection\<open> Example text antiquotation:\<close>
text\<open> @{docitem_attribute y::omega}  \<close>


section\<open>Simulation of a Monitor\<close>

declare[[free_class_in_monitor_checking]]

open_monitor*[figs1::figure_group, 
              caption="''Sample ''"]  
ML\<open>val monitor_infos = DOF_core.get_monitor_infos \<^context>\<close>
text*[testFreeA::A]\<open>\<close>
figure*[fig_A::figure, spawn_columns=False,
        relative_width="90",
        src="''figures/A.png''"]
       \<open> The A train \ldots \<close>

figure*[fig_B::figure, 
        spawn_columns=False,relative_width="90",
        src="''figures/B.png''"]
       \<open> The B train \ldots \<close>  
open_monitor*[figs2::figure_group, 
              caption="''Sample ''"]
ML\<open>val monitor_infos = DOF_core.get_monitor_infos \<^context>\<close>
figure*[fig_C::figure, spawn_columns=False,
        relative_width="90",
        src="''figures/A.png''"]
       \<open> The C train \ldots \<close>
open_monitor*[figs3::figure_group, 
              caption="''Sample ''"]
ML\<open>val monitor_infos = DOF_core.get_monitor_infos \<^context>\<close>

figure*[fig_D::figure, 
        spawn_columns=False,relative_width="90",
        src="''figures/B.png''"]
       \<open> The D train \ldots \<close>
close_monitor*[figs3]

open_monitor*[figs4::figure_group, 
              caption="''Sample ''"]
ML\<open>val monitor_infos = DOF_core.get_monitor_infos \<^context>\<close>

text*[testRejected1::figure_group, caption="''document/figures/A.png''"]
       \<open> The A train \ldots \<close>

figure*[fig_E::figure,
        spawn_columns=False,relative_width="90",
        src="''figures/B.png''"]
       \<open> The E train \ldots \<close>
close_monitor*[figs4]
close_monitor*[figs2]
text*[testRejected2::figure_group, caption="''document/figures/A.png''"]
       \<open> The A train \ldots \<close>

close_monitor*[figs1]  

declare[[free_class_in_monitor_checking = false]]

text\<open>Resulting trace of figs1 as ML antiquotation: \<close>
ML  \<open>@{trace_attribute figs1}\<close>
text\<open>Resulting trace of figs as text antiquotation:\<close>
text\<open>@{trace_attribute figs1}\<close>

text\<open>Test trace\_attribute term antiquotation:\<close>

term*\<open>map snd @{trace-attribute \<open>figs1\<close>}\<close>
value*\<open>map snd @{trace-attribute \<open>figs1\<close>}\<close>
term*\<open>map fst @{trace-attribute \<open>aaa\<close>}\<close>
value*\<open>map fst @{trace-attribute \<open>aaa\<close>}\<close>

definition example_expression where "example_expression \<equiv> \<lbrace>\<lfloor>''Conceptual.A''\<rfloor> || \<lfloor>''Conceptual.F''\<rfloor>\<rbrace>\<^sup>*"
value* \<open> DA.accepts (na2da (rexp2na example_expression)) (map fst @{trace-attribute \<open>aaa\<close>}) \<close>

definition word_test  :: "'a list \<Rightarrow> 'a rexp \<Rightarrow> bool" (infix "is-in" 60)
  where " w is-in rexp \<equiv>  DA.accepts (na2da (rexp2na rexp)) (w)"

value* \<open> (map fst @{trace-attribute \<open>aaa\<close>}) is-in example_expression \<close>


(*<*)
text\<open>Final Status:\<close>
print_doc_items
print_doc_classes 

end
(*>*)
