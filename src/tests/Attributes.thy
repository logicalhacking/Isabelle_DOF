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
  "../ontologies/Conceptual/Conceptual"
begin

section\<open>Elementary Creation of Doc-items and Access of their Attibutes\<close>

text\<open>Current status:\<close>
print_doc_classes
print_doc_items

(* this corresponds to low-level accesses : *)
ML\<open>  
val {docobj_tab={tab = docitem_tab, ...},docclass_tab, ISA_transformer_tab, monitor_tab,...} 
    = DOF_core.get_data @{context};
Symtab.dest docitem_tab;
Symtab.dest docclass_tab;
\<close>


ML\<open>
fun fac x = if x = 0 then 1 else x * (fac(x -1));
fac 3;
\<close>

ML\<open>
open Thm;
\<close>



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
   val @{typ "D"} = ODL_Command_Parser.cid_2_cidType "Conceptual.D" @{theory};
   val @{typ "E"} = ODL_Command_Parser.cid_2_cidType "Conceptual.E" @{theory};
  \<close>

text*[dfgdfg2::C, z = "None"]\<open> Lorem ipsum ... @{thm refl} \<close> 

text*[omega::E, x = "''def''"]\<open> Lorem ipsum ... @{thm refl} \<close> 

text\<open> As mentioned in @{docitem_ref \<open>dfgdfg\<close>} \<close>

text\<open>Here is a simulation what happens on the level of the (HOL)-term representation:\<close>
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
DOF_core.get_value_local "xxxy"  @{context};
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

update_instance*[omega::E, x+="''inition''"]

ML\<open> val s = HOLogic.dest_string ( @{docitem_attribute x::omega}) \<close>
                            
update_instance*[omega::E, y+="[''defini'',''tion'']"]

update_instance*[omega::E, y+="[''en'']"]

ML\<open> val s =  map HOLogic.dest_string (HOLogic.dest_list @{docitem_attribute y::omega}); \<close>

subsection\<open> Example text antiquotation:\<close>
text\<open> @{docitem_attribute omega::y}  \<close>


section\<open>Simulation of a Monitor\<close>

open_monitor*[figs1::figure_group, 
              caption="''Sample ''"]  

figure*[fig_A::figure, spawn_columns=False,
        relative_width="90",
        src="''figures/A.png''"]
       \<open> The A train \ldots \<close>

figure*[fig_B::figure, 
        spawn_columns=False,relative_width="90",
        src="''figures/B.png''"]
       \<open> The B train \ldots \<close>  

close_monitor*[figs1]  

text\<open>Resulting trace of figs1 as ML antiquotation: \<close>
ML  \<open>@{trace_attribute figs1}\<close>
text\<open>Resulting trace of figs as text antiquotation:\<close>
text\<open>@{trace_attribute figs1}\<close>

(*<*)
text\<open>Final Status:\<close>
print_doc_items
print_doc_classes 

end
(*>*)
