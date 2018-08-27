theory Attributes
  imports "../../ontologies/Conceptual"
begin

section\<open>Elementary Creation of DocItems and Access of their Attibutes\<close>

text\<open>Current status:\<close>
print_doc_classes
print_doc_items

(* corresponds to low-level accesses : *)
ML\<open>  
val ({tab = x, ...},y)= DOF_core.get_data @{context};
Symtab.dest x;
"==============================================";
Symtab.dest y;
\<close>

text*[dfgdfg::B, Conceptual.B.x ="''f''", y = "[''sdf'']"]\<open> sdfsdfs sdfsdf sdfsdf @{thm refl} \<close> 

typ "C"
typ "D"
ML\<open>val Type("Conceptual.B.B_ext",[Type("Conceptual.C.C_ext",t)]) = @{typ "C"};
   val @{typ "D"} = ODL_Command_Parser.cid_2_cidType "Conceptual.D" @{theory};
   val @{typ "E"}= ODL_Command_Parser.cid_2_cidType "Conceptual.E" @{theory};
  \<close>

text*[dfgdfg2::C, z = "None"]\<open> sdfsdfs sdfsdf sdfsdf @{thm refl} \<close> 

text*[omega::E, x = "''def''"]\<open> sdfsdfs sdfsdf sdfsdf @{thm refl} \<close> 

text\<open> @{docitem_ref \<open>dfgdfg\<close>} \<close>


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
DOF_core.get_value_local "sdf" @{context};
DOF_core.get_value_local "sdfg" @{context};
DOF_core.get_value_local "xxxy" @{context};
DOF_core.get_value_local "dfgdfg" @{context};
DOF_core.get_value_local "omega" @{context};
\<close>

text\<open>A not too trivial test: default y -> [].
     At creation :  x -> "f", y -> "sdf".
     The latter wins at access time.
     Then @{term "t"}: creation of a multi inheritance object omega,
     triple updates, the last one wins.\<close>
ML\<open>val s =  map HOLogic.dest_string (HOLogic.dest_list @{docitem_attr y::dfgdfg});
   val t =   HOLogic.dest_string (@{docitem_attr x::omega});  \<close>




section\<open>Mutation of Attibutes in DocItems\<close>

ML\<open> val  Const ("Groups.zero_class.zero", @{typ "int"}) =  @{docitem_attr a2::omega} \<close>

update_instance*[omega::E, a2+="1"]

ML\<open> val Const ("Groups.one_class.one", @{typ "int"})=  @{docitem_attr a2::omega} \<close>

update_instance*[omega::E, a2+="6"]

ML\<open>  @{docitem_attr a2::omega} \<close>
ML\<open>  HOLogic.dest_number @{docitem_attr a2::omega} \<close>

update_instance*[omega::E, x+="''inition''"]

ML\<open> val s =   HOLogic.dest_string ( @{docitem_attr x::omega}) \<close>
                            
update_instance*[omega::E, y+="[''defini'',''tion'']"]

update_instance*[omega::E, y+="[''en'']"]

ML\<open>val s =  map HOLogic.dest_string (HOLogic.dest_list @{docitem_attr y::omega});
\<close>


section\<open>Simulation of a Monitor\<close>

open_monitor*[fig1::figure_group, 
              anchor="''fig-demo''", 
              caption="''Sample ''"]  


figure*[fig_A::figure, spawn_columns=False,relative_width="''90''",
        src="''figures/A.png''"]
       \<open> The A train \ldots \<close>
update_instance*[fig1::figure_group, trace+="[figure]"]


figure*[fig_B::figure, spawn_columns=False,relative_width="''90''",
        src="''figures/B.png''"]
       \<open> The B train \ldots \<close>  
update_instance*[fig1::figure_group, trace+="[figure]"]

close_monitor*[fig1]  

ML\<open> map (fn Const(s,_) => s) (HOLogic.dest_list @{docitem_attr trace::fig1}) \<close>


end