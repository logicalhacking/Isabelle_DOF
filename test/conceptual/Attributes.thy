theory Attributes
  imports "../../ontologies/Conceptual"
begin

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

text*[omega::E, x = "''g''"]\<open> sdfsdfs sdfsdf sdfsdf @{thm refl} \<close> 

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
   val t =   HOLogic.dest_string (@{docitem_attr x::omega});
 \<close>

(* separate checking and term construction ?*)


ML\<open>val t = @{term "Conceptual.B.y_update"}\<close>
declare [[ML_print_depth=30]]

ML\<open>

\<close>
ML\<open>
val cid_long = "Conceptual.B"
val attr_name = "dfgdfg"
val thy = @{theory};

val S = DOF_core.get_attribute_defaults cid_long thy;
fun conv (na, _ (* ty *), term) = (Binding.name_of na, Binding.pos_of na, "=", term);
val (tt, ty, n) = ODL_Command_Parser.calc_update_term thy cid_long (map conv S) 
            (the(DOF_core.get_value_global attr_name thy));
\<close>




end