theory Attributes
  imports "../../ontologies/Conceptual"
begin


text*[dfgdfg::B, y = "[''sdf'']"]\<open> sdfsdfs sdfsdf sdfsdf @{thm refl}}\<close>

text\<open> @{docitem_ref \<open>dfgdfg\<close>} }\<close>

print_doc_classes

print_doc_items

ML\<open>  

val ({tab = x, ...},y)= DOF_core.get_data @{context};
Symtab.dest x;
Symtab.dest y;
\<close>
term "A.x (undefined\<lparr>A.x := 3\<rparr>)"
term "B.x ((undefined::C)\<lparr>B.y := [''sdf'']\<rparr>)"
term "C.z ((undefined::C)\<lparr>B.y := [''sdf'']\<rparr>)"

ML\<open>
val SOME {def_occurrence = "Conceptual.A", long_name = "Conceptual.A.x", typ = t} 
    = DOF_core.get_attribute_info  "Conceptual.A" "x" @{theory};
DOF_core.get_attribute_info  "Conceptual.B" "x" @{theory};
DOF_core.get_attribute_info  "Conceptual.B" "y" @{theory};
DOF_core.get_attribute_info  "Conceptual.C" "x" @{theory};
val SOME {def_occurrence = "Conceptual.C", long_name = "Conceptual.B.y", typ = t'}
    = DOF_core.get_attribute_info  "Conceptual.C" "y" @{theory};
    (* this is the situation where an attribute is defined in C, but due to inheritance
       from B, where it is firstly declared which results in a different long_name. *)
DOF_core.get_attribute_info  "Conceptual.C" "z" @{theory};
\<close>


ML\<open>
DOF_core.get_default_local "Conceptual.A" "x" @{context};

DOF_core.get_default_local "Conceptual.B" "x" @{context};
DOF_core.get_default_local "Conceptual.B" "y" @{context};

DOF_core.get_default_local "Conceptual.C" "x" @{context};
DOF_core.get_default_local "Conceptual.C" "y" @{context};
DOF_core.get_default_local "Conceptual.C" "z" @{context};
\<close>

ML\<open>
DOF_core.get_value_local "sdf" @{context};
DOF_core.get_value_local "sdfg" @{context};
DOF_core.get_value_local "xxxy" @{context};
DOF_core.get_value_local "dfgdfg" @{context};
\<close>

ML\<open>val s =  map HOLogic.dest_string (HOLogic.dest_list @{docitem_attr y::dfgdfg}) \<close>

end