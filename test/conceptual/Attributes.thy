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
DOF_core.get_attribute_long_name  "Conceptual.A" "x" @{theory};
DOF_core.get_attribute_long_name  "Conceptual.B" "x" @{theory};
DOF_core.get_attribute_long_name  "Conceptual.B" "y" @{theory};
DOF_core.get_attribute_long_name  "Conceptual.C" "x" @{theory};
DOF_core.get_attribute_long_name  "Conceptual.C" "y" @{theory};
DOF_core.get_attribute_long_name  "Conceptual.C" "z" @{theory};
(* this is only partially correct : the attribute longnames should be:
   Conceptual.A.x

   Conceptual.B.x
   Conceptual.B.y

   Conceptual.B.x
   Conceptual.B.y    
   Conceptual.C.z 
*) 
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

ML\<open>
val Type X = @{typ "A"}
\<close>

ML\<open>val t =  @{docitem_attr y::dfgdfg} \<close>

end