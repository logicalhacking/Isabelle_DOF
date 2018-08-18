theory Attributes
  imports "../../ontologies/Conceptual"
begin

text* [dfgdfg::B, y = "[''sdf'']"]\<open> sdfsdfs sdfsdf sdfsdf @{thm refl}}\<close>

term "B"
text\<open> @{docitem_ref \<open>dfgdfg\<close>} }\<close>

declare  [[ML_print_depth = 20]]
ML\<open>  
val ({tab = x, ...},y)= DOF_core.get_data @{context};
writeln "================";
Symtab.dest x;
writeln "================";
Symtab.dest y;
\<close>

ML\<open>val t =  @{docitem_attr y::dfgdfg} \<close>

end