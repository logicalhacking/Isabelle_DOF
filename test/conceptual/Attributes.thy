theory Attributes
  imports "../../ontologies/Conceptual"
begin

text* [dfgdfg::B, y = "[''sdf'']"]\<open> sdfsdfs sdfsdf sdfsdf @{thm refl}}\<close>

term "B"
text\<open> @{docitem_ref \<open>dfgdfg\<close>} }\<close>

print_doc_classes

print_doc_items

ML\<open>  

val ({tab = x, ...},y)= DOF_core.get_data @{context};
writeln "================";

Symtab.dest y;
\<close>

ML\<open>val t =  @{docitem_attr y::dfgdfg} \<close>

end