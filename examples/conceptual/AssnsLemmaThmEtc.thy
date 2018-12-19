theory AssnsLemmaThmEtc
  imports "../../ontologies/Conceptual"  "../../ontologies/math_paper"
begin

section\<open>Elementary Creation of Doc-items and Access of their Attibutes\<close>

text\<open>Current status:\<close>
print_doc_classes
print_doc_items



section\<open>Definitions, Lemmas, Theorems, Assertions\<close>
(* auxilliary *)
ML\<open>fun assert_list_dest X = map HOLogic.dest_string 
                                (map (fn Const ("Isa_DOF.ISA_term", _) $ s => s )  
                                     (HOLogic.dest_list X))\<close>


text*[aa::F]\<open>Our definition of the HOL-Logic has the following properties:\<close>
assert*[aa::F] "True"

ML\<open>assert_list_dest @{docitem_attribute property :: aa}\<close>
assert*[aa::F] "True & True" (* small pb: unicodes crashes here ... *)
ML\<open> assert_list_dest @{docitem_attribute property :: aa}\<close>

text\<open>An example for the ontology specification character of the short-cuts such as 
@{command  "assert*"}: in the following, we use the same notation referring to a completely
different class. "F" and "assertion" have only in common that they posses the attribute
\<^verbatim>\<open>property\<close>: \<close>

text*[aaa::assertion]\<open>Our definition of the integers has the following properties:\<close>
assert*[aaa::assertion] "3 < (4::int)"
assert*[aaa::assertion] "0 < (4::int)"


end
(*>*)
