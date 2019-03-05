theory AssnsLemmaThmEtc
  imports "../../ontologies/Conceptual"  "../../ontologies/math_paper"
begin

section\<open>Elementary Creation of Doc-items and Access of their Attibutes\<close>

text\<open>Current status:\<close>
print_doc_classes
print_doc_items



section\<open>Definitions, Lemmas, Theorems, Assertions\<close>


text*[aa::F, property = "[@{termrepr ''True''}]"]\<open>Our definition of the HOL-Logic has the following properties:\<close>
assert*[aa::F] "True"

ML\<open>  val (Const _ $ t $ t') =  @{docitem_attribute property :: aa}\<close>

ML\<open>  ISA_core.property_list_dest  @{docitem_attribute property :: aa}\<close>

assert*[aa::F] "True \<longrightarrow> True" (* small pb: unicodes crashes here ... *)

ML\<open>
Syntax.read_term_global @{theory} "[@{term '' 'True @<longrightarrow> True' ''}]";

@{term "[@{term '' ' True @<longrightarrow> True ' ''}]"} 
\<close>

ML\<open> ISA_core.property_list_dest @{docitem_attribute property :: aa}\<close>

text\<open>An example for the ontology specification character of the short-cuts such as 
@{command  "assert*"}: in the following, we use the same notation referring to a completely
different class. "F" and "assertion" have only in common that they posses the attribute
\<^verbatim>\<open>property\<close>: \<close>

text\<open>Creation just like that: \<close>
assert*[aaa::assertion] "3 < (4::int)"
assert*[aaa::assertion] "0 < (4::int)"


end
(*>*)
