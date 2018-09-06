theory InnerSyntaxAntiquotations
  imports "../../ontologies/Conceptual"
begin

ML\<open>
val ({tab = x, ...},y,z)= DOF_core.get_data @{context};

Symtab.dest z;

\<close>

text*[xcv::F, u="@{file ''./examples/conceptual/Attributes.thy''}"]\<open>Lorem ipsum ...\<close>


end
