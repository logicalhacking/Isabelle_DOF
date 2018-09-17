theory InnerSyntaxAntiquotations
  imports "../../ontologies/Conceptual"
begin

ML\<open> val ({tab = x, ...},y,z)= DOF_core.get_data @{context};
    Symtab.dest z; \<close>

lemma murks : "T = {ert,dfg}" sorry

text*[xcv::F, u="@{file ''./examples/conceptual/Attributes.thy''}"]\<open>Lorem ipsum ...\<close>

text*[xcv1::A, x=5]\<open>Lorem ipsum ...\<close>
text*[xcv2::C, g="@{thm ''HOL.refl''}"]\<open>Lorem ipsum ...\<close>
text*[xcv3::A, x=7]\<open>Lorem ipsum ...\<close>
text*[xcv4::F, r="[@{thm ''HOL.refl''}, 
                   @{thm ''InnerSyntaxAntiquotations.murks''}]", 
               b="{(@{docitem ''xcv1''},@{docitem ''xcv2''})}",  
               s="[@{typ ''int list''}]"]\<open>Lorem ipsum ...\<close>

text\<open>... and here we add a relation between @{docitem \<open>xcv3\<close>} and @{docitem \<open>xcv2\<close>} 
in the relation \verb+b+ of @{docitem_ref \<open>xcv4\<close>} \<close>
update_instance*[xcv4::F, b+="{(@{docitem ''xcv3''},@{docitem ''xcv2''})}"]

ML\<open>
@{docitem_attr b::xcv4}
\<close>

end
