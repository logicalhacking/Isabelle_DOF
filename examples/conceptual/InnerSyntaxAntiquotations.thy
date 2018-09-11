theory InnerSyntaxAntiquotations
  imports "../../ontologies/Conceptual"
begin

ML\<open>
val ({tab = x, ...},y,z)= DOF_core.get_data @{context};

Symtab.dest z;

\<close>

lemma murks : "T = {ert,dfg}" sorry

text*[xcv::F, u="@{file ''./examples/conceptual/Attributes.thy''}"]\<open>Lorem ipsum ...\<close>

text*[xcv1::F, r="[@{thm ''HOL.refl''}, 
                   @{thm ''InnerSyntaxAntiquotations.murks''}]", 
               b="{(@{docitem ''xcv''},@{docitem ''xcv''})}",   (* lamentable ! No typecheck.*)
               s="[@{typ ''int list''}]"]\<open>Lorem ipsum ...\<close>


end
