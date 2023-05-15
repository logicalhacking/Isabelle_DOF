theory Very_Deep_DOF
  imports "Isabelle_DOF-Proofs.Very_Deep_Interpretation"

begin

(* tests *)
term "@{typ  ''int => int''}"  
term "@{term ''Bound 0''}"  
term "@{thm  ''refl''}"  
term "@{docitem  ''<doc_ref>''}"
ML\<open>   @{term "@{docitem  ''<doc_ref>''}"}\<close>

term "@{typ  \<open>int \<Rightarrow> int\<close>}"  
term "@{term \<open>\<forall>x. P x \<longrightarrow> Q\<close>}"  
term "@{thm  \<open>refl\<close>}"  
term "@{docitem  \<open>doc_ref\<close>}"
ML\<open>   @{term "@{docitem  \<open>doc_ref\<close>}"}\<close>

end