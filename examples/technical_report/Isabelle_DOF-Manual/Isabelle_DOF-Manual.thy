(*<*)
theory "Isabelle_DOF-Manual"
  imports "05_Implementation"
begin
close_monitor*[this]
check_doc_global
text\<open>Resulting trace in doc\_item ''this'': \<close>
ML\<open>@{trace_attribute this}\<close>
end
(*>*) 
  
