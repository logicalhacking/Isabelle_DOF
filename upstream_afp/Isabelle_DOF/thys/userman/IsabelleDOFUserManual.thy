(*<*)
theory "IsabelleDOFUserManual"
  imports "C3_DocumentStructure"
begin
close_monitor*[this]
check_doc_global
text\<open>Resulting trace in \<^verbatim>\<open>doc_item\<close> ''this'': \<close>
ML\<open>@{trace_attribute this}\<close>

 
end
(*>*) 


