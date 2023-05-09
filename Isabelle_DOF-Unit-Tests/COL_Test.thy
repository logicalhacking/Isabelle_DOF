theory 
  COL_Test
imports 
  "Isabelle_DOF_Unit_Tests_document"
begin


print_doc_items
print_doc_classes


figure*[fig1_test::figure,spawn_columns=False,relative_width="95",src="''figures/A''"]
       \<open> This is the label text \<close>  

text*[fig2_test::figure, spawn_columns=False, relative_width="95",src="''figures/A''"
]\<open> This is the label text\<close>

text\<open>check @{figure fig1_test} cmp to @{figure fig2_test}\<close>

side_by_side_figure*["sbsfig1"::side_by_side_figure,
                      anchor="''Asub1''",
                      caption="''First caption.''",
                      relative_width="48",
                      src="''figures/A''",
                      anchor2="''Asub2''",
                      caption2="''Second caption.''",
                      relative_width2="47",
                      src2="''figures/B''"]\<open> Exploring text elements. \<close>


text*["sbsfig2"::side_by_side_figure,
      anchor="''fig:Asub1''",
      caption="''First caption.''",
      relative_width="48",
      src="''figures/A''",
      anchor2="''fig:Asub2''",
      caption2="''Second caption.''",
      relative_width2="47",
      src2="''figures/B''"]\<open>The final caption\<close>

text\<open>check @{side_by_side_figure sbsfig1} cmp to @{side_by_side_figure sbsfig2}
     \autoref{Asub1} vs. \autoref{Asub2}
     \autoref{fig:Asub1} vs. \autoref{fig:Asub2}
    \<close>

(*<*)
end
(*>*)
