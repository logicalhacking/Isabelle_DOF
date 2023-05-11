theory 
  COL_Test
imports 
  "Isabelle_DOF_Unit_Tests_document"
begin


print_doc_items
print_doc_classes

section\<open>General Heading COL Elements\<close> 

chapter*[S1::"chapter"]\<open>Chapter\<close>
text*[S1'::"chapter"]\<open>Chapter\<close>

section*[S2::"section"]\<open>Section\<close>
text*[S2'::"section"]\<open>Section\<close>

subsection*[S3::"subsection"]\<open>Subsection\<close>
text*[S3'::"subsection"]\<open>Subsection\<close>

subsubsection*[S4::"subsubsection"]\<open>Subsubsection\<close>
text*[S4'::"subsubsection"]\<open>Subsubsection\<close>

paragraph*[S5::"paragraph"]\<open>PAragraph\<close>
text*[S5'::"paragraph"]\<open>Paragraph\<close>


section\<open>General Figure COL Elements\<close> 

figure*[fig1_test::figure,spawn_columns=False,relative_width="95",src="''figures/A''"]
       \<open> This is the label text  \<^term>\<open>\<sigma>\<^sub>i+2\<close> \<close>  

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
      src2="''figures/B''"]\<open>The global caption\<close>

text\<open>check @{side_by_side_figure sbsfig1} cmp to @{side_by_side_figure sbsfig2}
     \autoref{Asub1} vs. \autoref{Asub2}
     \autoref{fig:Asub1} vs. \autoref{fig:Asub2}
    \<close>

(* And a side-chick ... *)

text*[inlinefig::float, 
      caption="\<open>The Caption.\<close>"]
\<open>@{theory_text [display, margin = 5] \<open>lemma A :: "a \<longrightarrow> b"\<close>}\<close>

text*[fffff::float]\<open> @{fig_content   [display] (scale = 80, width=80, caption=\<open>this is \<^term>\<open>\<sigma>\<^sub>i+2\<close> \<close>) 
                      \<open>figures/A.png\<close>}\<close>


(*<*)
text*[inlinegraph::float, 
      caption="\<open>Another \<sigma>\<^sub>i+2 Caption.\<close>"]
     \<open>@{fig_content [display] (scale = 80, width=80, caption=\<open>This is \<^term>\<open>\<sigma>\<^sub>i+2\<close> \<close>) 
               \<open>figures/A.png\<close>}\<close>
(*>*)



(*<*)
end
(*>*)
