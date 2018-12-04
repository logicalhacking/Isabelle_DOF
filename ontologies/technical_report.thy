section{* An example ontology for a scholarly paper*}

theory technical_report
   imports "scholarly_paper"
begin

(* for reports paper: invariant: level \<ge> -1 *)

doc_class table_of_contents =
   bookmark_depth :: int <= 3
   depth          :: int <= 3

doc_class front_matter = 
   front_matter_style :: string    (* TODO Achim :::: *)

doc_class index =
   kind  :: "doc_class" 
   level :: "int option"

doc_class report = 
   style_id :: string                <= "''LNCS''"
   version  :: "(int \<times> int \<times> int)"  <= "(0,0,0)"
   accepts "(title                 ~~ 
           \<lbrakk>subtitle\<rbrakk>              ~~
           \<lbrace>author\<rbrace>\<^sup>+               ~~ 
           \<lbrakk>front_matter\<rbrakk>          ~~
           abstract                ~~
           \<lbrakk>table_of_contents\<rbrakk>     ~~
           \<lbrace>introduction\<rbrace>\<^sup>+         ~~ 
           \<lbrace>technical || example\<rbrace>\<^sup>+ ~~ 
           \<lbrace>conclusion\<rbrace>\<^sup>+           ~~  
           \<lbrace>index\<rbrace>\<^sup>+  ~~  
           bibliography)"

ML\<open>
\<close>

end

