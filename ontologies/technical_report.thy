section{* An example ontology for a scholarly paper*}

theory technical_report
   imports "scholarly_paper"
begin

doc_class table_of_content =
   level       :: int <= 3

doc_class "chapter" = text_section +
   style :: string 
  
doc_class report = 
   style_id :: string                <= "''LNCS''"
   version  :: "(int \<times> int \<times> int)"  <= "(0,0,0)"
   where "(title       ~~ 
           \<lbrakk>subtitle\<rbrakk>   ~~
           \<lbrace>author\<rbrace>\<^sup>+   ~~ 
           abstract     ~~
           chapter      ~~
           introduction ~~ 
           \<lbrace>technical || example\<rbrace>\<^sup>+ ~~ 
           conclusion   ~~  
           bibliography)"

end

