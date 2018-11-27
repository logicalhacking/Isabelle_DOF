section{* An example ontology for a scholarly paper*}

theory technical_report
   imports "scholarly_paper"
begin

doc_class table_of_contents =
   depth       :: int <= 3

doc_class front_matter = 
   style :: string 

doc_class "chapter" = text_section +
   style :: string 
  
doc_class report = 
   style_id :: string                <= "''LNCS''"
   version  :: "(int \<times> int \<times> int)"  <= "(0,0,0)"
   accepts "(title       ~~ 
           \<lbrakk>subtitle\<rbrakk>   ~~
           \<lbrace>author\<rbrace>\<^sup>+   ~~ 
           \<lbrakk>front_matter\<rbrakk>  ~~
           abstract     ~~
           \<lbrakk>table_of_contents\<rbrakk>  ~~
           introduction ~~ 
           \<lbrace>technical || example\<rbrace>\<^sup>+ ~~ 
           conclusion   ~~  
           \<lbrakk>table_of_contents\<rbrakk>  ~~
           bibliography)"

end

