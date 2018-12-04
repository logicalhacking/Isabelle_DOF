chapter \<open>The Document Ontology Common Library for the Isabelle Ontology Framework\<close>

text\<open> Offering 
\<^item> ...
\<^item> 
\<^item> LaTeX support. \<close> 
  
  
theory Isa_COL   
  imports  Isa_DOF  
begin
  
   
section\<open> Library of Standard Text Ontology \<close>

datatype placement = pl_h | pl_t | pl_b | pl_ht | pl_hb   
doc_class figure   = 
   relative_width   :: "int" (* percent of textwidth *)    
   src              :: "string"
   placement        :: placement 
   spawn_columns    :: bool <= True 

doc_class side_by_side_figure = figure +
   anchor           :: "string"
   caption          :: "string"
   relative_width2  :: "int" (* percent of textwidth *)    
   src2             :: "string"
   anchor2          :: "string"
   caption2         :: "string"


doc_class figure_group = 
   (*  trace :: "doc_class rexp list" <= "[]" automatically generated since monitor clause *)
   anchor           :: "string"
   caption          :: "string"
   rejects             figure_group   (* this forbids recursive figure-groups *)
   accepts             "\<lbrace>figure\<rbrace>\<^sup>+"



(* dito the future table *)

(* dito the future monitor: table - block *)





section\<open>Tests\<close>

ML\<open>@{term "side_by_side_figure"};
@{typ "doc_class rexp"}; 
DOF_core.SPY;
\<close>


end
