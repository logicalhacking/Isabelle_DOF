chapter \<open>An Outline of a CENELEC Ontology\<close>

text{* NOTE: An Ontology-Model of a certification standard such as CENELEC or
Common Criteria identifies:
- notions (conceptual \emph{categories}) having \emph{instances}
  (similar to classes and objects),
- their subtype relation (eg., a "SRAC" is an "assumption"),
- their syntactical structure 
  (for the moment: defined by regular expressions describing the
   order of category instances in the overall document as a regular language)
 *}  

(*<<*)  
theory CENELEC_50126
  imports "../Isa_DOF"
begin
(*>>*) 


text{* Excerpt of the BE EN 50128:2011 *}

section {* Requirements-Analysis related Categories *}  

doc_class requirement =
   long_name :: "string option"
  

doc_class requirement_analysis = 
   no :: "nat"
   where "\<lbrace>requirement\<rbrace>\<^sup>+"

                              
text{*The category @{emph \<open>hypothesis\<close>} is used for assumptions from the 
      foundational mathematical or physical domain, so for example: 
      \<^item>   the Mordell-Lang conjecture holds,   
      \<^item>   euklidian geometry is assumed, or
      \<^item>   Newtonian (non-relativistic) physics is assumed,
      \<^item>   @{term "P \<noteq> NP"},
      \<^item>   or the computational hardness  of certain functions 
          relevant for cryptography (like prime-factorization).
     Their acceptance is inherently outside the scope of the model
     and can only established inside certification process by
     authority argument.
*}
  
datatype hyp_type = physical | mathematical | computational | other


typ "CENELEC_50126.requirement"


doc_class hypothesis = requirement +
      hyp_type :: hyp_type <= physical  (* default *)
  
text{*The category @{emph \<open>assumption\<close>} is used for domain-specific assumptions. 
      It has formal, semi-formal and informal sub-categories. They have to be 
      tracked and discharged by appropriate validation procedures within a 
      certification process, by it by test or proof. *}

datatype ass_kind = informal | semiformal | formal
  
doc_class assumption = requirement +
     assumption_kind :: ass_kind <= informal 

text{*The category @{emph \<open>exported constraint\<close>} (or @{emph \<open>ec\<close>} for short) 
      is used for formal assumptions, that arise during the analysis,
      design or implementation and have to be tracked till the final
      evaluation target, and discharged by appropriate validation procedures 
      within the certification process, by it by test or proof. *}

doc_class ec = assumption  +
     assumption_kind :: ass_kind <= (*default *) formal

text{*The category @{emph \<open>safety related application condition\<close>} (or @{emph \<open>srac\<close>} 
      for short) is used for @{typ ec}'s that establish safety properties
      of the evaluation target. Their track-ability throughout the certification
      is therefore particularly critical. *}
                        
doc_class srac = ec  +
     assumption_kind :: ass_kind <= (*default *) formal

section {* Design related Categories *}  

doc_class design_item = 
      description :: string
      
datatype design_kind = unit | module | protocol
      
doc_class interface =  design_item +
      kind :: design_kind
      

section {* Requirements-Analysis related Categories *}  

doc_class test_item =
      nn :: "string option"

text{* subcategories are : *}
  
datatype test_kind = blackbox | whitebox | greybox | fuzz | pertubation
  
datatype test_coverage_criterion =  
             allpathk  nat nat     (* depth, test_coverage_degree *)
             | mcdc  nat           (* depth, test_coverage_degree *)
             | exhaustive
             | dnf_E_d  string nat (* equivalence class testing *)
             | other string
    
doc_class test_specification = test_item +
          short_goal :: string
      
doc_class test_case = test_item +
          kind  :: test_kind
          descr :: string

          
          
doc_class test_result = test_item +
             verdict :: bool
             remarks :: string
             covvrit :: test_coverage_criterion

datatype   test_environment_kind = hardware_in_the_loop ("hil") 
                                 | simulated_hardware_in_the_loop ("shil") 
  
doc_class  test_environment = test_item +
             descr :: string
             kind  :: test_environment_kind <= shil

doc_class  test_tool = test_item +
             descr :: string

doc_class  test_requirement = test_item +
             descr :: string

doc_class  test_adm_role = test_item +
             name :: string

doc_class test_documentation = 
   no :: "nat"
   where "test_specification ~~ \<lbrace>test_case~~test_result\<rbrace>\<^sup>+ ~~ \<lbrace>test_environment||test_tool\<rbrace>\<^sup>+ ~~
          \<lbrakk>test_requirement\<rbrakk>  ~~ test_adm_role"
   where " test_specification ~~ \<lbrace>test_case~~test_result\<rbrace>\<^sup>+ ~~ \<lbrace>test_environment||test_tool\<rbrace>\<^sup>+ ~~
          \<lbrakk>test_requirement \<rbrakk> ~~ test_adm_role"


  
section{* Testing and Validation *}


ML{*
DOF_core.name2doc_class_name @{theory} "requirement";
DOF_core.name2doc_class_name @{theory} "srac";
DOF_core.is_defined_cid_global "srac" @{theory};
DOF_core.is_defined_cid_global "ec" @{theory};
"XXXXXXXXXXXXXXXXX";
DOF_core.is_subclass @{context} "CENELEC_50126.ec" "CENELEC_50126.ec";
DOF_core.is_subclass @{context} "CENELEC_50126.srac" "CENELEC_50126.ec";
DOF_core.is_subclass @{context} "CENELEC_50126.ec"   "CENELEC_50126.srac";
DOF_core.is_subclass @{context} "CENELEC_50126.ec"   "CENELEC_50126.test_requirement";
"XXXXXXXXXXXXXXXXX";
val ({maxano, tab=ref_tab},class_tab) = DOF_core.get_data @{context};
Symtab.dest ref_tab;
Symtab.dest class_tab;
*}
  
ML{*
"XXXXXXXXXXXXXXXXX";

DOF_core.get_attributes_local "srac" @{context};

@{term assumption_kind}
*}  


ML{*
DOF_core.name2doc_class_name @{theory} "requirement";
Syntax.parse_typ @{context} "requirement";
val Type(t,_) = Syntax.parse_typ @{context} "requirement" handle ERROR _ => dummyT;
Syntax.read_typ  @{context} "hypothesis" handle  _ => dummyT;
Proof_Context.init_global;
*}


end      
  