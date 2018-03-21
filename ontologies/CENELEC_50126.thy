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
  
theory CENELEC_50126
  imports "../Isa_DOF"
begin

text{* Excerpt of the BE EN 50128:2011 *}

section {* Requirements-Analysis related Categories *}  

doc_class requirement =
   long_name :: "string option"
  

doc_class requirement_analysis = 
   no :: "nat"
   where "requirement_item +"

                              
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
      evaluation target,and discharged by appropriate validation procedures 
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
   where "(test_specification.((test_case.test_result)+.(test_environment|test_tool))+.
          [test_requirement].test_adm_role"
   where "(test_specification.((test_case.test_result)+.(test_environment|test_tool))+.
          [test_requirement].test_adm_role"






section{* Example *}

text*[ass122::srac] {* The overall sampling frequence of the odometer
subsystem is therefore 14 khz, which includes sampling, computing and
result communication times... *}
  
text*[t10::test_result] {* This is a meta-test. This could be an ML-command
that governs the external test-execution via, eg., a makefile or specific calls
to a test-environment or test-engine *}


text \<open> As established by @{docref \<open>t10\<close>}, the 
       assumption @{docref \<open>ass122\<close>} is validated. \<close>

                               
section{* Provisory Setup *}

(* Hack: This should be generated automatically: *)
ML{*
val _ = Theory.setup
        ((DocAttrParser.control_antiquotation @{binding srac}     
                                              (DOF_core.name2doc_class_name @{theory} "srac")
                                              {strict_checking=true}  
                                              "\\autoref{" "}" ) #>
         (DocAttrParser.control_antiquotation @{binding ec}
                                              (DOF_core.name2doc_class_name @{theory} "ec")
                                              {strict_checking=true} 
                                              "\\autoref{" "}")#>
         (DocAttrParser.control_antiquotation @{binding test_specification}
                                              (DOF_core.name2doc_class_name @{theory} "test_specification")
                                              {strict_checking=true}   
                                              "\\label{" "}"))

*}




section{* Testing and Validation *}


ML{*
DOF_core.name2doc_class_name @{theory} "requirement";
DOF_core.name2doc_class_name @{theory} "srac";
DOF_core.is_defined_cid_global "srac" @{theory};
DOF_core.is_defined_cid_global "ec" @{theory};

DOF_core.is_subclass @{context} "CENELEC_50126.srac" "CENELEC_50126.ec";
DOF_core.is_subclass @{context} "CENELEC_50126.ec"   "CENELEC_50126.srac";

val ({maxano, tab},tab2) = DOF_core.get_data @{context};
Symtab.dest tab;
Symtab.dest tab2;


*}  


ML{*
DOF_core.name2doc_class_name @{theory} "requirement";
Syntax.parse_typ @{context} "requirement";
val Type(t,_) = Syntax.parse_typ @{context} "requirement" handle ERROR _ => dummyT;
Syntax.read_typ  @{context} "hypothesis" handle  _ => dummyT;
Proof_Context.init_global;
*}


end      
  