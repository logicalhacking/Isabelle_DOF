chapter \<open>An Outline of a CENELEC Ontology\<close>

text\<open> NOTE: An Ontology-Model of a certification standard such as CENELEC or Common Criteria 
identifies:
- notions (conceptual \emph{categories}) having \emph{instances}
  (similar to classes and objects),
- their subtype relation (eg., a "SRAC" is an "assumption"),
- their syntactical structure 
  (for the moment: defined by regular expressions describing the
   order of category instances in the overall document as a regular language)
 \<close> 

(*<<*)  
theory CENELEC_50128
  imports  "../Isa_COL"
begin
(*>>*) 

text\<open> Excerpt of the BE EN 50128:2011, page 22. \<close>

section\<open>Terms and Definitions\<close>

Definition*[assessment::concept]\<open>process of analysis to determine whether software, which may include 
process, documentation, system, subsystem hardware and/or software components, meets the specified 
requirements and to form  a judgement as to whether the software is fit for its intended purpose. 
Safety assessment is focused on but not limited to the safety properties of a system.\<close>

Definition*[assessor::concept, tag="''assessor''"]
\<open>entity that carries out an assessment\<close>

Definition*[cots::concept, tag="''commercial off-the-shelf (COTS) software''"]
\<open>software defined by market-driven need, commercially available and whose fitness for purpose 
has been demonstrated by a broad spectrum of commercial users\<close>


Definition*[component::concept]
\<open>a constituent part of software which has well-defined interfaces and behaviour 
with respect to the software architecture and design and fulfils the following 
criteria:
\<^enum> it is designed according to “Components” (see Table A.20);
\<^enum> it covers a specific subset of software requirements;
\<^enum> it is clearly identified and has an independent version inside the 
  configuration management system or is a part of a collection of components 
   (e. g. subsystems) which have an independent version
\<close>

Definition*[cmgr::concept, tag="''configuration manager''"]
\<open>entity that is responsible for implementing and carrying out the processes
for the configuration management of documents, software and related tools including 
\<^emph>\<open>change management\<close>\<close>

Definition*[customer::concept]
\<open>entity which purchases a railway control and protection system including the software\<close>

Definition*[designer::concept]
\<open>entity that analyses and transforms specified requirements into acceptable design solutions 
which have the required safety integrity level\<close>

Definition*[entity::concept]
\<open>person, group or organisation who fulfils a role as defined in this European Standard\<close>

declare_reference*[fault::concept]
Definition*[error::concept]
\<open>defect, mistake or inaccuracy which could result in failure or in a deviation 
from the intended performance or behaviour (cf @{concept (unchecked) \<open>fault\<close>}))\<close>

Definition*[fault::concept]
\<open>defect, mistake or inaccuracy which could result in failure or in a deviation 
from the intended performance or behaviour (cf @{concept \<open>error\<close>})\<close>

Definition*[failure::concept]
\<open>unacceptable difference between required and observed performance\<close>

Definition*[ft::concept, tag="''fault tolerance''"]
\<open>built-in capability of a system to provide continued correct provision of service as specified, 
in the presence of a limited number of hardware or software faults\<close>

Definition*[firmware::concept]
\<open>software stored in read-only memory or in semi-permanent storage such as flash memory, in a 
way that is functionally independent of applicative software\<close>

Definition*[gen_soft::concept,tag="''generic software''"]
\<open>software which can be used for a variety of installations purely by the provision of 
application-specific data and/or algorithms\<close>

Definition*[implementer::concept]
\<open>entity that transforms specified designs into their physical realisation\<close> 

Definition*[integration::concept]
\<open>process of assembling software and/or hardware items, according to the architectural and 
design specification, and testing the integrated unit\<close>

Definition*[integrator::concept]
\<open>entity that carries out software integration\<close>

Definition*[PES :: concept, tag="''pre-existing software''"]
\<open>software developed prior to the application currently in question, including COTS (commercial 
off-the shelf) and open source software\<close>

Definition*[OSS :: concept, tag="''open source software''"]
\<open>source code available to the general public with relaxed or non-existent copyright restrictions\<close>

Definition*[PLC::concept, tag="''programmable logic controller''"]
\<open>solid-state control system which has a user programmable memory for storage of instructions to 
implement specific functions\<close>

Definition*[PM::concept, tag="''project management''"]
\<open>administrative and/or technical conduct of a project, including safety aspects\<close>

Definition*[PGMGR::concept, tag="''project manager''"]
\<open>entity that carries out project management\<close>

Definition*[reliability::concept]
\<open>ability of an item to perform a required function under given conditions for a given period of time\<close>

Definition*[robustness::concept]
\<open>ability of an item to detect and handle abnormal situations\<close>

Definition*[RMGR::concept, tag="''requirements manager''"]
\<open>entity that carries out requirements management\<close>

Definition*[RMGMT::concept, tag="''requirements management''"]
\<open>the process of eliciting, documenting, analysing, prioritising and agreeing on requirements and 
then controlling change and communicating to relevant stakeholders. It is a continuous process 
throughout a project\<close>

Definition*[risk::concept]
\<open>combination of the rate of occurrence of accidents and incidents resulting in harm (caused by 
a hazard) and the degree of severity of that harm\<close>

Definition*[safety::concept]
\<open>freedom from unacceptable levels of risk of harm to people\<close>

Definition*[SA::concept, tag="''safety authority''"]
\<open>body responsible for certifying that safety related software or services comply with relevant 
statutory safety requirements\<close>

Definition*[SF::concept, tag="''safety function''"]
\<open>a function that implements a part or whole of a safety requirement\<close>

Definition*[SFRS::concept, tag= "''safety-related software''"]
\<open>software which performs safety functions\<close>

Definition*[software::concept]
\<open>intellectual creation comprising the programs, procedures, rules, data and any associated 
documentation pertaining to the operation of a system\<close>

Definition*[SB::concept, tag="''software baseline''"]
\<open>complete and consistent set of source code, executable files, configuration files, 
installation scripts and documentation that are needed for a software release. Information about 
compilers, operating systems, preexisting software and dependent tools is stored as part of the 
baseline. This will enable the organisation to software deployment
transferring, installing and activating a deliverable software baseline that has already been 
released and assessed
\<close>



Definition*[SWLC::concept, tag="''software life-cycle''"]
\<open>those activities occurring during a period of time that starts when
software is conceived and ends when the software is no longer available for use. The software life 
cycle typically includes a requirements phase, design phase,test phase, integration phase, 
deployment phase and a maintenance phase 3.1.35 software maintainability
capability of the software to be modified; to correct faults, improve to a different environment
\<close>

Definition*[SM::concept, tag="''software maintenance''"]
\<open> action, or set of actions, carried out on software after deployment functionality
performance or other attributes, or adapt it with the aim of enhancing or correcting its\<close>

Definition*[SOSIL::concept, tag="''software safety integrity level''"]
\<open>classification number which determines the techniques and measures that have to be applied to 
software NOTE Safety-related software has been classified into five safety integrity levels, where 
0 is the lowest and 4 the highest.\<close>

Definition*[supplier::concept]
\<open>entity that designs and builds a railway control and protection system including the software 
or parts thereof\<close>

Definition*[SYSIL::concept, tag="''system safety integrity level''"]
\<open>classification number which indicates the required degree of confidence that an integrated 
system comprising hardware and software will meet its specified safety requirements\<close>

Definition*[tester::concept]\<open>an entity that carries out testing\<close>

Definition*[testing::concept]
\<open>process of executing software under controlled conditions as to ascertain its behaviour and 
performance compared to the corresponding requirements specification\<close>

Definition*[TCT1::concept, tag="''tool class T1''"]
\<open>generates no outputs which can directly or indirectly contribute to the executable code 
(including data) of the software NOTE 11 examples include: a text editor or a requirement or 
design support tool with no automatic code generation capabilities; configuration control tools.\<close>

Definition*[TCT2::concept,tag="''tool class T2''"]
\<open>supports the test or verification of the design or executable code, where errors in the tool 
can fail to reveal defects but cannot directly create errors in the executable software
NOTE T2 examples include: a test harness generator; a test coverage measurement tool; a static 
analysis tool. reproduce defined versions and be the input for future releases at enhancements or 
at upgrade in the maintenance phase
\<close>

Definition*[TCT3::concept, tag="''tool class T3''"]
\<open>generates outputs which can directly or indirectly contribute to the executable code 
(including data) of the safety related system NOTE T3 examples include: a source code compiler, 
a data/algorithms compiler, a tool to change set-points during system operation; an optimising 
compiler where the relationship between the source code program and the generated object code is 
not obvious; a compiler that incorporates an executable run-time package into the executable code.
\<close>
Definition*[traceability::concept]
\<open>degree to which relationship can be established between two or more products of a development 
process, especially those having a predecessor/successor or master/subordinate relationship to one 
another\<close>

Definition*[validation::concept]
\<open>process of analysis followed by a judgment based on evidence to
documentation, software or application) fits the user needs,in particular with respect to safety 
and quality and determine whether an item (e.g. process, with emphasis on the suitability of its 
operation in accordance to its purpose in its intended environment\<close>

Definition*[validator::concept]
\<open>entity that is responsible for the validation\<close>

Definition*[verification::concept]
\<open>process of examination followed by a judgment based on evidence that output items (process,
documentation, software or application) of a specific development phase fulfils the requirements of 
that phase with respect to completeness, correctness and consistency.
NOTE Verification is mostly based on document reviews (design, implementation, test documents etc.).
\<close>

Definition*[verifier::concept]
\<open>entity that is responsible for one or more verification activities\<close>


datatype role =  PM  (* Program Manager *) 
              |  RQM (* Requirements Manager *)
              |  DES (* Designer *)
              |  IMP (* Implementer *)
              |  ASR (* Assessor *)
              |  Ne  (* Integrator *)
              |  TST (* Tester *)
              |  VER (* Verifier *)
              |  VAL (* Validator *)


datatype phase =  SR    (* Software Requirement      *) 
               |  SA    (* Software Architecture     *)
               |  SDES  (* Software Design           *)
               |  SCDES (* Software Component Design *)
               |  CInT  (* Component Implementation and Testing *)
               |  SI    (* Software Integration      *)
               |  SV    (* Software Validation       *)
               |  SD    (* Software Deployment       *)
               |  SM    (* Software Maintenance      *)

abbreviation software_requirement  :: "phase" where "software_requirement  \<equiv> SR"
abbreviation software_architecture :: "phase" where "software_architecture \<equiv> SA"
abbreviation software_design       :: "phase" where "software_design       \<equiv> SD"
abbreviation software_component_design:: "phase" where "software_component_design \<equiv> SCDES"
abbreviation component_implementation_and_testing :: "phase" 
                                             where "component_implementation_and_testing \<equiv> CInT"
abbreviation software_integration  :: "phase" where "software_integration \<equiv> SI"
abbreviation software_validation   :: "phase" where "software_validation  \<equiv> SV"
abbreviation software_deployment   :: "phase" where "software_deployment  \<equiv> SD"
abbreviation software_maintenance  :: "phase" where "software_maintenance \<equiv> SM"

term "SR"

doc_class objectives =
   long_name    :: "string option"
   is_concerned :: "role set"


section\<open> Requirements-Analysis related Categories \<close> 

doc_class requirement =
   long_name    :: "string option"
   is_concerned :: "role set"
  

doc_class requirement_analysis = 
   no :: "nat"
   accepts "\<lbrace>requirement\<rbrace>\<^sup>+"

                              
text\<open>The category @{emph \<open>hypothesis\<close>} is used for assumptions from the 
      foundational mathematical or physical domain, so for example: 
      \<^item>   the Mordell-Lang conjecture holds,   
      \<^item>   euklidian geometry is assumed, or
      \<^item>   Newtonian (non-relativistic) physics is assumed,
     Their acceptance is inherently outside the scope of the model
     and can only established inside certification process by
     authority argument.
\<close>
  
datatype hyp_type = physical | mathematical | computational | other


typ "CENELEC_50128.requirement"

doc_class hypothesis = requirement +
      hyp_type :: hyp_type <= physical  (* default *)

text\<open> The following sub-class of security related hypothesis might comprise, for example:
      \<^item>   @{term "P \<noteq> NP"},
      \<^item>   or the computational hardness  of certain functions 
          relevant for cryptography (like prime-factorization).\<close>

doc_class security_hyp = hypothesis +
      hyp_type :: hyp_type <= physical  (* default *)


text\<open>The category \<^emph>\<open>assumption\<close> is used for domain-specific assumptions. It has formal, semi-formal 
      and informal sub-categories. They have to be  tracked and discharged by appropriate 
      validation procedures within a certification process, by it by test or proof. \<close>

datatype ass_kind = informal | semiformal | formal
  
doc_class assumption = requirement +
     assumption_kind :: ass_kind <= informal 

text\<open> The category \<^emph>\<open>exported constraint\<close> (or \<^emph>\<open>ec\<close>  for short) is used for formal assumptions, ... \<close>

doc_class ec = assumption  +
     assumption_kind :: ass_kind <= (*default *) formal

text\<open> The category \<^emph>\<open>safety related application condition\<close> (or \<^emph>\<open>srac\<close> for short) is used  ... \<close>
                        
doc_class srac = ec  +
     assumption_kind :: ass_kind <= (*default *) formal

doc_class timing = ec  +
     assumption_kind :: ass_kind <= (*default *) formal

doc_class energy = ec  +
     assumption_kind :: ass_kind <= (*default *) formal

doc_class security = ec  +
     assumption_kind :: ass_kind <= (*default *) formal


section\<open> Design related Categories \<close>  

doc_class design_item = 
      description :: string
      
datatype design_kind = unit | module | protocol
      
doc_class interface =  design_item +
      kind :: design_kind
      

section\<open> Requirements-Analysis related Categories \<close>   

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
   accepts "test_specification ~~ \<lbrace>test_case~~test_result\<rbrace>\<^sup>+ ~~ \<lbrace>test_environment||test_tool\<rbrace>\<^sup>+ ~~
            \<lbrakk>test_requirement\<rbrakk>  ~~ test_adm_role"
   accepts " test_specification ~~ \<lbrace>test_case~~test_result\<rbrace>\<^sup>+ ~~ \<lbrace>test_environment||test_tool\<rbrace>\<^sup>+ ~~
            \<lbrakk>test_requirement \<rbrakk> ~~ test_adm_role"


  
section\<open> Testing and Validation \<close>

text\<open>Test : @{concept \<open>cots\<close>}\<close>


ML\<open>
DOF_core.name2doc_class_name @{theory} "requirement";
DOF_core.name2doc_class_name @{theory} "srac";
DOF_core.is_defined_cid_global "srac" @{theory};
DOF_core.is_defined_cid_global "ec" @{theory};
"XXXXXXXXXXXXXXXXX";
DOF_core.is_subclass @{context} "CENELEC_50128.ec" "CENELEC_50128.ec";
DOF_core.is_subclass @{context} "CENELEC_50128.srac" "CENELEC_50128.ec";
DOF_core.is_subclass @{context} "CENELEC_50128.ec"   "CENELEC_50128.srac";
DOF_core.is_subclass @{context} "CENELEC_50128.ec"   "CENELEC_50128.test_requirement";
"XXXXXXXXXXXXXXXXX";
val {docobj_tab={maxano, tab=ref_tab},docclass_tab=class_tab,...} = DOF_core.get_data @{context};
Symtab.dest ref_tab;
Symtab.dest class_tab;
\<close>


ML\<open>
"XXXXXXXXXXXXXXXXX";

DOF_core.get_attributes_local "srac" @{context};

@{term assumption_kind}
\<close> 


ML\<open>
DOF_core.name2doc_class_name @{theory} "requirement";
Syntax.parse_typ @{context} "requirement";
val Type(t,_) = Syntax.parse_typ @{context} "requirement" handle ERROR _ => dummyT;
Syntax.read_typ  @{context} "hypothesis" handle  _ => dummyT;
Proof_Context.init_global;
\<close>

end      
  