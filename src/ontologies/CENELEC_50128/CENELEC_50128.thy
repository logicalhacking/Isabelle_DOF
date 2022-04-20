(*************************************************************************
 * Copyright (C) 
 *               2019      The University of Exeter 
 *               2018-2019 The University of Paris-Saclay
 *               2018      The University of Sheffield
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

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
  imports  "../technical_report/technical_report"
begin

(* this is a hack and should go into an own ontology, providing thingsd like:
  - Assumption*
  - Hypothesis*
  - Definition*.  (Une redefinition de ce qui se passe dans tech-report, cible a semi-formal 
                         “Definitions of terminology” \<dots> )
  - Objective"
  - Claim* 
  - Requirement*
  
*) 
   

text\<open>We re-use the class @\<open>typ math_content\<close>, which provides also a framework for
semi-formal "math-alike" terminology, which we re-use by this definition.\<close>

doc_class semi_formal_content = math_content +
      status        :: status <= "semiformal" 
      mcc           :: math_content_class <= "terminology"

type_synonym sfc = semi_formal_content  

(*>>*)

declare[[ Definition_default_class="semi_formal_content"]]


text\<open> Excerpt of the BE EN 50128:2011, page 22. \<close>


section\<open>Terms and Definitions\<close>

Definition*[assessment,short_name="''assessment''"]
\<open>process of analysis to determine whether software, which may include 
process, documentation, system, subsystem hardware and/or software components, meets the specified 
requirements and to form  a judgement as to whether the software is fit for its intended purpose. 
Safety assessment is focused on but not limited to the safety properties of a system.\<close>

Definition*[assessor, short_name="''assessor''"]
\<open>entity that carries out an assessment\<close>

Definition*[COTS, short_name="''commercial off-the-shelf software''"]
\<open>software defined by market-driven need, commercially available and whose fitness for purpose 
has been demonstrated by a broad spectrum of commercial users\<close>


Definition*[component]
\<open>a constituent part of software which has well-defined interfaces and behaviour 
with respect to the software architecture and design and fulfils the following 
criteria:
\<^enum> it is designed according to “Components” (see Table A.20);
\<^enum> it covers a specific subset of software requirements;
\<^enum> it is clearly identified and has an independent version inside the 
  configuration management system or is a part of a collection of components 
   (e. g. subsystems) which have an independent version
\<close>
typ "sfc"

Definition*[CMGR, short_name="''configuration manager''"]
\<open>entity that is responsible for implementing and carrying out the processes
for the configuration management of documents, software and related tools including 
\<^emph>\<open>change management\<close>\<close>

Definition*[customer]
\<open>entity which purchases a railway control and protection system including the software\<close>

Definition*[designer]
\<open>entity that analyses and transforms specified requirements into acceptable design solutions 
which have the required safety integrity level\<close>

Definition*[entity]
\<open>person, group or organisation who fulfils a role as defined in this European Standard\<close>

declare_reference*[fault]
Definition*[error]
\<open>defect, mistake or inaccuracy which could result in failure or in a deviation 
from the intended performance or behaviour (cf. @{semi_formal_content (unchecked) \<open>fault\<close>}))\<close>

Definition*[fault]
\<open>defect, mistake or inaccuracy which could result in failure or in a deviation 
from the intended performance or behaviour (cf @{semi_formal_content \<open>error\<close>})\<close>

Definition*[failure]
\<open>unacceptable difference between required and observed performance\<close>

Definition*[FT, short_name="''fault tolerance''"]
\<open>built-in capability of a system to provide continued correct provision of service as specified, 
in the presence of a limited number of hardware or software faults\<close>

Definition*[firmware]
\<open>software stored in read-only memory or in semi-permanent storage such as flash memory, in a 
way that is functionally independent of applicative software\<close>

Definition*[GS,short_name="''generic software''"]
\<open>software which can be used for a variety of installations purely by the provision of 
application-specific data and/or algorithms\<close>

Definition*[implementer]
\<open>entity that transforms specified designs into their physical realisation\<close> 

Definition*[integration]
\<open>process of assembling software and/or hardware items, according to the architectural and 
design specification, and testing the integrated unit\<close>

Definition*[integrator]
\<open>entity that carries out software integration\<close>

Definition*[PES :: sfc, short_name="''pre-existing software''"]
\<open>software developed prior to the application currently in question, including COTS (commercial 
off-the shelf) and open source software\<close>

Definition*[OSS :: sfc, short_name="''open source software''"]
\<open>source code available to the general public with relaxed or non-existent copyright restrictions\<close>

Definition*[PLC, short_name="''programmable logic controller''"]
\<open>solid-state control system which has a user programmable memory for storage of instructions to 
implement specific functions\<close>

Definition*[PM, short_name="''project management''"]
\<open>administrative and/or technical conduct of a project, including safety aspects\<close>

Definition*[PGMGR, short_name="''project manager''"]
\<open>entity that carries out project management\<close>

Definition*[reliability]
\<open>ability of an item to perform a required function under given conditions for a given period of time\<close>

Definition*[robustness]
\<open>ability of an item to detect and handle abnormal situations\<close>

Definition*[RMGR, short_name="''requirements manager''"]
\<open>entity that carries out requirements management\<close>

Definition*[RMGMT, short_name="''requirements management''"]
\<open>the process of eliciting, documenting, analysing, prioritising and agreeing on requirements and 
then controlling change and communicating to relevant stakeholders. It is a continuous process 
throughout a project\<close>

Definition*[risk]
\<open>combination of the rate of occurrence of accidents and incidents resulting in harm (caused by 
a hazard) and the degree of severity of that harm\<close>

Definition*[safety]
\<open>freedom from unacceptable levels of risk of harm to people\<close>

Definition*[SA, short_name="''safety authority''"]
\<open>body responsible for certifying that safety related software or services comply with relevant 
statutory safety requirements\<close>

Definition*[SF, short_name="''safety function''"]
\<open>a function that implements a part or whole of a safety requirement\<close>

Definition*[SFRS, short_name= "''safety-related software''"]
\<open>software which performs safety functions\<close>

Definition*[software]
\<open>intellectual creation comprising the programs, procedures, rules, data and any associated 
documentation pertaining to the operation of a system\<close>

Definition*[SB, short_name="''software baseline''"]
\<open>complete and consistent set of source code, executable files, configuration files, 
installation scripts and documentation that are needed for a software release. Information about 
compilers, operating systems, preexisting software and dependent tools is stored as part of the 
baseline. This will enable the organisation to software deployment
transferring, installing and activating a deliverable software baseline that has already been 
released and assessed
\<close>



Definition*[SWLC, short_name="''software life-cycle''"]
\<open>those activities occurring during a period of time that starts when
software is conceived and ends when the software is no longer available for use. The software life 
cycle typically includes a requirements phase, design phase,test phase, integration phase, 
deployment phase and a maintenance phase 3.1.35 software maintainability
capability of the software to be modified; to correct faults, improve to a different environment
\<close>

Definition*[SM, short_name="''software maintenance''"]
\<open> action, or set of actions, carried out on software after deployment functionality
performance or other attributes, or adapt it with the aim of enhancing or correcting its\<close>

Definition*[SOSIL, short_name="''software safety integrity level''"]
\<open>classification number which determines the techniques and measures that have to be applied to 
software NOTE Safety-related software has been classified into five safety integrity levels, where 
0 is the lowest and 4 the highest.\<close>

Definition*[supplier]
\<open>entity that designs and builds a railway control and protection system including the software 
or parts thereof\<close>

Definition*[SYSIL, short_name="''system safety integrity level''"]
\<open>classification number which indicates the required degree of confidence that an integrated 
system comprising hardware and software will meet its specified safety requirements\<close>

Definition*[tester]\<open>an entity that carries out testing\<close>

Definition*[testing]
\<open>process of executing software under controlled conditions as to ascertain its behaviour and 
performance compared to the corresponding requirements specification\<close>

Definition*[TCT1, short_name="''tool class T1''"]
\<open>generates no outputs which can directly or indirectly contribute to the executable code 
(including data) of the software NOTE 11 examples include: a text editor or a requirement or 
design support tool with no automatic code generation capabilities; configuration control tools.\<close>

Definition*[TCT2,short_name="''tool class T2''"]
\<open>supports the test or verification of the design or executable code, where errors in the tool 
can fail to reveal defects but cannot directly create errors in the executable software
NOTE T2 examples include: a test harness generator; a test coverage measurement tool; a static 
analysis tool. reproduce defined versions and be the input for future releases at enhancements or 
at upgrade in the maintenance phase
\<close>

Definition*[TCT3, short_name="''tool class T3''"]
\<open>generates outputs which can directly or indirectly contribute to the executable code 
(including data) of the safety related system NOTE T3 examples include: a source code compiler, 
a data/algorithms compiler, a tool to change set-points during system operation; an optimising 
compiler where the relationship between the source code program and the generated object code is 
not obvious; a compiler that incorporates an executable run-time package into the executable code.
\<close>
Definition*[traceability, short_name="''traceability''"]
\<open>degree to which relationship can be established between two or more products of a development 
process, especially those having a predecessor/successor or master/subordinate relationship to one 
another\<close>

Definition*[validation, short_name="''validation''"]
\<open>process of analysis followed by a judgment based on evidence to
documentation, software or application) fits the user needs,in particular with respect to safety 
and quality and determine whether an item (e.g. process, with emphasis on the suitability of its 
operation in accordance to its purpose in its intended environment\<close>

Definition*[validator, short_name="''validator''"]
\<open>entity that is responsible for the validation\<close>

Definition*[verification, short_name="''verification''"]
\<open>process of examination followed by a judgment based on evidence that output items (process,
documentation, software or application) of a specific development phase fulfils the requirements of 
that phase with respect to completeness, correctness and consistency.
NOTE Verification is mostly based on document reviews (design, implementation, test documents etc.).
\<close>

Definition*[verifier, short_name="''verifier''"]
\<open>entity that is responsible for one or more verification activities\<close>

chapter\<open>Software Management and Organisation\<close>
text\<open>Representing chapter 5 in @{cite "bsi:50128:2014"}.\<close>

section\<open>Organization, Roles and Responsabilities\<close>
text\<open>see also section \<^emph>\<open>Software management and organization\<close>.\<close>

datatype role =  PM     \<comment> \<open>Program Manager\<close>
              |  RQM    \<comment> \<open>Requirements Manager\<close> 
              |  DES    \<comment> \<open>Designer\<close>
              |  IMP    \<comment> \<open>Implementer\<close> 
              |  ASR    \<comment> \<open>Assessor\<close> 
              |  INT    \<comment> \<open>Integrator\<close> 
              |  TST    \<comment> \<open>Tester\<close>
              |  VER    \<comment> \<open>Verifier\<close>
              |  VnV    \<comment> \<open>Verification and Validation\<close>
              |  VAL    \<comment> \<open>Validator\<close>



datatype phase = SYSDEV_ext \<comment> \<open> System Development Phase (external)\<close>  
               | SPl   \<comment> \<open>Software Planning\<close>
               | SR    \<comment> \<open>Software Requirement\<close> 
               | SA    \<comment> \<open>Software Architecture\<close>
               | SDES  \<comment> \<open>Software Design\<close>
               | SCDES \<comment> \<open>Software Component Design\<close> 
               | CInT  \<comment> \<open>Component Implementation and Testing\<close>
               | SI    \<comment> \<open>Software Integration\<close>
               | SV    \<comment> \<open>Software Validation\<close>
               | SD    \<comment> \<open>Software Deployment\<close>
               | SM    \<comment> \<open>Software Maintenance\<close>

abbreviation software_requirement      :: "phase" where "software_requirement  \<equiv> SR"
abbreviation software_architecture     :: "phase" where "software_architecture \<equiv> SA"
abbreviation software_design           :: "phase" where "software_design       \<equiv> SD"
abbreviation software_component_design :: "phase" where "software_component_design \<equiv> SCDES"
abbreviation component_implementation_and_testing :: "phase" 
                                                  where "component_implementation_and_testing \<equiv> CInT"
abbreviation software_integration      :: "phase" where "software_integration \<equiv> SI"
abbreviation software_validation       :: "phase" where "software_validation  \<equiv> SV"
abbreviation software_deployment       :: "phase" where "software_deployment  \<equiv> SD"
abbreviation software_maintenance      :: "phase" where "software_maintenance \<equiv> SM"

term "SR" (* meta-test *)


section\<open>Objectives, Conformance and Software Integrity Levels\<close>

datatype sil = SIL0 | SIL1 | SIL2 | SIL3 | SIL4

type_synonym safety_integration_level = sil


doc_class objectives =
   long_name    :: "string option"
   is_concerned :: "role set"


doc_class requirement = text_element +
   long_name    :: "string option"
   is_concerned :: "role set"
  
text\<open>The following class permits to represent common situations where a set of requirements 
decomposes a main requirement. The GSN notation favors this particular decomposition style.\<close>
doc_class sub_requirement = 
   decomposes ::  requirement
   relates_to :: "requirement set"

doc_class safety_requirement = requirement +
   formal_definition    :: "thm list"

                              
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
          relevant for cryptography (like prime-factorization).
      (* speculation bu, not 50128 *)\<close>

doc_class security_hyp = hypothesis +
      hyp_type :: hyp_type <= physical  (* default *)


doc_class FnI = requirement +
   is_concerned :: "role set" <= "UNIV"    
   type_synonym functions_and_interfaces = FnI


text\<open>The category \<^emph>\<open>assumption\<close> is used for domain-specific assumptions. It has formal, semi-formal 
      and informal sub-categories. They have to be  tracked and discharged by appropriate 
      validation procedures within a certification process, by it by test or proof. \<close>

datatype ass_kind = informal | semiformal | formal
  
doc_class assumption = requirement +
     assumption_kind :: ass_kind <= informal 

doc_class AC = assumption +
   is_concerned :: "role set" <= "UNIV" 

type_synonym application_conditions = AC


text\<open> The category \<^emph>\<open>exported constraint\<close> (or \<^emph>\<open>EC\<close>  for short) is used for formal application 
conditions; They represent in particular \<^emph>\<open>derived constraints\<close>, i.e. constraints that arrive
as side-conditions during refinement proofs or implementation decisions and must be tracked.\<close>

doc_class EC = AC  +
     assumption_kind :: ass_kind <= (*default *) formal
     type_synonym exported_constraint = EC

text\<open> The category \<^emph>\<open>safety related application condition\<close> (or \<^emph>\<open>SRAC\<close> for short) is used
for exported constraints assuring in judgements safety requirements of the system. \<close>
                        
doc_class SRAC = EC  +
     assumption_kind :: ass_kind <= (*default *) formal
     formal_repr     :: "thm list"
     type_synonym safety_related_application_condition = SRAC


doc_class CoAS = requirement +
   is_concerned :: "role set" <= "UNIV" 
   type_synonym configuration_or_architecture_of_system = CoAS

doc_class HtbC = requirement +
   is_concerned :: "role set" <= "UNIV" 
   type_synonym hazard_to_be_controlled = HtbC

doc_class SIR = requirement +
   is_concerned :: "role set" <= "UNIV" 
   type_synonym safety_integrity_requirement = SIR

text\<open>The following class is a bit unclear about usage and seems to be in 
sfcual mismatch with @{typ objectives}: \<close>
doc_class SILA = requirement +
   is_concerned :: "role set" <= "UNIV" 
   alloc        :: "sil" <= "SIL0" 
   type_synonym allocation_of_SIL = SILA

doc_class TC = requirement +
   is_concerned :: "role set" <= "UNIV" 
   type_synonym timing_constraint = TC


section\<open>Personal Competence\<close>

text\<open>pp. 20 MORE TO COME\<close>

section\<open>Lifecycle Issues and Documentation\<close>

text\<open>Figure 3 in Chapter 5: Illustrative Development Lifecycle 1\<close>

text\<open>Global Overview\<close>

figure*[fig3::figure, relative_width="100", 
 src="''examples/CENELEC_50128/mini_odo/document/figures/CENELEC-Fig.3-docStructure.png''"]
\<open>Illustrative Development Lifecycle 1\<close>
                                     
section\<open>Software Assurance related Entities and Concepts\<close>


text\<open>subcategories are :\<close>

text\<open>Table A.13:  \<close>

datatype dyn_ana_kind = 
           boundary_analysis     (* -- Test Case Execution from Boundary Analysis *)
         | error_guessing        (* -- Test Case Execution from Error Guessing *)
         | error_seeding         (* -- Test Case Execution from Error Seeding *)
         | performance_modeling  (* -- Performance Modeling *)
         | equivalence_class_test(* -- Equivalence Classes and Input Partition Testing*)
         | structure_based_test  (* -- Structure-Based Testing *)

text\<open>Table A.14:  \<close>

datatype fun_test_kind = 
           cause_consequence_diagram (* -- Test Case Execution from Cause Consequence Diagrams *)
         | prototyping               (* -- Prototyping / Animation *)
         | bounadry_value_analysis   (* -- Boundary Value Analysis *) 
         | equivalence_class_test    (* -- Equivalence Classes and Input Partition Testing*)
         | process_simulation        (* -- Process Simulation *) 
 

text\<open>Table A.5: Verification and Testing\<close>

datatype test_coverage_criterion =  
             allpathk  nat nat     (* depth, test_coverage_degree *)
             | mcdc  nat           (* depth, test_coverage_degree *)
             | exhaustive
             | dnf_E_d  string nat (* equivalence class testing *)
             | other string

datatype vnt_technique = 
               formal_proof "thm list"
             | stat_analysis 
             | dyn_analysis dyn_ana_kind 
             | metrics 
             | traceability
             | sw_error_effect_analysis
             | test_coverage_for_code test_coverage_criterion
             | functional_testing fun_test_kind test_coverage_criterion
             | perf_testing test_coverage_criterion
             | interface_testing test_coverage_criterion
             | model_based_testing  test_coverage_criterion (* 'modeling' unclear *)  


type_synonym verification_and_testing_technique = vnt_technique


text\<open>The objective of software verification is to examine and arrive at a \<^emph>\<open>judgement\<close> based on 
\<^emph>\<open>evidence\<close> that  output items (process, documentation, software or application) of a specific 
development phase fulfil the requirements and plans with respect to completeness, correctness 
and consistency. \<close>
datatype status = complete | in_complete | reject | unclear | unknown 

doc_class judgement =    
   refers_to       :: requirement
   evidence        :: "vnt_technique list"
   status          :: status
   is_concerned    :: "role set" <= "{VER,ASR,VAL}" 

section\<open> Design and Test Documents \<close> 

doc_class cenelec_document = text_element +
   phase        :: "phase"
   level        :: "int option" <= "Some(0)" 
   written_by   :: role                       \<comment> \<open>Annex C Table C.1 \<close>
   fst_check    :: role                       \<comment> \<open>Annex C Table C.1\<close>
   snd_check    :: role                       \<comment> \<open>Annex C Table C.1\<close>
   is_concerned :: "role set" <= "UNIV" 
   invariant must_be_chapter :: "text_element.level \<sigma> = Some(0)" 
   invariant three_eyes_prcpl:: "  written_by \<sigma> \<noteq> fst_check \<sigma> 
                                 \<and> written_by \<sigma> \<noteq> snd_check \<sigma>"
text\<open>see Fig.3.\<close>


doc_class SYSREQS = cenelec_document + 
   phase        :: "phase"  <= "SYSDEV_ext" 
   accepts      "\<lbrace>objectives||requirement||cenelec_document\<rbrace>\<^sup>+ "       
   type_synonym system_requirements_specification = SYSREQS

doc_class SYSSREQS = cenelec_document + 
   phase        :: "phase"  <= "SYSDEV_ext" 
   type_synonym system_safety_requirements_specification = SYSSREQS

doc_class SYSAD = cenelec_document + 
   phase        :: "phase"  <= "SYSDEV_ext" 
   type_synonym system_architecture_description = SYSAD

doc_class SYSS_pl = cenelec_document + 
   phase        :: "phase"  <= "SPl" 
   type_synonym system_safety_plan = SYSS_pl

doc_class SYS_VnV_pl = cenelec_document + 
   phase        :: "phase"  <= "SPl" 
   type_synonym system_VnV_plan = SYS_VnV_pl

doc_class SWRS = cenelec_document + 
   phase        :: "phase"  <= "SD" 
   type_synonym software_requirements_specification = SWRS

doc_class SWRVR = cenelec_document + 
   phase        :: "phase"  <= "SD" 
   type_synonym software_requirements_verification_report = SWRVR


doc_class SWTS = cenelec_document + 
   phase        :: "phase"  <= "SD" 
   type_synonym software_test_specification = SWTS

   
doc_class SWAS = cenelec_document + 
   phase        :: "phase"  <= "SD" 
   type_synonym software_architecture_specification = SWAS

doc_class SWDS = cenelec_document + 
   phase        :: "phase"  <= "SD" 
   type_synonym software_design_specification = SWDS

doc_class SWIS_E =
   \<comment> \<open>input - output of an operation; alternatives could be channels or public global variables ...\<close>
   op_name           :: "string"
   op_args_ty        :: "(string \<times> typ) list \<times> typ"
   raises_exn        :: "(string \<times> typ) list"         \<comment> \<open>exn name and value\<close>
   pre_cond          :: "(string \<times> thm) list" <= "[]" \<comment> \<open>labels and predicates\<close>
   post_cond         :: "(string \<times> thm) list" <= "[]" \<comment> \<open>labels and predicates\<close>
   boundary_pre_cond :: "thm list" <= "[]"
   type_synonym software_interface_specification_element = SWIS_E


doc_class SWIS = cenelec_document + 
   phase        :: "phase"  <= "SCDES" 
   written_by   :: "role"   <= "DES"
   fst_check    :: "role"   <= "VER"
   snd_check    :: "role"   <= "VAL"
   components   :: "SWIS_E list"
   type_synonym software_interface_specification = SWIS

doc_class SWITS = cenelec_document + 
   phase        :: "phase"  <= "SD" 
   type_synonym software_integration_test_specification = SWITS

doc_class SWHITS = cenelec_document + 
   phase        :: "phase"  <= "SD" 
   type_synonym software_hardware_integration_test_specification = SWHITS

doc_class SWADVR = cenelec_document + 
   phase        :: "phase"  <= "SD" 
   type_synonym software_architecture_and_design_verification_report = SWADVR

doc_class SWCDS = cenelec_document + 
   phase        :: "phase"  <= "SD" 
   type_synonym software_component_design_specification = SWCDS

doc_class SWCTS = cenelec_document + 
   phase        :: "phase"  <= "SD" 
   type_synonym software_component_test_specification = SWCTS

doc_class SWCDVR = cenelec_document + 
   phase        :: "phase"  <= "SD" 
   type_synonym software_component_design_verification_report = SWCDVR


doc_class SWSCD = cenelec_document + 
   phase        :: "phase"  <= "SD" 
   type_synonym software_source_code_and_documentation = SWSCD

doc_class SWCTR = cenelec_document + 
   phase        :: "phase"  <= "SD" 
   type_synonym software_component_test_report = SWCTR

doc_class SWSCVR = cenelec_document + 
   phase        :: "phase"  <= "SD" 
   type_synonym software_source_code_verification_report = SWSCVR

doc_class SWHAITR = cenelec_document +
   phase        :: "phase"  <= "SD" 
   type_synonym software_hardware_integration_test_report = SWHAITR

doc_class SWIVR = cenelec_document +
   phase        :: "phase"  <= "SD" 
   type_synonym software_integration_verification_report = SWIVR

doc_class SWTR_global = cenelec_document + 
   phase        :: "phase"  <= "SD" 
   type_synonym overall_software_test_report = SWTR_global

doc_class SWVALR = cenelec_document +
   phase        :: "phase"  <= "SD" 
   type_synonym software_validation_report = SWVALR

doc_class SWDD = cenelec_document + 
   phase        :: "phase"  <= "SD" 
   type_synonym software_deployment_documents = SWDD

doc_class SWMD = cenelec_document + 
   phase        :: "phase"  <= "SD" 
   type_synonym software_maintenance_documents = SWMD

 
section\<open> Software Assurance \<close>
\<comment> \<open>MORE TO COME\<close>

subsection\<open> Software Testing \<close>
text\<open>Objective: 
The objective of software testing, as performed by the Tester and/or Integrator, 
is to ascertain the behaviour or performance of software against the corresponding test 
specification to the extent achievable by the selected test coverage.
\<close>

text\<open>Outputs:
\<^enum> @{typ overall_software_test_report}
\<^enum> @{typ software_test_specification} Overall Software Test Specification
\<^enum> Overall Software Test Report
\<^enum> Software Integration Test Specification
\<^enum> Software Integration Test Report
\<^enum> Software/Hardware Integration Test Specification
\<^enum> Software/Hardware Integration Test Report
\<^enum> Software Component Test Specification
\<^enum> Software Component Test Report
\<close>

subsection\<open> Software Verification \<close>
text\<open>Objective:
The objective of software verification is to examine and arrive at a judgement based on evidence 
that output items (process, documentation, software or application) of a specific development 
phase fulfil the requirements and plans with respect to completeness, correctness and consistency. 
These activities are managed by the @{semi_formal_content \<open>verifier\<close>}.
\<close>

text\<open>Outputs:
\<^enum> Software Verification Plan
\<^enum> Software Verification Report(s)
\<^enum> Software Quality Assurance Verification Report
\<close>

subsection\<open> Software Validation  \<close>
text\<open>Objective:
\<^enum>The objective of software validation is to demonstrate that the processes and their outputs are 
such that the software is of the defined software safety integrity level, fulfils the software 
requirements and is fit for its intended application. This activity is performed by the Validator.
\<^enum>The main validation activities are to demonstrate by analysis and/or testing that all the software
requirements are specified, implemented, tested and fulfilled as required by the applicable SIL, 
and to evaluate the safety criticality of all anomalies and non-conformities based on the results 
of reviews, analyses and tests.
\<close>
text\<open>Output documents:
\<^enum> Software Validation Plan
\<^enum> Software Validation Report
\<^enum> Software Validation Verification Report
\<close>

subsection\<open> Software Assessment \<close> (* other word for : formal evaluation. *)
text\<open>Objective:
\<^enum>To evaluate that the lifecycle processes and their outputs are such that the software is of the 
defined software safety integrity levels 1-4 andis fit for its intended application.
\<^enum> For SIL 0 software, requirements of this standard shall be fulfilled but where a certificate stating 
compliance with EN ISO 9001 is available, no assessment will be required.
\<close>

subsection\<open> Software Quality Assurance  \<close>
text\<open>Objectives: To identify, monitor and control all those activities, both technical and 
managerial, which are necessary to ensure that the software achieves the quality required. 
This is necessary to provide the required qualitative defence against systematic faults and 
to ensure that an audit trail can be established to allow
verification and validation activities to be undertaken effectively.\<close>
(* So : pretty much META *)





(* DEATH ZONE FROM HERE ... >>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>>> *)


section\<open> Design related Categories \<close>  

doc_class design_item = 
             description :: string
      
datatype  design_kind = unit | module | protocol
      
doc_class interface =  design_item +
             kind :: design_kind
      

section\<open> Requirements-Analysis related Categories \<close>   

doc_class test_item =
             nn :: "string option"
    
doc_class test_specification = test_item +
             short_goal :: string
      
doc_class test_case = test_item +
             descr :: string
          
doc_class test_result = test_item +
             verdict :: bool
             remarks :: string
             covvrit :: test_coverage_criterion

datatype  test_environment_kind = hardware_in_the_loop ("hil") 
                                | simulated_hardware_in_the_loop ("shil") 
  
doc_class test_environment = test_item +
             descr :: string
             kind  :: test_environment_kind <= shil

doc_class test_tool = test_item +
             descr :: string

doc_class test_requirement = test_item +
             descr :: string

doc_class test_adm_role = test_item +
             name :: string

doc_class test_documentation =    (* OUTDATED ? *)
             no :: "nat"
             accepts "test_specification ~~ 
                      \<lbrace>test_case~~test_result\<rbrace>\<^sup>+ ~~ 
                      \<lbrace>test_environment||test_tool\<rbrace>\<^sup>+ ~~
                      \<lbrakk>test_requirement\<rbrakk>  ~~ 
                      test_adm_role"


section\<open>Global Documentation Structure\<close>

doc_class global_documentation_structure = text_element +
   level :: "int option" <= "Some(-1::int)"  \<comment> \<open>document must be a chapter\<close>
   accepts "SYSREQS      ~~                  \<comment> \<open>system_requirements_specification\<close>
            SYSSREQS     ~~                  \<comment> \<open>system_safety_requirements_specification\<close> 
            SYSAD        ~~                  \<comment> \<open>system_architecture description\<close>
            SYSS_pl      ~~                  \<comment> \<open>system safety plan\<close> 
            (SWRS || SWTS)  "                \<comment> \<open>software requirements specification OR
                                                 overall software test specification\<close> 
(* MORE TO COME : *)

section\<open> META : Testing and Validation \<close>

text\<open>Test : @{semi_formal_content \<open>COTS\<close>}\<close>

ML
\<open> DOF_core.read_cid_global @{theory} "requirement";
  DOF_core.read_cid_global @{theory} "SRAC";
  DOF_core.is_defined_cid_global "SRAC" @{theory};
  DOF_core.is_defined_cid_global "EC" @{theory}; \<close>

ML
\<open> DOF_core.is_subclass @{context} "CENELEC_50128.EC"   "CENELEC_50128.EC";
  DOF_core.is_subclass @{context} "CENELEC_50128.SRAC" "CENELEC_50128.EC";
  DOF_core.is_subclass @{context} "CENELEC_50128.EC"   "CENELEC_50128.SRAC";
  DOF_core.is_subclass @{context} "CENELEC_50128.EC"   "CENELEC_50128.test_requirement"; \<close>

ML
\<open> val {docobj_tab={maxano, tab=ref_tab},docclass_tab=class_tab,...} = DOF_core.get_data @{context};
  Symtab.dest ref_tab;
  Symtab.dest class_tab; \<close>

ML
\<open> val internal_data_of_SRAC_definition = DOF_core.get_attributes_local "SRAC" @{context} \<close> 

ML
\<open> DOF_core.read_cid_global         @{theory}  "requirement";
  Syntax.parse_typ                 @{context} "requirement";
  val Type(t,_) = Syntax.parse_typ @{context} "requirement" handle ERROR _ => dummyT; 
  Syntax.read_typ                  @{context} "hypothesis"  handle  _ => dummyT;
  Proof_Context.init_global; \<close>

end