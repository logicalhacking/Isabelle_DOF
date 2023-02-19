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
- notions (conceptual \<^emph>\<open>categories\<close>) having \<^emph>\<open>instances\<close>
  (similar to classes and objects),
- their \<^emph>\<open>subtype\<close> relation (eg., a "SRAC" is an "assumption"),
- their syntactical structure 
  (for the moment: defined by regular expressions describing the
   order of category instances in the overall document as a regular language)
 \<close> 

(*<<*)  
theory CENELEC_50128
  imports  "Isabelle_DOF.technical_report"
begin

define_ontology "DOF-CENELEC_50128.sty"

(* this is a hack and should go into an own ontology, providing thingsd like:
  - Assumption*
  - Hypothesis*
  - Definition*.  (Une redefinition de ce qui se passe dans tech-report, cible a semi-formal 
                         “Definitions of terminology” \<dots> )
  - Objective"
  - Claim* 
  - Requirement*
  
*) 
   

text\<open>We re-use the class \<^typ>\<open>math_content\<close>, which provides also a framework for
semi-formal "math-alike" terminology, which we re-use by this definition.\<close>

doc_class semi_formal_content = math_content +
      status        :: status <= "semiformal" 
      mcc           :: math_content_class 



type_synonym sfc = semi_formal_content  

doc_class cenelec_term = semi_formal_content + 
      mcc          :: math_content_class <= "terminology"


text\<open> in the following, all \<^theory_text>\<open>Definition*\<close> statements are interpreted as 
     \<^doc_class>\<open>cenelec_term\<close>s, i.e. semi-formal teminological definitions.\<close>

(*
ML\<open>
val typ_abbrev = Scan.lift
\<close>

ML\<open>
Parse.position: ( Token.T list -> 'a *  Token.T list) -> ('a * Position.T) parser;
Scan.lift(Parse.position Args.name) ; 
Args.name_position;
Proof_Context.read_typ_abbrev;

 Args.typ_abbrev : Context.generic * Token.T list ->  typ  * (Context.generic * Token.T list) ;

 Proof_Context.read_typ_abbrev;

(Args.typ_abbrev >> (fn Type(ss,_) =>  ss
                      | _ => error "Undefined Class Id"))
                 

\<close>
ML\<open>

fun context_position_parser parse_con (ctxt, toks) = 
     let val pos = case toks of 
                    a :: _ => Token.pos_of a 
                  | _ => @{here}             \<comment> \<open>a real hack !\<close>
         val (res, (ctxt', toks')) = parse_con (ctxt, toks)
     in  ((res,pos),(ctxt', toks')) end

val parse_cid = (context_position_parser Args.typ_abbrev)
          >> (fn (Type(ss,_),pos) =>  (pos,ss)
                |( _,pos) => ISA_core.err "Undefined Class Id" pos);


val parse_cid' = Term_Style.parse -- parse_cid

fun pretty_cid_style ctxt (style,(pos,cid)) = 
    (*reconversion to term in order to haave access to term print options like: short_names etc...) *)
          Document_Output.pretty_term ctxt ((AttributeAccess.compute_cid_repr ctxt cid pos));

val _ = Theory.setup (AttributeAccess.basic_entity \<^binding>\<open>Onto_class\<close> parse_cid' pretty_cid_style) 

\<close>

text\<open> \<^Onto_class>\<open>cenelec_term\<close> \<close>

*)

declare[[ Definition_default_class="cenelec_term"]]
(*>>*)


text\<open> Excerpt of the BE EN 50128:2011, page 22. \<close>

section\<open>Terms and Definitions\<close>

Definition*[assessment,short_name="''assessment''"]
\<open>process of analysis to determine whether software, which may include 
process, documentation, system, subsystem hardware and/or software components, meets the specified 
requirements and to form  a judgement as to whether the software is fit for its intended purpose. 
Safety assessment is focused on but not limited to the safety properties of a system.\<close>

Definition*[assessor, short_name="''assessor''"]
\<open>entity that carries out an assessment.\<close>

Definition*[COTS, short_name="''commercial off-the-shelf software''"]
\<open>software defined by market-driven need, commercially available and whose fitness for purpose 
has been demonstrated by a broad spectrum of commercial users.\<close>


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
\<^emph>\<open>change management\<close>.\<close>

Definition*[customer]
\<open>entity which purchases a railway control and protection system including the software.\<close>

Definition*[designer]
\<open>entity that analyses and transforms specified requirements into acceptable design solutions 
which have the required safety integrity level.\<close>

Definition*[entity]
\<open>person, group or organisation who fulfils a role as defined in this European Standard.\<close>

declare_reference*[fault::cenelec_term]
Definition*[error]
\<open>defect, mistake or inaccuracy which could result in failure or in a deviation 
from the intended performance or behaviour (cf. @{cenelec_term (unchecked) \<open>fault\<close>}).\<close>

Definition*[fault]
\<open>defect, mistake or inaccuracy which could result in failure or in a deviation 
from the intended performance or behaviour (cf @{cenelec_term \<open>error\<close>}).\<close>

Definition*[failure]
\<open>unacceptable difference between required and observed performance.\<close>

Definition*[FT, short_name="''fault tolerance''"]
\<open>built-in capability of a system to provide continued correct provision of service as specified, 
in the presence of a limited number of hardware or software faults.\<close>

Definition*[firmware]
\<open>software stored in read-only memory or in semi-permanent storage such as flash memory, in a 
way that is functionally independent of applicative software.\<close>

Definition*[GS,short_name="''generic software''"]
\<open>software which can be used for a variety of installations purely by the provision of 
application-specific data and/or algorithms.\<close>

Definition*[implementer]
\<open>entity that transforms specified designs into their physical realisation.\<close> 

Definition*[integration]
\<open>process of assembling software and/or hardware items, according to the architectural and 
design specification, and testing the integrated unit.\<close>

Definition*[integrator]
\<open>entity that carries out software integration.\<close>

Definition*[PES, short_name="''pre-existing software''"]
\<open>software developed prior to the application currently in question, including COTS (commercial 
off-the shelf) and open source software.\<close>

Definition*[OS, short_name="''open source software''"]
\<open>source code available to the general public with relaxed or non-existent copyright restrictions.\<close>

Definition*[PLC, short_name="''programmable logic controller''"]
\<open>solid-state control system which has a user programmable memory for storage of instructions to 
implement specific functions.\<close>

Definition*[PM, short_name="''project management''"]
\<open>administrative and/or technical conduct of a project, including safety aspects.\<close>

Definition*[PMGR, short_name="''project manager''"]
\<open>entity that carries out \<^cenelec_term>\<open>PM\<close>.\<close>

Definition*[reliability]
\<open>ability of an item to perform a required function under given conditions for a given period of time\<close>

Definition*[robustness]
\<open>ability of an item to detect and handle abnormal situations\<close>

Definition*[RM, short_name="''requirements management''"]
\<open>the process of eliciting, documenting, analysing, prioritising and agreeing on requirements and 
then controlling change and communicating to relevant stakeholders. It is a continuous process 
throughout a project\<close>

Definition*[RMGR, short_name="''requirements manager''"]
\<open>entity that carries out \<^cenelec_term>\<open>RM\<close>.\<close>

Definition*[risk]
\<open>combination of the rate of occurrence of accidents and incidents resulting in harm (caused by 
a hazard) and the degree of severity of that harm.\<close>

Definition*[safety]
\<open>freedom from unacceptable levels of risk of harm to people.\<close>

Definition*[SA, short_name="''safety authority''"]
\<open>body responsible for certifying that safety related software or services comply with relevant 
statutory safety requirements.\<close>

Definition*[SF, short_name="''safety function''"]
\<open>a function that implements a part or whole of a safety requirement.\<close>

Definition*[SFRS, short_name= "''safety-related software''"]
\<open>software which performs safety functions.\<close>

Definition*[software]
\<open>intellectual creation comprising the programs, procedures, rules, data and any associated 
documentation pertaining to the operation of a system.\<close>

Definition*[SB, short_name="''software baseline''"]
\<open>complete and consistent set of source code, executable files, configuration files, 
installation scripts and documentation that are needed for a software release. Information about 
compilers, operating systems, preexisting software and dependent tools is stored as part of the 
baseline. This will enable the organisation to reproduce defined versions and be the input
for future releases at enhancements or at upgrade in the maintenance phase.\<close>

Definition*[SD, short_name="''software deployment''"]
\<open>transferring, installing and activating a deliverable software baseline that has already been 
released and assessed.\<close>


Definition*[SWLC, short_name="''software life-cycle''"]
\<open>those activities occurring during a period of time that starts when
software is conceived and ends when the software is no longer available for use. The software life 
cycle typically includes a requirements phase, design phase, test phase, integration phase, 
deployment phase and a maintenance phase.\<close>

Definition*[SWMA, short_name="''software maintainability''"]
\<open>capability of the software to be modified; to correct faults,
improve performance or other attributes, or adapt it to a different environment\<close>

Definition*[SM, short_name="''software maintenance''"]
\<open> action, or set of actions, carried out on software after deployment functionality
performance or other attributes, or adapt it with the aim of enhancing or correcting its behaviour.\<close>

Definition*[SOSIL, short_name="''software safety integrity level''"]
\<open>classification number which determines the techniques and measures that have to be applied to 
software.

NOTE: Safety-related software has been classified into five safety integrity levels, where 
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
(including data) of the software
NOTE: T1 examples include: a text editor or a requirement or 
design support tool with no automatic code generation capabilities; configuration control tools.\<close>

Definition*[TCT2,short_name="''tool class T2''"]
\<open>supports the test or verification of the design or executable code, where errors in the tool 
can fail to reveal defects but cannot directly create errors in the executable software
NOTE: T2 examples include: a test harness generator; a test coverage measurement tool; a static 
analysis tool.\<close>

Definition*[TCT3, short_name="''tool class T3''"]
\<open>generates outputs which can directly or indirectly contribute to the executable code 
(including data) of the safety related system
NOTE: T3 examples include: a source code compiler, 
a data/algorithms compiler, a tool to change set-points during system operation; an optimising 
compiler where the relationship between the source code program and the generated object code is 
not obvious; a compiler that incorporates an executable run-time package into the executable code.
\<close>
Definition*[traceability, short_name="''traceability''"]
\<open>degree to which relationship can be established between two or more products of a development 
process, especially those having a predecessor/successor or master/subordinate relationship to one 
another.\<close>

Definition*[validation, short_name="''validation''"]
\<open>process of analysis followed by a judgment based on evidence to
documentation, software or application) fits the user needs,in particular with respect to safety 
and quality and determine whether an item (e.g. process, with emphasis on the suitability of its 
operation in accordance to its purpose in its intended environment.\<close>

Definition*[validator, short_name="''validator''"]
\<open>entity that is responsible for the validation.\<close>

Definition*[verification, short_name="''verification''"]
\<open>process of examination followed by a judgment based on evidence that output items (process,
documentation, software or application) of a specific development phase fulfils the requirements of 
that phase with respect to completeness, correctness and consistency.
NOTE: Verification is mostly based on document reviews
(design, implementation, test documents etc.).
\<close>

Definition*[verifier, short_name="''verifier''"]
\<open>entity that is responsible for one or more verification activities.\<close>

chapter\<open>Software Management and Organisation\<close>
text\<open>Representing chapter 5 in @{cite "bsi:50128:2014"}.\<close>

section\<open>Organization, Roles and Responsabilities\<close>
text\<open>See also section \<^emph>\<open>Software management and organization\<close> and Annex B and C.\<close>

text\<open>REQ role in Table C.1 is assumed to be a typo and should be RQM.\<close>

datatype role =  RQM    \<comment> \<open>Requirements Manager\<close> 
              |  DES    \<comment> \<open>Designer\<close>
              |  IMP    \<comment> \<open>Implementer\<close> 
              |  TST    \<comment> \<open>Tester\<close>
              |  VER    \<comment> \<open>Verifier\<close>
              |  INT    \<comment> \<open>Integrator\<close>
              |  VAL    \<comment> \<open>Validator\<close>
              |  ASR    \<comment> \<open>Assessor\<close> 
              |  PM     \<comment> \<open>Program Manager\<close>
              |  CM     \<comment> \<open>Configuration Manager\<close>
              |  No_Role_Defined \<comment> \<open>See Annex C footnote a\<close>



datatype phase = SYSDEV_ext \<comment> \<open> System Development Phase (external)\<close>  
               | SPl        \<comment> \<open>Software Planning\<close>
               | SR         \<comment> \<open>Software Requirements\<close> 
               | SADES      \<comment> \<open>Software Architecture and Design\<close>
               | SCDES      \<comment> \<open>Software Component Design\<close> 
               | CInT       \<comment> \<open>Component Implementation and Testing\<close>
               | SI         \<comment> \<open>Software Integration\<close>
               | SV         \<comment> \<open>Overall Software Testing/Final Validation\<close>
               | SCADA      \<comment> \<open>Systems Configured by Application Data/Algorithms\<close>
               | SD         \<comment> \<open>Software Deployment\<close>
               | SM         \<comment> \<open>Software Maintenance\<close>
               | SA         \<comment> \<open>Software Assessment\<close>

abbreviation software_planning      :: "phase" where "software_planning  \<equiv> SPl"
abbreviation software_requirements      :: "phase" where "software_requirements  \<equiv> SR"
abbreviation software_architecture_and_design :: "phase"
  where "software_architecture_and_design \<equiv> SADES"
abbreviation software_component_design :: "phase" where "software_component_design \<equiv> SCDES"
abbreviation component_implementation_and_testing :: "phase" 
  where "component_implementation_and_testing \<equiv> CInT"
abbreviation software_integration      :: "phase" where "software_integration \<equiv> SI"
abbreviation software_validation       :: "phase" where "software_validation  \<equiv> SV"
abbreviation systems_configured_application_data_algorithm :: "phase"
  where "systems_configured_application_data_algorithm  \<equiv> SCADA"
abbreviation software_deployment       :: "phase" where "software_deployment  \<equiv> SD"
abbreviation software_maintenance      :: "phase" where "software_maintenance \<equiv> SM"
abbreviation software_assessment      :: "phase" where "software_assessment \<equiv> SM"

term "SR" (* meta-test *)


section\<open>Objectives, Conformance and Software Integrity Levels\<close>

datatype sil = SIL0 | SIL1 | SIL2 | SIL3 | SIL4

type_synonym safety_integration_level = sil

text\<open>Requirement levels specified Annex A: we use the term \<^emph>\<open>normative level\<close> to distinguish
them from the requirements specified in the standard.\<close>

datatype normative_level =
    M   \<comment> \<open>(Mandatory)\<close>
  | HR  \<comment> \<open>Highly Recommended\<close>
  | R   \<comment> \<open>Recommended\<close>
  | Any \<comment> \<open>No recommendation\<close>
  | NR  \<comment> \<open>Not Recommended\<close>

doc_class objective =
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

                              
text\<open>
The category \<^emph>\<open>hypothesis\<close> is used for assumptions from the 
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
      \<^item>   \<^term>\<open>P \<noteq> NP\<close>,
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
sfcual mismatch with @{typ objective}: \<close>
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

text\<open>Actually, the Figure 4 in Chapter 5: Illustrative Development Lifecycle 2 is more fidele
to the remaining document: Software Architecture and Design phases are merged, like in 7.3.\<close>

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

(* modelling example of a table ... *)

fun table_A_5 :: "vnt_technique \<Rightarrow> sil \<Rightarrow> normative_level option"
  where "table_A_5 (formal_proof _) = Map.empty(          SIL1 \<mapsto> R, SIL2 \<mapsto> R, SIL3 \<mapsto> HR,SIL4 \<mapsto> HR)"
       |"table_A_5 stat_analysis    = Map.empty(          SIL1 \<mapsto> HR,SIL2 \<mapsto> HR,SIL3 \<mapsto> HR,SIL4 \<mapsto> HR)"
       |"table_A_5 (dyn_analysis _) = Map.empty(          SIL1 \<mapsto> HR,SIL2 \<mapsto> HR,SIL3 \<mapsto> HR,SIL4 \<mapsto> HR)"
       |"table_A_5 traceability     = Map.empty(SIL0 \<mapsto> R,SIL1 \<mapsto> HR,SIL2 \<mapsto> HR,SIL3 \<mapsto> M ,SIL4 \<mapsto> M )"

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

section\<open> A Classification of CENELEC Reports and Documents \<close> 

(* should we rename this as "report" ??? bu *)
doc_class cenelec_report = text_element +
   phase        :: "phase"
   sil          :: "sil"
   level        :: "int option" <= "Some(0)"
   nlvl         :: "normative_level"          \<comment> \<open>Annex A Table A.1\<close>
   written_by   :: "role option"              \<comment> \<open>Annex C Table C.1 \<close>
   fst_check    :: "role option"              \<comment> \<open>Annex C Table C.1\<close>
   snd_check    :: "role option"              \<comment> \<open>Annex C Table C.1\<close>
   is_concerned :: "role set" <= "UNIV"
   accepts      "\<lbrace>objective\<rbrace>\<^sup>+||\<lbrace>requirement\<rbrace>\<^sup>+"
   invariant must_be_chapter :: "text_element.level \<sigma> = Some(0)" 
   invariant three_eyes_prcpl:: "  written_by \<sigma> \<noteq> fst_check \<sigma> 
                                 \<and> written_by \<sigma> \<noteq> snd_check \<sigma>"
   
text\<open>see \<^figure>\<open>fig3\<close> and Fig 4 in Chapter 5: Illustrative Development Lifecycle 2\<close>

doc_class external_specification =
  phase        :: "phase"  <= "SYSDEV_ext"

doc_class SYSREQS = external_specification + 
   phase        :: "phase"  <= "SYSDEV_ext" 
   type_synonym system_requirements_specification = SYSREQS

doc_class SYSSREQS = external_specification + 
   phase        :: "phase"  <= "SYSDEV_ext" 
   type_synonym system_safety_requirements_specification = SYSSREQS

doc_class SYSAD = external_specification + 
   phase        :: "phase"  <= "SYSDEV_ext" 
   type_synonym system_architecture_description = SYSAD

doc_class SYSS_pl = external_specification + 
   phase        :: "phase"  <= "SYSDEV_ext" 
   type_synonym system_safety_plan = SYSS_pl

(* SYS_VnV_pl exists in Figure 3 but not in Figure 4: surely a typo in Figure 4 *)
doc_class SYS_VnV_pl = external_specification +
   phase        :: "phase"  <= "SYSDEV_ext" 
   type_synonym system_VnV_plan = SYS_VnV_pl
                        
doc_class SQAP = cenelec_report +
   phase        :: "phase"  <= "SPl"
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_sqap :: "nlvl \<sigma> = HR"
   type_synonym software_quality_assurance_plan = SQAP

doc_class SQAVR = cenelec_report + 
   phase        :: "phase"  <= "SPl"
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_sqavr :: "nlvl \<sigma> = HR"
type_synonym software_quality_assurance_verfication_report = SQAVR

doc_class SCMP = cenelec_report + 
   phase        :: "phase"  <= "SPl"
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_scmp :: "nlvl \<sigma> = HR"
type_synonym software_configuration_management_plan = SCMP

doc_class SVP = cenelec_report + 
   phase        :: "phase"  <= "SPl"
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_svp :: "nlvl \<sigma> = HR"
type_synonym software_verification_plan = SVP

doc_class SVAP = cenelec_report + 
   phase        :: "phase"  <= "SPl"
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_svap :: "nlvl \<sigma> = HR"
type_synonym software_validation_plan = SVAP

doc_class SWRS = cenelec_report + 
   phase        :: "phase"  <= "SR"
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_swrs :: "nlvl \<sigma> = HR"
type_synonym software_requirements_specification = SWRS

doc_class OSWTS = cenelec_report + 
   phase        :: "phase"  <= "SR"
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_oswts :: "nlvl \<sigma> = HR"
   type_synonym overall_software_test_specification = OSWTS

doc_class SWRVR = cenelec_report + 
   phase        :: "phase"  <= "SR"
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_swrvr :: "nlvl \<sigma> = HR"
type_synonym software_requirements_verification_report = SWRVR
   
doc_class SWAS = cenelec_report + 
   phase        :: "phase"  <= "SADES" 
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_swas :: "nlvl \<sigma> = HR"
   type_synonym software_architecture_specification = SWAS

doc_class SWDS = cenelec_report + 
   phase        :: "phase"  <= "SADES"
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_swds :: "nlvl \<sigma> = HR"
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


doc_class SWIS = cenelec_report + 
   phase        :: "phase"  <= "SADES" 
   nlvl :: "normative_level" <= "HR"
   written_by   :: "role option"   <= "Some DES"
   fst_check    :: "role option"   <= "Some VER"
   snd_check    :: "role option"   <= "Some VAL"
   components   :: "SWIS_E list"
   invariant force_nlvl_swis :: "nlvl \<sigma> = HR"
   type_synonym software_interface_specifications = SWIS

doc_class SWITS = cenelec_report + 
   phase        :: "phase"  <= "SADES"
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_swits :: "nlvl \<sigma> = HR"
   type_synonym software_integration_test_specification = SWITS

doc_class SWHITS = cenelec_report + 
   phase        :: "phase"  <= "SADES"
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_swhits :: "nlvl \<sigma> = HR"
   type_synonym software_hardware_integration_test_specification = SWHITS

doc_class SWADVR = cenelec_report + 
   phase        :: "phase"  <= "SADES"
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_swadvr :: "nlvl \<sigma> = HR"
   type_synonym software_architecture_and_design_verification = SWADVR

doc_class SWCDS = cenelec_report + 
   phase        :: "phase"  <= "SCDES"
   invariant force_nlvl_swcds :: "if sil \<sigma> = SIL0 then nlvl \<sigma> = R else nlvl \<sigma> = HR"
   type_synonym software_component_design_specification = SWCDS

doc_class SWCTS = cenelec_report + 
   phase        :: "phase"  <= "SCDES"
   invariant force_nlvl_swcts :: "if sil \<sigma> = SIL0 then nlvl \<sigma> = R else nlvl \<sigma> = HR"
   type_synonym software_component_test_specification = SWCTS

doc_class SWCDVR = cenelec_report + 
   phase        :: "phase"  <= "SCDES"
   invariant force_nlvl_swcdvr :: "if sil \<sigma> = SIL0 then nlvl \<sigma> = R else nlvl \<sigma> = HR"
   type_synonym software_component_design_verification = SWCDVR

doc_class SWSCD = cenelec_report + 
   phase        :: "phase"  <= "CInT"
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_swscd :: "nlvl \<sigma> = HR"
   type_synonym software_source_code_and_documentation = SWSCD

doc_class SWCTR = cenelec_report + 
   phase        :: "phase"  <= "CInT"
   invariant force_nlvl_swctr :: "if sil \<sigma> = SIL0 then nlvl \<sigma> = R else nlvl \<sigma> = HR"
   type_synonym software_component_test_report = SWCTR

doc_class SWSCVR = cenelec_report + 
   phase        :: "phase"  <= "CInT"
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_swscvr :: "nlvl \<sigma> = HR"
   type_synonym software_source_code_verification_report = SWSCVR

doc_class SWITR = cenelec_report +
   phase        :: "phase"  <= "SI"
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_switr :: "nlvl \<sigma> = HR"
   type_synonym software_integration_test_report = SWITR

doc_class SWHAITR = cenelec_report +
   phase        :: "phase"  <= "SI"
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_swhaitr :: "nlvl \<sigma> = HR"
   type_synonym software_hardware_integration_test_report = SWHAITR

doc_class SWIVR = cenelec_report +
   phase        :: "phase"  <= "SI" 
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_swivr :: "nlvl \<sigma> = HR"
   type_synonym software_integration_verification_report = SWIVR

doc_class OSWTR = cenelec_report + 
   phase        :: "phase"  <= "SV"
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_oswtr :: "nlvl \<sigma> = HR"
type_synonym overall_software_test_report = OSWTR

doc_class SWVALR = cenelec_report +
   phase        :: "phase"  <= "SV" 
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_swvalr :: "nlvl \<sigma> = HR"
   type_synonym software_validation_report = SWVALR

doc_class TVALR = cenelec_report +
   phase        :: "phase"  <= "SV"
   invariant force_nlvl_tvalr :: "if sil \<sigma> = SIL0 then nlvl \<sigma> = R else nlvl \<sigma> = HR"
   type_synonym tools_validation_report = TVALR

doc_class SWVRN = cenelec_report +
   phase        :: "phase"  <= "SV"
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_swvrn :: "nlvl \<sigma> = HR"
   type_synonym software_validation_release_note = SWVRN

doc_class ARS = cenelec_report +
   phase        :: "phase"  <= "SCADA"
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_ars :: "nlvl \<sigma> = HR"
   type_synonym application_requirements_specification = ARS

doc_class APP = cenelec_report +
   phase        :: "phase"  <= "SCADA"
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_APP :: "nlvl \<sigma> = HR"
   type_synonym application_preparation_plan = APP

doc_class ATS = cenelec_report +
   phase        :: "phase"  <= "SCADA"
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_ats :: "nlvl \<sigma> = HR"
   type_synonym application_test_specification = ATS

doc_class AAD = cenelec_report +
   phase        :: "phase"  <= "SCADA"
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_aad :: "nlvl \<sigma> = HR"
   type_synonym application_architecture_design = AAD

doc_class APVR = cenelec_report +
   phase        :: "phase"  <= "SCADA"
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_apvr :: "nlvl \<sigma> = HR"
   type_synonym application_preparation_verification_report = APVR

doc_class ATR = cenelec_report +
   phase        :: "phase"  <= "SCADA"
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_atr :: "nlvl \<sigma> = HR"
   type_synonym application_test_report= ATR

doc_class SOCOADA = cenelec_report +
   phase        :: "phase"  <= "SCADA"
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_socoada :: "nlvl \<sigma> = HR"
   type_synonym source_code_application_data_algorithms = SOCOADA

doc_class ADAVR = cenelec_report +
   phase        :: "phase"  <= "SCADA"
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_adavr :: "nlvl \<sigma> = HR"
   type_synonym application_data_algorithms_verification_report= ADAVR

doc_class SWRDP = cenelec_report + 
   phase        :: "phase"  <= "SD"
   invariant force_nlvl_swrdp :: "if sil \<sigma> = SIL0 then nlvl \<sigma> = R else nlvl \<sigma> = HR"
   type_synonym software_release_deployment_plan = SWRDP

doc_class SWDM = cenelec_report + 
   phase        :: "phase"  <= "SD"
   invariant force_nlvl_swdm :: "if sil \<sigma> = SIL0 then nlvl \<sigma> = R else nlvl \<sigma> = HR"
   type_synonym software_deployment_manual = SWDM

doc_class SWDRN = cenelec_report + 
   phase        :: "phase"  <= "SD"
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_swdrn :: "nlvl \<sigma> = HR"
   type_synonym software_deployment_release_notes = SWDRN

doc_class SWDR = cenelec_report + 
   phase        :: "phase"  <= "SD"
   invariant force_nlvl_swdr :: "if sil \<sigma> = SIL0 then nlvl \<sigma> = R else nlvl \<sigma> = HR"
   type_synonym software_deployment_records = SWDR

doc_class SWDVR = cenelec_report + 
   phase        :: "phase"  <= "SD"
   invariant force_nlvl_swdvr :: "if sil \<sigma> = SIL0 then nlvl \<sigma> = R else nlvl \<sigma> = HR"
   type_synonym software_deployment_verification_report = SWDVR

doc_class SWMP = cenelec_report + 
   phase        :: "phase"  <= "SM"
   invariant force_nlvl_swmp :: "if sil \<sigma> = SIL0 then nlvl \<sigma> = R else nlvl \<sigma> = HR"
   type_synonym software_maintenance_plan = SWMP

doc_class SWCR = cenelec_report + 
   phase        :: "phase"  <= "SM"
   nlvl :: "normative_level" <= "HR"
   invariant force_nlvl_swcr :: "nlvl \<sigma> = HR"
   type_synonym software_change_records = SWCR

doc_class SWMR = cenelec_report +
   phase        :: "phase"  <= "SM"
   invariant force_nlvl_swmr :: "if sil \<sigma> = SIL0 then nlvl \<sigma> = R else nlvl \<sigma> = HR"
type_synonym software_maintenance_records = SWMR

doc_class SWMVR = cenelec_report + 
   phase        :: "phase"  <= "SM"
   invariant force_nlvl_swmvr :: "if sil \<sigma> = SIL0 then nlvl \<sigma> = R else nlvl \<sigma> = HR"
   type_synonym software_maintenance_verification_report = SWMVR

doc_class SWAP = cenelec_report + 
   phase        :: "phase"  <= "SA"
   invariant force_nlvl_swap :: "if sil \<sigma> = SIL0 then nlvl \<sigma> = R else nlvl \<sigma> = HR"
   type_synonym software_assessment_plan = SWAP

doc_class SWAR = cenelec_report + 
   phase        :: "phase"  <= "SA"
   invariant force_nlvl_swar :: "if sil \<sigma> = SIL0 then nlvl \<sigma> = R else nlvl \<sigma> = HR"
   type_synonym software_assessment_report = SWAR

text\<open>Table A.1: Lifecycle Issues and Documentation (5.3).
The requirement levels of table A.1 is expressed with monitor classes:
first the SIL of each class is enforced to be the same as the monitor class SIL,
then, when closing the monitor, the normative level (requirement level in CENELEC lingua)
of each CENELEC document instance is checked and warning/errors are triggered
if they do not respect the monitor class SIL\<close>

doc_class monitor_SIL =
  sil :: sil

doc_class monitor_SIL0 = monitor_SIL +
  sil :: sil <= SIL0
  accepts "\<lbrakk>SQAP\<rbrakk> ~~ \<lbrakk>SQAVR\<rbrakk> ~~ \<lbrakk>SCMP\<rbrakk> ~~ \<lbrakk>SVP\<rbrakk> ~~ \<lbrakk>SVAP\<rbrakk>
           ~~ \<lbrakk>SWRS\<rbrakk> ~~ \<lbrakk>OSWTS\<rbrakk> ~~ \<lbrakk>SWRVR\<rbrakk>
           ~~ \<lbrakk>SWAS\<rbrakk> ~~ \<lbrakk>SWDS\<rbrakk> ~~ \<lbrakk>SWIS\<rbrakk> ~~ \<lbrakk>SWITS\<rbrakk> ~~ \<lbrakk>SWHITS\<rbrakk> ~~ \<lbrakk>SWADVR\<rbrakk>
           ~~ \<lbrakk>SWCDS\<rbrakk> ~~ \<lbrakk>SWCTS\<rbrakk> ~~ \<lbrakk>SWCDVR\<rbrakk>
           ~~ \<lbrakk>SWSCD\<rbrakk> ~~ \<lbrakk>SWCTR\<rbrakk> ~~ \<lbrakk>SWSCVR\<rbrakk>
           ~~ \<lbrakk>SWITR\<rbrakk> ~~ \<lbrakk>SWHAITR\<rbrakk> ~~ \<lbrakk>SWIVR\<rbrakk>
           ~~ \<lbrakk>OSWTR\<rbrakk> ~~ \<lbrakk>SWVALR\<rbrakk> ~~ \<lbrakk>TVALR\<rbrakk> ~~ \<lbrakk>SWVRN\<rbrakk>
           ~~ \<lbrakk>ARS\<rbrakk> ~~ \<lbrakk>APP\<rbrakk> ~~ \<lbrakk>ATS\<rbrakk> ~~ \<lbrakk>AAD\<rbrakk> ~~ \<lbrakk>APVR\<rbrakk> ~~ \<lbrakk>ATR\<rbrakk> ~~ \<lbrakk>SOCOADA\<rbrakk> ~~ \<lbrakk>ADAVR\<rbrakk>
           ~~ \<lbrakk>SWRDP\<rbrakk> ~~ \<lbrakk>SWDM\<rbrakk> ~~ \<lbrakk>SWDRN\<rbrakk> ~~ \<lbrakk>SWDR\<rbrakk> ~~ \<lbrakk>SWDVR\<rbrakk>
           ~~ \<lbrakk>SWMP\<rbrakk> ~~ \<lbrakk>SWCR\<rbrakk> ~~ \<lbrakk>SWMR\<rbrakk> ~~ \<lbrakk>SWMVR\<rbrakk>
           ~~ \<lbrakk>SWAP\<rbrakk> ~~ \<lbrakk>SWAR\<rbrakk>"
  invariant force_sil0 :: "sil \<sigma> = SIL0"

doc_class monitor_SIL1 = monitor_SIL +
  sil :: sil <= SIL1
  accepts "\<lbrakk>SQAP\<rbrakk> ~~ \<lbrakk>SQAVR\<rbrakk> ~~ \<lbrakk>SCMP\<rbrakk> ~~ \<lbrakk>SVP\<rbrakk> ~~ \<lbrakk>SVAP\<rbrakk>
           ~~ \<lbrakk>SWRS\<rbrakk> ~~ \<lbrakk>OSWTS\<rbrakk> ~~ \<lbrakk>SWRVR\<rbrakk>
           ~~ \<lbrakk>SWAS\<rbrakk> ~~ \<lbrakk>SWDS\<rbrakk> ~~ \<lbrakk>SWIS\<rbrakk> ~~ \<lbrakk>SWITS\<rbrakk> ~~ \<lbrakk>SWHITS\<rbrakk> ~~ \<lbrakk>SWADVR\<rbrakk>
           ~~ \<lbrakk>SWCDS\<rbrakk> ~~ \<lbrakk>SWCTS\<rbrakk> ~~ \<lbrakk>SWCDVR\<rbrakk>
           ~~ \<lbrakk>SWSCD\<rbrakk> ~~ \<lbrakk>SWCTR\<rbrakk> ~~ \<lbrakk>SWSCVR\<rbrakk>
           ~~ \<lbrakk>SWITR\<rbrakk> ~~ \<lbrakk>SWHAITR\<rbrakk> ~~ \<lbrakk>SWIVR\<rbrakk>
           ~~ \<lbrakk>OSWTR\<rbrakk> ~~ \<lbrakk>SWVALR\<rbrakk> ~~ \<lbrakk>TVALR\<rbrakk> ~~ \<lbrakk>SWVRN\<rbrakk>
           ~~ \<lbrakk>ARS\<rbrakk> ~~ \<lbrakk>APP\<rbrakk> ~~ \<lbrakk>ATS\<rbrakk> ~~ \<lbrakk>AAD\<rbrakk> ~~ \<lbrakk>APVR\<rbrakk> ~~ \<lbrakk>ATR\<rbrakk> ~~ \<lbrakk>SOCOADA\<rbrakk> ~~ \<lbrakk>ADAVR\<rbrakk>
           ~~ \<lbrakk>SWRDP\<rbrakk> ~~ \<lbrakk>SWDM\<rbrakk> ~~ \<lbrakk>SWDRN\<rbrakk> ~~ \<lbrakk>SWDR\<rbrakk> ~~ \<lbrakk>SWDVR\<rbrakk>
           ~~ \<lbrakk>SWMP\<rbrakk> ~~ \<lbrakk>SWCR\<rbrakk> ~~ \<lbrakk>SWMR\<rbrakk> ~~ \<lbrakk>SWMVR\<rbrakk>
           ~~ \<lbrakk>SWAP\<rbrakk> ~~ \<lbrakk>SWAR\<rbrakk>"
  invariant force_sil1 :: "sil \<sigma> = SIL1"

doc_class monitor_SIL2 = monitor_SIL +
  sil :: sil <= SIL2
  accepts "\<lbrakk>SQAP\<rbrakk> ~~ \<lbrakk>SQAVR\<rbrakk> ~~ \<lbrakk>SCMP\<rbrakk> ~~ \<lbrakk>SVP\<rbrakk> ~~ \<lbrakk>SVAP\<rbrakk>
           ~~ \<lbrakk>SWRS\<rbrakk> ~~ \<lbrakk>OSWTS\<rbrakk> ~~ \<lbrakk>SWRVR\<rbrakk>
           ~~ \<lbrakk>SWAS\<rbrakk> ~~ \<lbrakk>SWDS\<rbrakk> ~~ \<lbrakk>SWIS\<rbrakk> ~~ \<lbrakk>SWITS\<rbrakk> ~~ \<lbrakk>SWHITS\<rbrakk> ~~ \<lbrakk>SWADVR\<rbrakk>
           ~~ \<lbrakk>SWCDS\<rbrakk> ~~ \<lbrakk>SWCTS\<rbrakk> ~~ \<lbrakk>SWCDVR\<rbrakk>
           ~~ \<lbrakk>SWSCD\<rbrakk> ~~ \<lbrakk>SWCTR\<rbrakk> ~~ \<lbrakk>SWSCVR\<rbrakk>
           ~~ \<lbrakk>SWITR\<rbrakk> ~~ \<lbrakk>SWHAITR\<rbrakk> ~~ \<lbrakk>SWIVR\<rbrakk>
           ~~ \<lbrakk>OSWTR\<rbrakk> ~~ \<lbrakk>SWVALR\<rbrakk> ~~ \<lbrakk>TVALR\<rbrakk> ~~ \<lbrakk>SWVRN\<rbrakk>
           ~~ \<lbrakk>ARS\<rbrakk> ~~ \<lbrakk>APP\<rbrakk> ~~ \<lbrakk>ATS\<rbrakk> ~~ \<lbrakk>AAD\<rbrakk> ~~ \<lbrakk>APVR\<rbrakk> ~~ \<lbrakk>ATR\<rbrakk> ~~ \<lbrakk>SOCOADA\<rbrakk> ~~ \<lbrakk>ADAVR\<rbrakk>
           ~~ \<lbrakk>SWRDP\<rbrakk> ~~ \<lbrakk>SWDM\<rbrakk> ~~ \<lbrakk>SWDRN\<rbrakk> ~~ \<lbrakk>SWDR\<rbrakk> ~~ \<lbrakk>SWDVR\<rbrakk>
           ~~ \<lbrakk>SWMP\<rbrakk> ~~ \<lbrakk>SWCR\<rbrakk> ~~ \<lbrakk>SWMR\<rbrakk> ~~ \<lbrakk>SWMVR\<rbrakk>
           ~~ \<lbrakk>SWAP\<rbrakk> ~~ \<lbrakk>SWAR\<rbrakk>"
  invariant force_sil2 :: "sil \<sigma> = SIL2"

doc_class monitor_SIL3 = monitor_SIL +
  sil :: sil <= SIL3
  accepts "\<lbrakk>SQAP\<rbrakk> ~~ \<lbrakk>SQAVR\<rbrakk> ~~ \<lbrakk>SCMP\<rbrakk> ~~ \<lbrakk>SVP\<rbrakk> ~~ \<lbrakk>SVAP\<rbrakk>
           ~~ \<lbrakk>SWRS\<rbrakk> ~~ \<lbrakk>OSWTS\<rbrakk> ~~ \<lbrakk>SWRVR\<rbrakk>
           ~~ \<lbrakk>SWAS\<rbrakk> ~~ \<lbrakk>SWDS\<rbrakk> ~~ \<lbrakk>SWIS\<rbrakk> ~~ \<lbrakk>SWITS\<rbrakk> ~~ \<lbrakk>SWHITS\<rbrakk> ~~ \<lbrakk>SWADVR\<rbrakk>
           ~~ \<lbrakk>SWCDS\<rbrakk> ~~ \<lbrakk>SWCTS\<rbrakk> ~~ \<lbrakk>SWCDVR\<rbrakk>
           ~~ \<lbrakk>SWSCD\<rbrakk> ~~ \<lbrakk>SWCTR\<rbrakk> ~~ \<lbrakk>SWSCVR\<rbrakk>
           ~~ \<lbrakk>SWITR\<rbrakk> ~~ \<lbrakk>SWHAITR\<rbrakk> ~~ \<lbrakk>SWIVR\<rbrakk>
           ~~ \<lbrakk>OSWTR\<rbrakk> ~~ \<lbrakk>SWVALR\<rbrakk> ~~ \<lbrakk>TVALR\<rbrakk> ~~ \<lbrakk>SWVRN\<rbrakk>
           ~~ \<lbrakk>ARS\<rbrakk> ~~ \<lbrakk>APP\<rbrakk> ~~ \<lbrakk>ATS\<rbrakk> ~~ \<lbrakk>AAD\<rbrakk> ~~ \<lbrakk>APVR\<rbrakk> ~~ \<lbrakk>ATR\<rbrakk> ~~ \<lbrakk>SOCOADA\<rbrakk> ~~ \<lbrakk>ADAVR\<rbrakk>
           ~~ \<lbrakk>SWRDP\<rbrakk> ~~ \<lbrakk>SWDM\<rbrakk> ~~ \<lbrakk>SWDRN\<rbrakk> ~~ \<lbrakk>SWDR\<rbrakk> ~~ \<lbrakk>SWDVR\<rbrakk>
           ~~ \<lbrakk>SWMP\<rbrakk> ~~ \<lbrakk>SWCR\<rbrakk> ~~ \<lbrakk>SWMR\<rbrakk> ~~ \<lbrakk>SWMVR\<rbrakk>
           ~~ \<lbrakk>SWAP\<rbrakk> ~~ \<lbrakk>SWAR\<rbrakk>"
  invariant force_sil3 :: "sil \<sigma> = SIL3"

doc_class monitor_SIL4 = monitor_SIL +
  sil :: sil <= SIL4
  accepts "\<lbrakk>SQAP\<rbrakk> ~~ \<lbrakk>SQAVR\<rbrakk> ~~ \<lbrakk>SCMP\<rbrakk> ~~ \<lbrakk>SVP\<rbrakk> ~~ \<lbrakk>SVAP\<rbrakk>
           ~~ \<lbrakk>SWRS\<rbrakk> ~~ \<lbrakk>OSWTS\<rbrakk> ~~ \<lbrakk>SWRVR\<rbrakk>
           ~~ \<lbrakk>SWAS\<rbrakk> ~~ \<lbrakk>SWDS\<rbrakk> ~~ \<lbrakk>SWIS\<rbrakk> ~~ \<lbrakk>SWITS\<rbrakk> ~~ \<lbrakk>SWHITS\<rbrakk> ~~ \<lbrakk>SWADVR\<rbrakk>
           ~~ \<lbrakk>SWCDS\<rbrakk> ~~ \<lbrakk>SWCTS\<rbrakk> ~~ \<lbrakk>SWCDVR\<rbrakk>
           ~~ \<lbrakk>SWSCD\<rbrakk> ~~ \<lbrakk>SWCTR\<rbrakk> ~~ \<lbrakk>SWSCVR\<rbrakk>
           ~~ \<lbrakk>SWITR\<rbrakk> ~~ \<lbrakk>SWHAITR\<rbrakk> ~~ \<lbrakk>SWIVR\<rbrakk>
           ~~ \<lbrakk>OSWTR\<rbrakk> ~~ \<lbrakk>SWVALR\<rbrakk> ~~ \<lbrakk>TVALR\<rbrakk> ~~ \<lbrakk>SWVRN\<rbrakk>
           ~~ \<lbrakk>ARS\<rbrakk> ~~ \<lbrakk>APP\<rbrakk> ~~ \<lbrakk>ATS\<rbrakk> ~~ \<lbrakk>AAD\<rbrakk> ~~ \<lbrakk>APVR\<rbrakk> ~~ \<lbrakk>ATR\<rbrakk> ~~ \<lbrakk>SOCOADA\<rbrakk> ~~ \<lbrakk>ADAVR\<rbrakk>
           ~~ \<lbrakk>SWRDP\<rbrakk> ~~ \<lbrakk>SWDM\<rbrakk> ~~ \<lbrakk>SWDRN\<rbrakk> ~~ \<lbrakk>SWDR\<rbrakk> ~~ \<lbrakk>SWDVR\<rbrakk>
           ~~ \<lbrakk>SWMP\<rbrakk> ~~ \<lbrakk>SWCR\<rbrakk> ~~ \<lbrakk>SWMR\<rbrakk> ~~ \<lbrakk>SWMVR\<rbrakk>
           ~~ \<lbrakk>SWAP\<rbrakk> ~~ \<lbrakk>SWAR\<rbrakk>"
  invariant force_sil4 :: "sil \<sigma> = SIL4"

ML\<open>
fun check_sil oid _ ctxt =
  let
    val ctxt' = Proof_Context.init_global(Context.theory_of ctxt)
    val DOF_core.Instance {value = monitor_record_value, ...} =
                          DOF_core.get_instance_global oid (Context.theory_of ctxt)
    val Const _ $ _ $ monitor_sil $ _ = monitor_record_value
    val traces = AttributeAccess.compute_trace_ML ctxt oid NONE \<^here>
    fun check_sil'' [] = true
      | check_sil'' (x::xs) =
          let
            val (_, doc_oid) = x
            val DOF_core.Instance {value = doc_record_value, ...} =
                      DOF_core.get_instance_global doc_oid (Context.theory_of ctxt)
            val Const _ $ _ $ _ $ _ $ _ $ cenelec_document_ext = doc_record_value
            val Const _ $ _ $ _ $ doc_sil $ _ $ _ $ _ $ _ $ _ $ _ = cenelec_document_ext
          in 
            if doc_sil <> monitor_sil
            then error(doc_oid
                       ^ " cenelec document SIL must be: "
                       ^ Syntax.string_of_term ctxt' monitor_sil)
            else check_sil'' xs end
  in check_sil'' traces end
\<close>

setup\<open>
(fn thy =>
let val ctxt = Proof_Context.init_global thy
    val binding = DOF_core.binding_from_onto_class_pos "monitor_SIL0" thy
in  DOF_core.add_ml_invariant binding check_sil thy end)
\<close>

text\<open>
A more generic example of check_sil which can be generalized:
it is decoupled from the CENELEC current implementation
but is much less efficient regarding time computation by relying on Isabelle evaluation mechanism.\<close>
ML\<open>
fun check_sil_slow oid _ ctxt =
  let 
    val ctxt' = Proof_Context.init_global(Context.theory_of ctxt)
    val DOF_core.Instance {value = monitor_record_value, ...} =
                          DOF_core.get_instance_global oid (Context.theory_of ctxt)
    val DOF_core.Instance {cid = monitor_cid, ...} =
                          DOF_core.get_instance_global oid (Context.theory_of ctxt)
    val monitor_sil_typ = (Syntax.read_typ ctxt' monitor_cid) --> @{typ "sil"}
    val monitor_sil = Value_Command.value ctxt'
                    (Const("CENELEC_50128.monitor_SIL.sil", monitor_sil_typ) $ monitor_record_value)
    val traces = AttributeAccess.compute_trace_ML ctxt oid NONE \<^here>
    fun check_sil'  [] = true
      | check_sil' (x::xs) =
          let
            val (doc_cid, doc_oid) = x
            val DOF_core.Instance {value = doc_record_value, ...} =
                    DOF_core.get_instance_global doc_oid (Context.theory_of ctxt)
            val doc_sil_typ = (Syntax.read_typ ctxt' doc_cid) --> @{typ "sil"} 
            val doc_sil = Value_Command.value ctxt'
                    (Const ("CENELEC_50128.cenelec_document.sil", doc_sil_typ) $ doc_record_value)
          in 
            if doc_sil <> monitor_sil
            then error(doc_oid
                       ^ " cenelec document SIL must be: "
                       ^ Syntax.string_of_term ctxt' monitor_sil)
            else check_sil' xs end
  in check_sil' traces end
\<close>

(*setup\<open>
(fn thy =>
let val ctxt = Proof_Context.init_global thy
    val binding = DOF_core.binding_from_onto_class_pos "monitor_SIL0" thy
in  DOF_core.add_ml_invariant binding check_sil_slow thy end)
\<close>*)

(* As traces of monitor instances (docitems) are updated each time an instance is declared
  (with text*, section*, etc.), invariants checking functions which check the full list of traces
  must be declared as lazy invariants, to be checked only when closing a monitor, i.e.,
  after all the monitor traces are populated.
*)
ML\<open>
fun check_required_documents oid _ ctxt = 
  let
    val ctxt' = Proof_Context.init_global(Context.theory_of ctxt)
    val DOF_core.Monitor_Info {accepted_cids, ...} =
                      DOF_core.get_monitor_info_global oid (Context.theory_of ctxt)
    val traces = AttributeAccess.compute_trace_ML ctxt oid NONE \<^here>
    fun check_required_documents' [] = true
      | check_required_documents' (cid::cids) =
          if exists (fn (doc_cid, _) => equal cid doc_cid) traces
          then check_required_documents' cids
          else
            let
              val ctxt' = Proof_Context.init_global(Context.theory_of ctxt)
              val DOF_core.Instance {value = monitor_record_value, ...} =
                          DOF_core.get_instance_global oid (Context.theory_of ctxt)
              val Const _ $ _ $ monitor_sil $ _ = monitor_record_value
            in error ("A " ^ cid ^ " cenelec document is required with "
                      ^ Syntax.string_of_term ctxt' monitor_sil)
            end
  in check_required_documents' accepted_cids end
\<close>

setup\<open>
fn thy =>
let val ctxt = Proof_Context.init_global thy
    val binding = DOF_core.binding_from_onto_class_pos "monitor_SIL0" thy
in  DOF_core.add_closing_ml_invariant binding check_required_documents thy end
\<close>

(* Test pattern matching for the records of the current CENELEC implementation classes,
   and used by checking functions.
   If the test failed, then it means that the CENELEC implementation has changed
   (the class definitions have been updated) and the checking functions must be updated.
*)
text*[MonitorPatternMatchingTest::monitor_SIL0]\<open>\<close>
text*[CenelecClassPatternMatchingTest::SQAP, sil = "SIL0"]\<open>\<close>
ML\<open>
val thy = @{theory}
val DOF_core.Instance {value = monitor_record_value, ...} =
                                        DOF_core.get_instance_global "MonitorPatternMatchingTest" thy
val Const _ $ _ $ monitor_sil $ _ = monitor_record_value
val DOF_core.Instance {value = doc_record_value, ...} =
                                    DOF_core.get_instance_global "CenelecClassPatternMatchingTest" thy
val Const _ $ _ $ _ $ _ $ _ $ cenelec_document_ext = doc_record_value
val Const _ $ _ $ _ $ doc_sil $ _ $ _ $ _ $ _ $ _ $ _ = cenelec_document_ext
\<close>

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
\<^enum> @{typ overall_software_test_specification} Overall Software Test Specification
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
            (SWRS || OSWTS)  "                \<comment> \<open>software requirements specification OR
                                                 overall software test specification\<close> 
(* MORE TO COME : *)

section\<open> META : Testing and Validation \<close>

text\<open>Test : @{semi_formal_content \<open>COTS\<close>}\<close>

ML
\<open> DOF_core.get_onto_class_name_global "requirement" @{theory};
  DOF_core.get_onto_class_name_global "SRAC" @{theory};
  DOF_core.get_onto_class_global "SRAC" @{theory};
  DOF_core.get_onto_class_global "EC" @{theory}; \<close>

ML
\<open> DOF_core.is_subclass @{context} "CENELEC_50128.EC"   "CENELEC_50128.EC";
  DOF_core.is_subclass @{context} "CENELEC_50128.SRAC" "CENELEC_50128.EC";
  DOF_core.is_subclass @{context} "CENELEC_50128.EC"   "CENELEC_50128.SRAC";
  DOF_core.is_subclass @{context} "CENELEC_50128.EC"   "CENELEC_50128.test_requirement"; \<close>

ML
\<open> val ref_tab = DOF_core.get_instances \<^context> 
  val docclass_tab = DOF_core.get_onto_classes @{context};
  Name_Space.dest_table ref_tab;
  Name_Space.dest_table docclass_tab; \<close>

ML
\<open> val internal_data_of_SRAC_definition = DOF_core.get_attributes_local "SRAC" @{context} \<close> 

ML
\<open> DOF_core.get_onto_class_name_global "requirement" @{theory};
  Syntax.parse_typ                 @{context} "requirement";
  val Type(t,_) = Syntax.parse_typ @{context} "requirement" handle ERROR _ => dummyT; 
  Syntax.read_typ                  @{context} "hypothesis"  handle  _ => dummyT;
  Proof_Context.init_global; \<close>

end