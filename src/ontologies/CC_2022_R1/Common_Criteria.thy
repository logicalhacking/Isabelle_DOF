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
theory Common_Criteria
  imports  "Isabelle_DOF.Common_Criteria_terms"
begin

define_shortcut* csp      \<rightleftharpoons> \<open>CSP\<close>
                 holcsp   \<rightleftharpoons> \<open>HOL-CSP\<close>
                 hol      \<rightleftharpoons> \<open>HOL\<close>
                 isabelle \<rightleftharpoons> \<open>Isabelle/HOL\<close>


datatype cc_spec =
      package             
    | PP                  
    | PP_module           
    | PP_configuration    
    | ST                  
    | PP_PP_configuration 

datatype cc_spec_chapter =
      Introduction
    | Conformance
    | SPD \<comment> \<open>Security problem definition  \<^cc_term>\<open>SPD\<close>\<close>
    | SO  \<comment> \<open>Security objectives  \<^cc_term>\<open>SO\<close>\<close>
    | ECD \<comment> \<open>Extended components definition\<close>
    | SR  \<comment> \<open>Security requirements  \<^cc_term>\<open>SR\<close>\<close>

datatype cc_spec_section =
      PP_reference
    | PP_overview
    | Threats
    | Assumptions
    | OSPs          \<comment> \<open>organizational security policies\<close>
    | SO_for_TOE    \<comment> \<open>security objectives for the TOE\<close>
    | SO_for_OE     \<comment> \<open>security objectives for the operational environment\<close>
    | SOR           \<comment> \<open>security objectives rationale\<close>
    | SFRs          \<comment> \<open>security functional requirements\<close>
    | SARs          \<comment> \<open>security assurance requirements\<close>

doc_class cc_spec_report = text_element +
    cc_spec         ::    "cc_spec"
    cc_definition   ::    "cc_term option" <= "None"

doc_class PP_report = cc_spec_report +
    cc_spec           ::    "cc_spec" <= "PP"
    level             ::    "int option" <= "Some 1"
    invariant PP_spec ::    \<open>cc_spec \<sigma> = PP\<close>

(* Declaration of the superclass of each chapter of the specification of PP*)
doc_class PP_introduction_report = PP_report +
    cc_spec_chapter     ::    "cc_spec_chapter" <= "Introduction"
    invariant introduction_chapter ::  \<open>cc_spec_chapter \<sigma> = Introduction\<close>

doc_class PP_Conformance_report = PP_report +
    cc_spec_chapter     ::    "cc_spec_chapter" <= "Conformance"
    invariant conformance_chapter ::  \<open>cc_spec_chapter \<sigma> = Conformance\<close>

doc_class PP_SPD_report = PP_report +
    cc_spec_chapter       ::    "cc_spec_chapter" <= "SPD"
    invariant SPD_chapter ::  \<open>cc_spec_chapter \<sigma> = SPD\<close>

doc_class PP_SO_report = PP_report +
    cc_spec_chapter       ::    "cc_spec_chapter" <= "SO"
    invariant SO_chapter  ::  \<open>cc_spec_chapter \<sigma> = SO\<close>

doc_class PP_ECD_report = PP_report +
    cc_spec_chapter       ::    "cc_spec_chapter" <= "ECD"
    invariant ECD_chapter ::  \<open>cc_spec_chapter \<sigma> = ECD\<close>

doc_class PP_SR_report = PP_report +
cc_spec_chapter       ::    "cc_spec_chapter" <= "SR"
    invariant SR_chapter  ::  \<open>cc_spec_chapter \<sigma> = SR\<close>

(* Declaration of the sections in the PP introduction *)
doc_class PP_introduction = PP_introduction_report +
    level             ::    "int option" <= "Some 0"

doc_class PP_reference = PP_introduction_report +
    cc_spec_section   ::    "cc_spec_section" <= "PP_reference"
    cc_title             ::    "title"
    version           ::    "string" <= "''''"
    sponsors          ::    "string list" <= "[]"
    publication_date  ::    "string" <= "''''"
    invariant null_title    ::    \<open>short_title (cc_title \<sigma>) \<noteq> None\<close> 
    invariant null_version  ::    \<open>version \<sigma> \<noteq> ''''\<close>
    invariant null_sponsors ::    \<open>sponsors \<sigma> \<noteq> []\<close>
    invariant null_date     ::    \<open>publication_date \<sigma> \<noteq> ''''\<close>

term\<open>scholarly_paper.short_title (cc_title a) \<noteq> None \<and> 
     the(scholarly_paper.short_title (cc_title a)) \<noteq> ''''\<close>

doc_class PP_overview = PP_introduction_report +
    cc_spec_section  ::    "cc_spec_section" <= "PP_overview"

(* Declaration of the sections in the conformance *)

doc_class Conformance = PP_Conformance_report +
    level             ::    "int option" <= "Some 0"

(* Declaration of the sections in the security problem definition *)

doc_class SPD = PP_SPD_report +
    cc_definition     ::    "cc_term option" <= "Some @{cc-term \<open>SPD\<close>}"
    level             ::    "int option" <= "Some 0"

doc_class Threats = PP_SPD_report +
    cc_spec_section  ::    "cc_spec_section" <= "Threats"

doc_class Assumptions = PP_SPD_report +
    cc_spec_section  ::    "cc_spec_section" <= "Assumptions"

doc_class OSPs = PP_SPD_report +
    cc_spec_section  ::    "cc_spec_section" <= "OSPs"
    type_synonym organizational_security_policies = OSPs

(* Declaration of the sections in the security objectives *)

doc_class SO = PP_SO_report +
    level             ::    "int option" <= "Some 0"

doc_class SO_for_TOE = PP_SO_report +
    cc_spec_section  ::    "cc_spec_section" <= "SO_for_TOE"
    type_synonym security_objectives_for_the_TOE = SO_for_TOE

doc_class SO_for_OE = PP_SO_report +
    cc_spec_section  ::    "cc_spec_section" <= "SO_for_OE"
    type_synonym security_objectives_for_the_operational_environment = SO_for_TOE

doc_class SOR = PP_SO_report +
    cc_spec_section  ::    "cc_spec_section" <= "SOR"
    type_synonym security_objectives_rationale = SOR

(* Declaration of the sections in the extended components definition *)

doc_class ECD = PP_ECD_report +
    level             ::    "int option" <= "Some 0"

doc_class ECD_section = PP_ECD_report +
    ECD_title           ::    "title"
    type_synonym extended_component_definition = ECD_section

(* Declaration of the sections in the Security requirements *)

doc_class SR = PP_SR_report +
    
    level             ::    "int option" <= "Some 0"

doc_class SFR = PP_SR_report +
    level             ::    "int option" <= "Some 2"
    cc_spec_section  ::    "cc_spec_section" <= "SFRs"

doc_class SAR = PP_SR_report +
    level             ::    "int option" <= "Some 2"
    cc_spec_section  ::    "cc_spec_section" <= "SARs"
    
doc_class SFRs = PP_SR_report +
    cc_spec_section  ::    "cc_spec_section" <= "SFRs"
    accepts "\<lbrace>SFR\<rbrace>\<^sup>+"

doc_class SARs = PP_SR_report +
    cc_spec_section  ::    "cc_spec_section" <= "SARs"
    accepts "\<lbrace>SAR\<rbrace>\<^sup>+"

(* Declaration of the monitor of each chapter of the PP specification *)

doc_class PP_introduction_monitor = 
    cc_spec         ::    "cc_spec" <= "PP"
    accepts "PP_introduction  ~~ PP_reference ~~ PP_overview"

doc_class Conformance_monitor = 
    cc_spec         ::    "cc_spec" <= "PP"
    accepts "Conformance ~~ \<lbrace>PP_Conformance_report\<rbrace>\<^sup>*"

doc_class SPD_monitor = 
    cc_spec         ::    "cc_spec" <= "PP"
    accepts "Threats ~~ Assumptions ~~ \<lbrakk>OSPs\<rbrakk>"

doc_class SO_monitor = 
    cc_spec         ::    "cc_spec" <= "PP"
    accepts "SO_for_TOE ~~ SO_for_OE ~~ \<lbrakk>SOR\<rbrakk>"

doc_class ECD_monitor = 
    cc_spec         ::    "cc_spec" <= "PP"
    accepts "\<lbrace>ECD_section\<rbrace>\<^sup>+"

doc_class SR_monitor = 
    cc_spec         ::    "cc_spec" <= "PP"
    accepts "SFRs ~~ SARs"

doc_class Appendix = cc_spec_report +
    level             ::    "int option" <= "Some 0"
    letter          ::    "char"

doc_class Annex = cc_spec_report +
    level             ::    "int option" <= "Some 0"
    letter          ::    "char"

(* Declaration of the monitor of the whole PP specification *)
doc_class monitor_cc_spec =
    cc_spec         ::    "cc_spec"

doc_class monitor_PP_spec =
    cc_spec         ::    "cc_spec" <= "PP"
    accepts "title ~~ PP_introduction_monitor ~~ Conformance_monitor ~~ 
             SPD_monitor ~~ SO_monitor ~~ \<lbrakk>ECD_monitor\<rbrakk> ~~ SR_monitor ~~ \<lbrace>Appendix\<rbrace>\<^sup>*"
    

doc_class monitor_PP_control =
    cc_spec         ::    "cc_spec" <= "PP"
    rejects text_element
    accepts "\<lbrace>PP_report\<rbrace>\<^sup>*"

(* Put cc_term option in attribut
   
*)
end