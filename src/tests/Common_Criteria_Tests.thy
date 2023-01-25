theory Common_Criteria_Tests
  imports  "Isabelle_DOF.Common_Criteria"
begin
(*Example for the verification of a Protection Profile
  from the Common Criteria certification :

  Adress of the example :
  https://www.commoncriteriaportal.org/files/ppfiles/pp0088V2b_EP_AH_pdf.pdf

*)
open_monitor* [ex_PP_monitor1::monitor_PP_spec]
open_monitor* [ex_PP_monitor2::monitor_PP_control]
text*[ex_title:: title, 
    short_title = "Some ''DBMS PP Extended Package  Access History''"]\<open>
DBMS PP Extended Package – Access History\<close>

open_monitor* [ex_Intro_monitor::PP_introduction_monitor]
text*[ex_intro::PP_introduction]\<open>
INTRODUCTION TO THE DBMS PP EXTENDED PACKAGE
\<close>
text*[ex_identification::PP_reference, 
version = "''1.02''", 
sponsors = "[''DBMS Working Group / Technical Community'']", 
publication_date = "''23rd March, 2017''",
cc_title = "@{title \<open>ex_title\<close>}"]\<open>
DBMS PP Extended Package Identification
Title: DBMS PP Extended Package – Access History DBMS PP Extended Package Abbreviation: AH Sponsor: DBMS Working Group / Technical Community CC Version: Common Criteria (CC) Version 3.1 R4
EP Version: 1.02
Publication Date: 23rd March, 2017
Keywords: database management system, DBMS PP, DBMS, COTS, access history
\<close>
text*[ex_overview::PP_overview]\<open>
DBMS PP Extended Package Overview
The base DBMS PP Security Problem Definition does not include a security objective relating to access history.
While many organizations do not specify this objective as part of their security problem definition, this additional security objective may need to be included in the security problem definition by some organizations in order to support further mitigation of the threats of T.ACCESS_TSFDATA, T.IA_MASQUERADE and T.TSF_COMPROMISE. This is achieved by allowing trained users to review their access history in order to help identify unauthorized access attempts.
This extended package supplements the DBMS PP by adding the TOE Security Objective O.ACCESS-HISTORY and the security functional requirement supporting that objective.
\<close>
text*[ex_framework::PP_introduction_report]\<open>
DBMS PP Extended Package Framework
The DBMS PP Extended Package – Access History is part of the Database Management System Protection Profile framework defined in [DBMS PP] chapter 1.3. An ST author may optionally use this document specifying an extended package in addition to the DBMS base protection profile defined with [DBMS PP] chapters 3ff.
\<close>
text*[ex_structure::PP_introduction_report]\<open>
Structure of the Extended Package
This document is structured as follows:
• Chapter 1 provides the introduction into the DBMS PP extended package.
• Chapter 2 specifies the conformance claims for the DBMS PP extended package.
• Chapter 3 contains the security problem definition applicable to this DBMS PP extended package.
• Chapter 4 defines the objectives to be covered by TOEs that are conformant to this DBMS PP extended package.
• Chapter 5 contains the definition of extended components used in this DBMS PP extended package.
• Chapter 6 holds the security requirements definition for this DBMS PP extended package. database management system.
\<close>
text*[ex_references::PP_introduction_report]\<open>
References
The references given in the [DBMS PP] are also applicable to this document. The following references are also applicable to this document:
DBMS PP Protection Profile for Database Management Systems (Base Package) V 2.12
\<close>
text*[ex_documents_conventions::PP_introduction_report]\<open>
Document Conventions
The document convention explained in Chapter 1.4 of [DBMS PP] are applicable in this document.
\<close>
close_monitor*[ex_Intro_monitor]

open_monitor*[ex_Conformance_monitor::Conformance_monitor]
text*[ex_Conf_claims::Conformance]\<open>
CONFORMANCE CLAIMS
The following sections describe the conformance claims of the Database Management System Protection Profile (DBMS PP).
\<close>
text*[ex_Conf_with_CC::PP_Conformance_report]\<open>
Conformance with CC
This extended package does not augment the conformance claim of the DBMS PP base specified in [DBMS PP] chapter 3.
\<close>
text*[ex_EPCR::PP_Conformance_report]\<open>
Extended Package Conformance Rules
This extended package does not depend on other DBMS PP extended packages.
This package can only be claimed together with the DBMS PP base package, in the version defined in [DBMS PP].
This extended package does not conflict with any other DBMS PP extended package at the time of publication.
\<close>
close_monitor*[ex_Conformance_monitor]

open_monitor*[ex_SPD_monitor::SPD_monitor]
text*[ex_SPD::SPD]\<open>
SECURITY PROBLEM DEFINITION
The security problem definition of the DBMS PP Extended Package – Access History does not change the security problem definition of the DBMS PP base.
\<close>
(* text*[ex_error::text_element]\<open>
This instance is an example of the use of the reject clause by   \<^monitor_PP_control>\<open>PP_monitor2\<close>
\<close> *)
text*[ex_treats::Threats]\<open>
Threats
This extended package neither adds to nor alters the threats given in [DBMS PP].
\<close>
text*[ex_OSPs::OSPs]\<open>
Organizational Security Policies
This extended package neither adds to nor alters any organizational security policies given in [DBMS PP].
\<close>
text*[ex_Assumptions::Assumptions]\<open>
Assumptions
This extended package neither adds to nor alters the assumptions given in [DBMS PP].
\<close>
close_monitor*[ex_SPD_monitor]

open_monitor*[ex_SO_monitor::SO_monitor]
text*[ex_SO::SO]\<open>
SECURITY OBJECTIVES
This section identifies the additional security objectives of the TOE and its supporting environment met by this extended package.
These security objectives identify the responsibilities of the TOE and its environment in meeting the security problem definition (SPD).
\<close>
text*[ex_TOE_SO::SO_for_TOE]\<open>
TOE Security Objectives
This extended package specifies one additional security objective in addition to those given in [DBMS PP].
\<close>
text*[ex_OE_SO::SO_for_OE]\<open>
Operational Environment Security Objectives
This extended package neither adds to nor alters the operational environment security objectives given in [DBMS PP].
\<close>
text*[ex_R_for_SO::SOR]\<open>
Rationale for Security Objectives
The table below gives a summary of the policies, and threats relating to the TOE security objectives.
Security objectives coverage
Rationale for the Security objectives sufficiency
The table below gives the rationale for the TOE security objectives. In this extended package security objective O.ACCESS_HISTORY is supportive in reducing the threats T.ACCESS_TSFDATA, T.IA_MASQUERADE and T.TSF_COMPROMISE given in the base DBMS PP.
\<close>
close_monitor*[ex_SO_monitor]

open_monitor*[ex_ECD_monitor::ECD_monitor]
text*[ex_ESFR::ECD]\<open>
EXTENDED SECURITY FUNCTIONAL REQUIREMENTS
This extended package defines one extended SFR.
\<close>
text*[ex_ESFR_spe::PP_ECD_report]\<open>
Extended Security Functional Requirements Specified By This Extended Package
FTA_TAH_(EXT).1 TOE access information
FTA_TAH_(EXT).1 TOE access information provides the requirement for a TOE to make available information related to attempts to establish a session.
Component levelling
FTA_TAH_(EXT).1 is not hierarchical to any other components. Management: FTA_TAH_(EXT).1
There are no management activities foreseen.
Audit: FTA_TAH_(EXT).1
There are no auditable events foreseen.
FTA_TAH_(EXT).1 TOE access information
Hierarchical to: No other components.
Dependencies: No dependencies.
FTA_TAH_(EXT).1.1
Upon a session establishment attempt, the TSF shall store
a. the [date and time] of the session establishment attempt of the user.
b. the incremental count of successive unsuccessful session establishment attempt(s).
FTA_TAH_(EXT).1.2
Upon successful session establishment, the TSF shall allow the [date and time] of
a. the previous last successful session establishment, and
b. the last unsuccessful attempt to session establishment and the number of unsuccessful attempts since the previous last successful session establishment
to be retrieved by the user.
\<close>
text*[ex_R_for_ESFR::PP_ECD_report]\<open>
Rationale For The Extended Security Functional Requirement
The table below presents a rationale for the inclusion of the extended functional security requirements found in this extended package.
\<close>
close_monitor*[ex_ECD_monitor]

open_monitor*[ex_SR_monitor::SR_monitor]
text*[ex_SR::SR]\<open>
SECURITY REQUIREMENTS
\<close>
text*[ex_ASFR::SFR]\<open>
Additional Security Functional Requirements to The Base DBMS PP
This section defines the functional requirements for the TOE that are amended or specified by this extended package.
Functional requirements in this extended package were drawn directly from Part 2 of the CC [1b], or were based on Part 2 of the CC, including the use of extended components. These requirements are relevant to supporting the secure operation of the TOE.
TOE Access (FTA)
FTA_TAH_(EXT).1 TOE access information FTA_TAH_(EXT).1.1
Upon a session establishment attempt, the TSF shall store
a. the [date and time] of the session establishment attempt of the user.
b. the incremental count of successive unsuccessful session establishment attempt(s).
FTA_TAH_(EXT).1.2
Upon successful session establishment, the TSF shall allow the [date and time] of
a. the previous last successful session establishment, and
b. the last unsuccessful attempt to session establishment and the number of unsuccessful attempts since the previous last successful session establishment
to be retrieved by the user.
\<close>
text*[ex_SFRR::SFR]\<open>
Security Functional Requirements Refined from The Base DBMS PP
Security Audit (FAU)
FAU_GEN.1 Audit data generation
\<close>
text*[ex_R_for_ASFR::SFR]\<open>
Rationale For The Additional TOE Security Functional Requirements
The following table provides the rationale for the selection of the security functional requirements. It traces each TOE security objective to the identified security functional requirements.
\<close>
text*[ex_R_for_all_SFRD::SFR]\<open>
Rationale for Satisfying All Security Functional Requirement Dependencies
This extended package does not contain any additional or amended SFRs that have dependencies.
\<close>
text*[ex_::SAR]\<open>
Security Assurance Requirements
This extended package neither adds to nor alters the security assurance requirements given in [DBMS PP].
\<close>
close_monitor*[ex_SR_monitor]

close_monitor*[ex_PP_monitor2]
close_monitor*[ex_PP_monitor1]


end