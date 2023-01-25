theory Common_Criteria_Tests
  imports  "Isabelle_DOF.Common_Criteria"
begin
(*Example for the verification of a Protection Profile
  from the Common Criteria certification :

  Adress of the example :
  https://www.commoncriteriaportal.org/files/ppfiles/pp0088V2b_EP_AH_pdf.pdf

*)
open_monitor* [PP_monitor1::monitor_PP_spec]
open_monitor* [PP_monitor2::monitor_PP_control]
text*[PP_title:: title, 
    short_title = "Some ''DBMS PP Extended Package  Access History''"]\<open>
DBMS PP Extended Package – Access History\<close>
open_monitor* [Intro_monitor::PP_introduction_monitor]
text*[ex_intro::PP_introduction]\<open>
INTRODUCTION TO THE DBMS PP EXTENDED PACKAGE
\<close>
text*[ex_identification::PP_reference, 
version = "''1.02''", 
sponsors = "[''DBMS Working Group / Technical Community'']", 
publication_date = "''23rd March, 2017''",
cc_title = "@{title \<open>PP_title\<close>}"]\<open>
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
close_monitor*[Intro_monitor]
open_monitor*[Conformance_monitor::Conformance_monitor]
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
close_monitor*[Conformance_monitor]
open_monitor*[SPD_monitor::SPD_monitor]
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
close_monitor*[SPD_monitor]
close_monitor*[PP_monitor2]
close_monitor*[PP_monitor1]


end