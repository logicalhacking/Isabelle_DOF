theory PikeOS_ST (*Security Target *)

imports "../../../src/ontologies/CC_v3.1_R5/CC_v3_1_R5"
        (*  Isabelle_DOF.CommonCriteria_15408  *)

begin 

section \<open>ST PikeOS\<close>

open_monitor*[stpkos::ST_MNT]
section*[pkosstintrosec::st_ref_cls]\<open> ST Introduction \<close>
open_monitor*[PikosIntro::ST_INTRO_MNT]
subsection*[pkosstrefsubsec::st_ref_cls]\<open> ST Reference \<close>

text*[pkosstref::st_ref_cls, title="''PikeOS Security Target''", st_version ="(0,4,5)",
      authors= "[]", st_date= "''29072020''"]
\<open>This document is the @{docitem st_def} for the Common Criteria evaluation of PikeOS. 
 It complies with the Common Criteria for Information Technology Security Evaluation 
 Version 3.1 Revision 4.\<close>

subsection*[pkossttoerefsubsec::st_ref_cls]\<open> TOE Reference \<close>

text*[pkostoeref::toe_ref_cls, dev_name="''''", toe_name="''PikeOS''",
      toe_version= "(0,3,4)", prod_name="Some ''S3725''"]
\<open>The @{docitem toe_def} is the operating system PikeOS version 3.4 
   running on the microprocessor family x86 hosting different applications. 
   The @{docitem toe_def} is referenced as PikeOS 3.4 base
   product build S3725 for Linux and Windows development host with PikeOS 3.4
   Certification Kit build S4250 and PikeOS 3.4 Common Criteria Kit build S4388.\<close>

subsection*[pkossttoeovrvwsubsec::st_ref_cls]\<open> TOE Overview \<close>
text*[pkosovrw1::toe_ovrw_cls]\<open>The @{definition \<open>toe\<close> } is a special kind of operating 
system, that allows to effectively separate
different applications running on the same platform from each other. The TOE can host
user applications that can also be operating systems. User applications can also be
malicious, and even in that case the TOE ensures that malicious user applications are
harming neither the TOE nor other applications in other partitions. The TOE will be
installed and run on a hardware platform (e.g. embedded systems).
The TOE is intended to be used as a component (the separation kernel) in MILS systems.
MILS (Multiple Independent Levels of Security) systems are explained in .
The TOE controls usage of memory, devices, processors, and communication channels
to ensure complete separation of user applications and to prevent unexpected
interference between user applications. The TOE enforces restrictions on the
communication between the separated user applications as specified by the configuration
data.

The major security services provided by the TOE are:

Separation in space of applications hosted in different partitions from each other
and from the PikeOS operating system according to the configuration data by
Page 3 of 44using the underlying hardware,
2086 Separation in time of applications hosted in different partitions from each other
and from the PikeOS operating system according to the configuration data,
   Provision and management of communication objects,
 Management of and access to the TOE and TOE data,
 PikeOS operating system self-protection and accuracy of security functionality,
 Generation and treatment of audit data according to the configuration data.\<close>

text*[pkosovrw2::toe_ovrw_cls, toe_type="''OS separation kernel''"]
\<open>The TOE is a special kind of operating system providing a separation kernel with real-
time support.
The typical life cycle phases for this TOE type are development (source code
development), manufacturing (compilation to binary), system integration (by the system
integrator), installation (by the system operator), and finally, operational use (by the
system operator). Operational use of the TOE is explicitly in the focus of this ST. A
security evaluation/certification according to the assurance package chosen in this ST
(see Section 2.3 “Package Claim” below) involves all these life cycle phases.\<close>
text*[pkosdesc::toe_desc_cls]\<open>\<close>
close_monitor*[PikosIntro]

open_monitor*[PikosCCLM::CONF_CLAIMS_MNT]

close_monitor*[PikosCCLM]

open_monitor*[PikosSPD::SEC_PROB_DEF_MNT]

close_monitor*[PikosSPD]

open_monitor*[PikosSO::SEC_OBJ_MNT]

close_monitor*[PikosSO]



open_monitor*[PikosSR::SEC_REQ_MNT]

close_monitor*[PikosSR]

close_monitor*[stpkos]
end