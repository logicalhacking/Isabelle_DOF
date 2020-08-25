chapter\<open>Common Criteria Definitions\<close>

(*<<*)
theory CC_terminology

imports  "../technical_report/technical_report" 

begin

text\<open>We re-use the class @\<open>typ math_content\<close>, which provides also a framework for
semi-formal terminology, which we re-use by this definition.\<close>

doc_class concept_definition = "definition" +
      status        :: status <= "semiformal" 
      mcc           :: math_content_class <= "terminology"
      tag           :: string

type_synonym concept = concept_definition  

(*>>*)

section \<open>Terminology\<close>


subsection \<open>Terms and definitions common in the CC\<close>

Definition* [aas_def::concept, tag= "''adverse actions''"]
 \<open>actions performed by a threat agent on an asset\<close>

declare_reference*[toe_def::concept]

Definition* [assts_def::concept, tag="''assets''"]
 \<open>entities that the owner of the @{docitem toe_def} presumably places value upon \<close>

Definition* [asgn_def::concept, tag="''assignment''"]
\<open>the specification of an identified parameter in a component (of the CC) or requirement.\<close>

declare_reference*[sfrs_def::concept]

Definition* [assrc_def::concept, tag="''assurance''"]
  \<open>grounds for confidence that a @{docitem toe_def} meets the @{docitem sfrs_def}\<close>

Definition* [attptl_def::concept, tag="''attack potential''"] 
  \<open>measure of the effort to be expended in attacking a TOE, expressed in terms of 
   an attacker's expertise, resources and motivation\<close>

Definition* [argmt_def::concept, tag= "''augmentation''"] 
  \<open>addition of one or more requirement(s) to a package\<close>

Definition* [authdata_def::concept, tag="''authentication data''"]
  \<open>information used to verify the claimed identity of a user\<close>

Definition* [authusr_def::concept, tag = "''authorised user''"] 
\<open>@{docitem toe_def} user who may, in accordance with the @{docitem sfrs_def}, perform an operation\<close>

Definition* [bpp_def::concept, tag="''Base Protection Profile''"] 
\<open>Protection Profile used as a basis to build a Protection Profile Configuration\<close>

Definition* [cls_def::concept,tag="''class''"]
\<open>set of CC families that share a common focus\<close>

Definition* [cohrnt_def::concept,tag="''coherent''"] 
\<open>logically ordered and having discernible meaning For documentation, this addresses 
 both the actual text and the structure of the document, in terms of whether it is 
 understandable by its target audience.\<close>

Definition* [cmplt_def::concept, tag="''complete''"] 
\<open>property where all necessary parts of an entity have been provided
 In terms of documentation, this means that all relevant information is
 covered in the documentation, at such a level of detail that no further
 explanation is required at that level of abstraction.\<close>

Definition* [compnt_def::concept, tag="''component''"] 
 \<open>smallest selectable set of elements on which requirements may be based\<close>

Definition*[cap_def::concept, tag="''composed assurance package''"] 
\<open>assurance package consisting of requirements drawn from CC Part 3 
 (predominately from the ACO class), representing a point on the CC predefined 
 composition assurance scale\<close>

Definition* [cfrm_def::concept,tag="''confirm''"] 
\<open>declare that something has been reviewed in detail with an independent determination 
 of sufficiency

 The level of rigour required depends on the nature of the subject matter. This
 term is only applied to evaluator actions.\<close>

Definition* [cnnctvty_def::concept, tag="''connectivity''"]
\<open>property of the @{docitem toe_def} allowing interaction with IT entities external to the 
 @{docitem toe_def}

 This includes exchange of data by wire or by wireless means, over any
 distance in any environment or configuration.\<close>

Definition* [cnstnt_def::concept, tag="''consistent''"] 
\<open>relationship between two or more entities such that there are no apparent 
 contradictions between these entities\<close>

Definition* [cnt_vrb_def::concept, tag="''counter, verb''"] 
\<open>meet an attack where the impact of a particular threat is mitigated 
 but not necessarily eradicated\<close>

declare_reference*[st_def::concept]
declare_reference*[pp_def::concept]

Definition* [dmnst_conf_def::concept, tag="''demonstrable conformance''"] 
\<open>relation between an @{docitem st_def} and a @{docitem pp_def}, where the @{docitem st_def} 
 provides a solution which solves the generic security problem in the PP

The @{docitem pp_def} and the @{docitem st_def} may contain entirely different statements that discuss
different entities, use different concepts etc. Demonstrable conformance is
also suitable for a @{docitem toe_def} type where several similar @{docitem pp_def}s already exist, thus
allowing the ST author to claim conformance to these @{docitem pp_def}s simultaneously,
thereby saving work.\<close>

Definition* [dmstrt_def::concept, tag="''demonstrate''"] 
\<open>provide a conclusion gained by an analysis which is less rigorous than a “proof”\<close>

Definition* [dpndcy::concept, tag="''dependency''"] 
\<open>relationship between components such that if a requirement based on the depending 
 component is included in a @{docitem pp_def}, ST or package, a requirement based on 
 the component that is depended upon must normally also be included in the @{docitem pp_def}, 
 @{docitem st_def} or package\<close>

Definition* [dscrb_def::concept, tag="''describe''"] 
\<open>provide specific details of an entity\<close>

Definition* [dtrmn_def::concept, tag="''determine''"] 
\<open>affirm a particular conclusion based on independent analysis with the objective 
 of reaching a particular conclusion

 The usage of this term implies a truly independent analysis, usually in the
 absence of any previous analysis having been performed. Compare with the
 terms “confirm” or “verify” which imply that an analysis has already been
 performed which needs to be reviewed\<close>

Definition* [devenv_def::concept, tag="''development environment''"] 
\<open>environment in which the @{docitem toe_def} is developed\<close>

Definition* [elmnt_def::concept, tag="''element''"] 
\<open>indivisible statement of a security need\<close>

Definition* [ensr_def::concept, tag="''ensure''"] 
\<open>guarantee a strong causal relationship between an action and its consequences
 
 When this term is preceded by the word “help” it indicates that the
 consequence is not fully certain, on the basis of that action alone.\<close>

Definition* [eval_def::concept, tag="''evaluation''"] 
\<open>assessment of a @{docitem pp_def}, an @{docitem st_def} or a @{docitem toe_def}, 
 against defined criteria.\<close>

Definition* [eal_def::concept, tag= "''evaluation assurance level''"] 
\<open>set of assurance requirements drawn from CC Part 3, representing a point on the 
 CC predefined assurance scale, that form an assurance package\<close>

Definition* [eval_auth_def::concept, tag="''evaluation authority''"] 
\<open>body that sets the standards and monitors the quality of evaluations conducted by bodies within a specific community and
 implements the CC for that community by means of an evaluation scheme\<close>

Definition* [eval_schm_def::concept, tag="''evaluation scheme''"] 
\<open>administrative and regulatory framework under which the CC is applied by an 
 evaluation authority within a specific community\<close>

Definition* [exst_def::concept, tag="''exhaustive''"]
\<open>characteristic of a methodical approach taken to perform an
analysis or activity according to an unambiguous plan
This term is used in the CC with respect to conducting an analysis or other
activity. It is related to “systematic” but is considerably stronger, in that it
indicates not only that a methodical approach has been taken to perform the
analysis or activity according to an unambiguous plan, but that the plan that
was followed is sufficient to ensure that all possible avenues have been
exercised.\<close>

Definition* [expln_def::concept, tag="''explain''"] 
\<open> give argument accounting for the reason for taking a course of action
This term differs from both “describe” and “demonstrate”. It is intended to
answer the question “Why?” without actually attempting to argue that the
course of action that was taken was necessarily optimal.\<close>

Definition* [extn_def::concept, tag= "''extension''"] 
\<open>addition to an ST or PP of functional requirements not contained in CC 
 Part 2 and/or assurance requirements not contained in CC Part 3\<close>

Definition* [extnl_ent_def::concept, tag="''external entity''"] 
 \<open>human or IT entity possibly interacting with the TOE from outside of the TOE boundary\<close>

Definition* [fmly_def::concept, tag="''family''"] 
 \<open>set of components that share a similar goal but differ in emphasis or rigour\<close>

Definition* [fml_def::concept, tag="''formal''"] 
 \<open>expressed in a restricted syntax language with defined semantics
  based on well-established mathematical concepts \<close>

Definition* [gudn_doc_def::concept, tag="''guidance documentation''"] 
\<open>documentation that describes the delivery, preparation, operation, 
 management and/or use of the TOE\<close>

Definition* [ident_def::concept, tag="''identity''"]
\<open>representation uniquely identifying entities (e.g. a user, a process or a disk) 
 within the context of the TOE

 An example of such a representation is a string. For a human user, the
 representation can be the full or abbreviated name or a (still unique)
 pseudonym.\<close>

Definition* [infml_def::concept, tag="''informal''"] 
  \<open>expressed in natural language\<close>

Definition* [intr_tsf_trans_def::concept, tag ="''inter TSF transfers''"] 
  \<open>communicating data between the TOE and the security functionality of 
   other trusted IT products\<close>

Definition* [intl_com_chan_def::concept, tag ="''internal communication channel''"] 
  \<open>communication channel between separated parts of the TOE\<close>

Definition* [int_toe_trans::concept, tag="''internal TOE transfer''"] 
  \<open>communicating data between separated parts of the TOE\<close>

Definition* [inter_consist_def::concept, tag="''internally consistent''"] 
  \<open>no apparent contradictions exist between any aspects of an entity

   In terms of documentation, this means that there can be no statements within
   the documentation that can be taken to contradict each other.\<close>

Definition* [iter_def::concept, tag="''iteration''"] 
  \<open>use of the same component to express two or more distinct requirements\<close>

Definition* [jstfct_def::concept, tag="''justification''"] 
\<open>analysis leading to a conclusion “Justification” is more rigorous than a demonstration. 
This term requires significant rigour in terms of very carefully and thoroughly explaining every
step of a logical argument.\<close>

Definition* [objct_def::concept, tag="''object''"] 
\<open>passive entity in the TOE, that contains or receives information,
and upon which subjects perform operations\<close>

Definition* [op_cc_cmpnt_def::concept, tag ="''operation (on a component of the CC)''"] 
\<open>modification or repetition of a component
 Allowed operations on components are assignment, iteration, refinement and
 selection.\<close>

Definition* [op_obj_def::concept, tag= "''operation (on an object)''"] 
  \<open>specific type of action performed by a subject on an object\<close>

Definition* [op_env_def::concept, tag= "''operational environment''"] 
\<open>environment in which the TOE is operated\<close>

Definition* [org_sec_po_def::concept, tag="''organisational security policy''"] 
\<open>set of security rules, procedures, or guidelines for an organisation
 A policy may pertain to a specific operational environment.\<close>

Definition* [pckg_def::concept, tag="''package''"] 
\<open>named set of either security functional or security assurance requirements 
 An example of a package is “EAL 3”.\<close>

Definition* [pp_config_def::concept, tag="''Protection Profile Configuration''"] 
\<open>Protection Profile composed of Base Protection Profiles and Protection Profile Module\<close>

Definition* [pp_eval_def::concept, tag="''Protection Profile evaluation''"]
\<open> assessment of a PP against defined criteria \<close>

Definition* [pp_def::concept, tag="''Protection Profile''"] 
\<open>implementation-independent statement of security needs for a TOE type\<close>

Definition* [ppm_def::concept, tag="''Protection Profile Module''"] 
\<open>implementation-independent statement of security needs for a TOE type 
  complementary to one or more Base Protection Profiles\<close>

declare_reference*[tsf_def::concept]

Definition* [prv_def::concept, tag="''prove''"] 
\<open>show correspondence by formal analysis in its mathematical sense
 It is completely rigorous in all ways. Typically, “prove” is used when there is
 a desire to show correspondence between two @{docitem tsf_def} representations at a high
 level of rigour.\<close>

Definition* [ref_def::concept, tag="''refinement''"] 
\<open>addition of details to a component\<close>

Definition* [role_def::concept, tag="''role''"] 
\<open>predefined set of rules establishing the allowed interactions between
 a user and the @{docitem toe_def}\<close>

declare_reference*[sfp_def::concept]

Definition* [scrt_def::concept, tag="''secret''"]
\<open>information that must be known only to authorised users and/or the
 @{docitem tsf_def} in order to enforce a specific @{docitem sfp_def}\<close>

declare_reference*[sfr_def::concept]

Definition* [sec_st_def::concept, tag="''secure state''"] 
\<open>state in which the @{docitem tsf_def} data are consistent and the  @{docitem tsf_def} 
 continues correct enforcement of the  @{docitem sfr_def}s\<close>

Definition* [sec_att_def::concept, tag="''security attribute''"] 
\<open>property of subjects, users (including external IT products), objects, 
 information, sessions and/or resources that is used in defining the @{docitem sfr_def}s 
 and whose values are used in enforcing the @{docitem sfr_def}s\<close>

Definition* [sec_def::concept, tag="''security''"]
\<open>function policy set of rules describing specific security behaviour enforced 
 by the @{docitem tsf_def} and expressible as a set of @{docitem sfr_def}s\<close>

Definition* [sec_obj_def::concept, tag="''security objective''"] 
\<open>statement of an intent to counter identified threats and/or satisfy identified 
 organisation security policies and/or assumptions\<close>

Definition* [sec_prob_def::concept, tag ="''security problem''"] 
\<open>statement which in a formal manner defines the nature and scope of the security that 
the TOE is intended to address This statement consists of a combination of:
  \begin{itemize}
 \item threats to be countered by the TOE and its operational environment,
 \item the OSPs enforced by the TOE and its operational environment, and
 \item the assumptions that are upheld for the operational environment of the TOE.
 \end{itemize}\<close>

Definition* [sr_def::concept, tag="''security requirement''"] 
\<open>requirement, stated in a standardised language, which is meant to contribute 
 to achieving the security objectives for a TOE\<close>
text \<open>@{docitem toe_def}\<close>
Definition* [st_def::concept, tag="''Security Target''"] 
\<open>implementation-dependent statement of security needs for a specific identified @{docitem toe_def}\<close>

Definition* [slct_def::concept, tag="''selection''"] 
\<open>specification of one or more items from a list in a component\<close>

Definition* [smfrml_def::concept, tag="''semiformal''"] 
\<open>expressed in a restricted syntax language with defined semantics\<close>

Definition* [spcfy_def::concept, tag= "''specify''"] 
\<open>provide specific details about an entity in a rigorous and precise manner\<close>

Definition* [strct_conf_def::concept, tag="''strict conformance''"] 
\<open>hierarchical relationship between a PP and an ST where all the requirements in the 
 PP also exist in the ST
 
 This relation can be roughly defined as “the ST shall contain all statements
 that are in the PP, but may contain more”. Strict conformance is expected to
 be used for stringent requirements that are to be adhered to in a single
 manner. \<close>

Definition* [st_eval_def::concept, tag="''ST evaluation''"]
\<open>assessment of an ST against defined criteria\<close>

Definition* [subj_def::concept, tag="''subject''"]
\<open>active entity in the TOE that performs operations on objects\<close>

Definition* [toe_def::concept, tag= "''target of evaluation''"]
\<open>set of software, firmware and/or hardware possibly accompanied by guidance\<close>

Definition* [thrt_agnt_def::concept, tag="''threat agent''"] 
\<open>entity that can adversely act on assets\<close>

Definition* [toe_eval_def::concept, tag="''TOE evaluation''"] 
\<open>assessment of a TOE against defined criteria\<close>

Definition* [toe_res_def::concept, tag="''TOE resource''"] 
\<open>anything useable or consumable in the TOE\<close>

Definition* [toe_sf_def::concept, tag="''TOE security functionality''"] 
\<open>combined functionality of all hardware, software, and firmware of a TOE that must be relied upon for the correct
enforcement of the SFRs\<close>

Definition* [tr_vrb_def::concept, tag="''trace, verb''"] 
\<open>perform an informal correspondence analysis between two entities with only a 
 minimal level of rigour\<close>

Definition* [trnsfs_out_toe_def::concept, tag="''transfers outside of the TOE''"] 
\<open>TSF mediated communication of data to entities not under the control of the TSF\<close>

Definition* [transl_def::concept, tag= "''translation''"]
\<open> describes the process of describing security requirements in a
 standardised language.

use of the term translation in this context is not literal and does not imply
that every SFR expressed in standardised language can also be translated
back to the security objectives.\<close>

Definition* [trst_chan_def::concept, tag="''trusted channel''"] 
\<open>a means by which a TSF and another trusted IT product
 can communicate with necessary confidence\<close>

Definition* [trst_it_prod_def::concept, tag="''trusted IT product''"] 
\<open>IT product, other than the TOE, which has its security functional requirements administratively coordinated with the TOE
 and which is assumed to enforce its security functional requirements correctly
 An example of a trusted IT product would be one that has been separately
 evaluated.\<close>

Definition* [trst_path_def::concept, tag="''trusted path''"] 
\<open>means by which a user and a TSF can communicate with the necessary confidence\<close>

Definition* [tsf_data_def::concept, tag="''TSF data''"] 
\<open>data for the operation of the TOE upon which the enforcement of the SFR relies\<close>

Definition* [tsf_intrfc_def::concept, tag="''TSF interface''"] 
\<open>means by which external entities (or subjects in the TOE but outside of the TSF) 
 supply data to the TSF, receive data from the TSF and invoke services from the TSF\<close>

Definition* [usr_def::concept, tag="''user''"] \<open>see external entity\<close>

Definition* [usr_datat_def::concept, tag="''user data''"] 
\<open>data for the user, that does not affect the operation of the TSF\<close>

Definition* [vrfy_def::concept, tag="''verify''"] 
\<open>rigorously review in detail with an independent determination of
sufficiency
Also see “confirm”. This term has more rigorous connotations. The term
“verify” is used in the context of evaluator actions where an independent
effort is required of the evaluator.\<close>

Definition* [dev_def::concept, tag="''Developer''"]
\<open>who respond to actual or perceived consumer security requirements in 
 constructing a @{docitem toe_def}, reference this  CC_Part_3 
 when interpreting statements of assurance requirements and determining
 assurance approaches of @{docitem toe_def}s.\<close>

Definition*[evalu_def::concept, tag="'' Evaluator''"]
\<open>who use the assurance requirements defined in CC_Part_3 
 as mandatory statement of evaluation criteria when determining the assurance 
 of @{docitem toe_def}s and when evaluating @{docitem pp_def}s and @{docitem st_def}s.\<close>

end