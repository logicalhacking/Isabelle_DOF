(*************************************************************************
 * Copyright (C) 
 *               2019-2022 The University of Exeter 
 *               2019-2022 The University of Paris-Saclay
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

chapter\<open>Common Criteria\<close>
section\<open>Terminology\<close>

(*<<*)
theory CC_terminology

imports  
"Isabelle_DOF.technical_report" 

begin

define_ontology "DOF-CC_terminology.sty" "CC"

(*>>*)
text\<open>We re-use the class @\<open>typ math_content\<close>, which provides also a framework for
semi-formal terminology, which we re-use by this definition.\<close>

doc_class concept_definition = math_content +
      status        :: status <= "semiformal" 
      mcc           :: math_content_class <= "terminology"
      tag           :: string
      short_tag    :: "string option" <= "None"

text\<open>The \<^verbatim>\<open>short_tag\<close>, if set, is used in the presentation directly.\<close>

type_synonym concept = concept_definition  

declare[[ Definition_default_class="concept_definition"]]



subsection \<open>Terminology\<close>


subsubsection \<open>Terms and definitions common in the CC\<close>

Definition* [aas_def, tag= "''adverse actions''"]
 \<open>actions performed by a threat agent on an asset\<close>

declare_reference*[toeDef]

Definition* [assts_def, tag="''assets''"]
 \<open>entities that the owner of the @{docitem (unchecked) toeDef} presumably places value upon \<close>

Definition* [asgn_def, tag="''assignment''"]
\<open>the specification of an identified parameter in a component (of the CC) or requirement.\<close>

declare_reference*[sfrs_def]

Definition* [assrc_def, tag="''assurance''"]
  \<open>grounds for confidence that a @{docitem (unchecked) toeDef}
   meets the @{docitem (unchecked) sfrs_def}\<close>

Definition* [attptl_def, tag="''attack potential''"] 
  \<open>measure of the effort to be expended in attacking a TOE, expressed in terms of 
   an attacker's expertise, resources and motivation\<close>

Definition* [argmt_def, tag= "''augmentation''"] 
  \<open>addition of one or more requirement(s) to a package\<close>

Definition* [authdata_def, tag="''authentication data''"]
  \<open>information used to verify the claimed identity of a user\<close>

Definition* [authusr_def, tag = "''authorised user''"] 
\<open>@{docitem (unchecked) toeDef} user who may,
 in accordance with the @{docitem (unchecked) sfrs_def}, perform an operation\<close>

Definition* [bppDef, tag="''Base Protection Profile''"] 
\<open>Protection Profile used as a basis to build a Protection Profile Configuration\<close>

Definition* [cls_def,tag="''class''"]
\<open>set of CC families that share a common focus\<close>

Definition* [cohrnt_def,tag="''coherent''"] 
\<open>logically ordered and having discernible meaning For documentation, this addresses 
 both the actual text and the structure of the document, in terms of whether it is 
 understandable by its target audience.\<close>

Definition* [cmplt_def, tag="''complete''"] 
\<open>property where all necessary parts of an entity have been provided
 In terms of documentation, this means that all relevant information is
 covered in the documentation, at such a level of detail that no further
 explanation is required at that level of abstraction.\<close>

Definition* [compnt_def, tag="''component''"] 
 \<open>smallest selectable set of elements on which requirements may be based\<close>

Definition*[cap_def, tag="''composed assurance package''"] 
\<open>assurance package consisting of requirements drawn from CC Part 3 
 (predominately from the ACO class), representing a point on the CC predefined 
 composition assurance scale\<close>

Definition* [cfrm_def,tag="''confirm''"] 
\<open>declare that something has been reviewed in detail with an independent determination 
 of sufficiency

 The level of rigour required depends on the nature of the subject matter. This
 term is only applied to evaluator actions.\<close>

Definition* [cnnctvty_def, tag="''connectivity''"]
\<open>property of the @{docitem (unchecked) toeDef} allowing interaction with IT entities external to the 
 @{docitem (unchecked) toeDef}

 This includes exchange of data by wire or by wireless means, over any
 distance in any environment or configuration.\<close>

Definition* [cnstnt_def, tag="''consistent''"] 
\<open>relationship between two or more entities such that there are no apparent 
 contradictions between these entities\<close>

Definition* [cnt_vrb_def, tag="''counter, verb''"] 
\<open>meet an attack where the impact of a particular threat is mitigated 
 but not necessarily eradicated\<close>

declare_reference*[stDef]
declare_reference*[ppDef]

Definition* [dmnst_conf_def, tag="''demonstrable conformance''"] 
\<open>relation between an @{docitem (unchecked) stDef} and a @{docitem (unchecked) ppDef},
 where the @{docitem (unchecked) stDef} 
 provides a solution which solves the generic security problem in the PP

The @{docitem (unchecked) ppDef} and the @{docitem (unchecked) stDef} may contain
entirely different statements that discuss
different entities, use different concepts etc. Demonstrable conformance is
also suitable for a @{docitem (unchecked) toeDef} type
where several similar @{docitem (unchecked) ppDef}s already exist, thus
allowing the ST author to claim conformance to these @{docitem (unchecked) ppDef}s simultaneously,
thereby saving work.\<close>

Definition* [dmstrt_def, tag="''demonstrate''"] 
\<open>provide a conclusion gained by an analysis which is less rigorous than a “proof”\<close>

Definition* [dpndcy, tag="''dependency''"] 
\<open>relationship between components such that if a requirement based on the depending 
 component is included in a @{docitem (unchecked) ppDef}, ST or package, a requirement based on 
 the component that is depended upon must normally also be included
 in the @{docitem (unchecked) ppDef}, 
 @{docitem (unchecked) stDef} or package\<close>

Definition* [dscrb_def, tag="''describe''"] 
\<open>provide specific details of an entity\<close>

Definition* [dtrmn_def, tag="''determine''"] 
\<open>affirm a particular conclusion based on independent analysis with the objective 
 of reaching a particular conclusion

 The usage of this term implies a truly independent analysis, usually in the
 absence of any previous analysis having been performed. Compare with the
 terms “confirm” or “verify” which imply that an analysis has already been
 performed which needs to be reviewed\<close>

Definition* [devenv_def, tag="''development environment''"] 
\<open>environment in which the @{docitem (unchecked) toeDef} is developed\<close>

Definition* [elmnt_def, tag="''element''"] 
\<open>indivisible statement of a security need\<close>

Definition* [ensr_def, tag="''ensure''"] 
\<open>guarantee a strong causal relationship between an action and its consequences
 
 When this term is preceded by the word “help” it indicates that the
 consequence is not fully certain, on the basis of that action alone.\<close>

Definition* [eval_def, tag="''evaluation''"] 
\<open>assessment of a @{docitem (unchecked) ppDef}, an @{docitem (unchecked) stDef}
 or a @{docitem (unchecked) toeDef}, against defined criteria.\<close>

Definition* [eal_def, tag= "''evaluation assurance level''"] 
\<open>set of assurance requirements drawn from CC Part 3, representing a point on the 
 CC predefined assurance scale, that form an assurance package\<close>

Definition* [eval_auth_def, tag="''evaluation authority''"] 
\<open>body that sets the standards and monitors the quality of evaluations conducted 
 by bodies within a specific community and implements the CC for that community 
 by means of an evaluation scheme\<close>

Definition* [eval_schm_def, tag="''evaluation scheme''"] 
\<open>administrative and regulatory framework under which the CC is applied by an 
 evaluation authority within a specific community\<close>

Definition* [exstDef, tag="''exhaustive''"]
\<open>characteristic of a methodical approach taken to perform an
analysis or activity according to an unambiguous plan
This term is used in the CC with respect to conducting an analysis or other
activity. It is related to ``systematic'' but is considerably stronger, in that it
indicates not only that a methodical approach has been taken to perform the
analysis or activity according to an unambiguous plan, but that the plan that
was followed is sufficient to ensure that all possible avenues have been
exercised.\<close>

Definition* [expln_def, tag="''explain''"] 
\<open> give argument accounting for the reason for taking a course of action
This term differs from both “describe” and “demonstrate”. It is intended to
answer the question “Why?” without actually attempting to argue that the
course of action that was taken was necessarily optimal.\<close>

Definition* [extn_def, tag= "''extension''"] 
\<open>addition to an ST or PP of functional requirements not contained in CC 
 Part 2 and/or assurance requirements not contained in CC Part 3\<close>

Definition* [extnl_ent_def, tag="''external entity''"] 
 \<open>human or IT entity possibly interacting with the TOE from outside of the TOE boundary\<close>

Definition* [fmly_def, tag="''family''"] 
 \<open>set of components that share a similar goal but differ in emphasis or rigour\<close>

Definition* [fml_def, tag="''formal''"] 
 \<open>expressed in a restricted syntax language with defined semantics
  based on well-established mathematical concepts \<close>

Definition* [gudn_doc_def, tag="''guidance documentation''"] 
\<open>documentation that describes the delivery, preparation, operation, 
 management and/or use of the TOE\<close>

Definition* [ident_def, tag="''identity''"]
\<open>representation uniquely identifying entities (e.g. a user, a process or a disk) 
 within the context of the TOE

 An example of such a representation is a string. For a human user, the
 representation can be the full or abbreviated name or a (still unique)
 pseudonym.\<close>

Definition* [infml_def, tag="''informal''"] 
  \<open>expressed in natural language\<close>

Definition* [intr_tsf_trans_def, tag ="''inter TSF transfers''"] 
  \<open>communicating data between the TOE and the security functionality of 
   other trusted IT products\<close>

Definition* [intl_com_chan_def, tag ="''internal communication channel''"] 
  \<open>communication channel between separated parts of the TOE\<close>

Definition* [int_toe_trans, tag="''internal TOE transfer''"] 
  \<open>communicating data between separated parts of the TOE\<close>

Definition* [inter_consistDef, tag="''internally consistent''"] 
  \<open>no apparent contradictions exist between any aspects of an entity

   In terms of documentation, this means that there can be no statements within
   the documentation that can be taken to contradict each other.\<close>

Definition* [iter_def, tag="''iteration''"] 
  \<open>use of the same component to express two or more distinct requirements\<close>

Definition* [jstfct_def, tag="''justification''"] 
\<open>analysis leading to a conclusion “Justification” is more rigorous than a demonstration. 
This term requires significant rigour in terms of very carefully and thoroughly explaining every
step of a logical argument.\<close>

Definition* [objct_def, tag="''object''"] 
\<open>passive entity in the TOE, that contains or receives information,
and upon which subjects perform operations\<close>

Definition* [op_cc_cmpnt_def, tag ="''operation (on a component of the CC)''"] 
\<open>modification or repetition of a component
 Allowed operations on components are assignment, iteration, refinement and
 selection.\<close>

Definition* [op_obj_def, tag= "''operation (on an object)''"] 
  \<open>specific type of action performed by a subject on an object\<close>

Definition* [op_env_def, tag= "''operational environment''"] 
\<open>environment in which the TOE is operated\<close>

Definition* [org_sec_po_def, tag="''organisational security policy''"] 
\<open>set of security rules, procedures, or guidelines for an organisation
 A policy may pertain to a specific operational environment.\<close>

Definition* [pckg_def, tag="''package''"] 
\<open>named set of either security functional or security assurance requirements 
 An example of a package is ``EAL 3''.\<close>

Definition* [pp_config_def, tag="''Protection Profile Configuration''"] 
\<open>Protection Profile composed of Base Protection Profiles and Protection Profile Module\<close>

Definition* [pp_eval_def, tag="''Protection Profile evaluation''"]
\<open> assessment of a PP against defined criteria \<close>

Definition* [ppDef, tag="''Protection Profile''"] 
\<open>implementation-independent statement of security needs for a TOE type\<close>

Definition* [ppm_def, tag="''Protection Profile Module''"] 
\<open>implementation-independent statement of security needs for a TOE type 
  complementary to one or more Base Protection Profiles\<close>

declare_reference*[tsf_def]

Definition* [prv_def, tag="''prove''"] 
\<open>show correspondence by formal analysis in its mathematical sense
 It is completely rigorous in all ways. Typically, “prove” is used when there is
 a desire to show correspondence between two @{docitem (unchecked) tsf_def}
 representations at a high level of rigour.\<close>

Definition* [ref_def, tag="''refinement''"] 
\<open>addition of details to a component\<close>

Definition* [role_def, tag="''role''"] 
\<open>predefined set of rules establishing the allowed interactions between
 a user and the @{docitem (unchecked) toeDef}\<close>

declare_reference*[sfp_def]

Definition* [scrt_def, tag="''secret''"]
\<open>information that must be known only to authorised users and/or the
 @{docitem (unchecked) tsf_def} in order to enforce a specific @{docitem (unchecked) sfp_def}\<close>

declare_reference*[sfr_def]

Definition* [sec_stDef, tag="''secure state''"] 
\<open>state in which the @{docitem (unchecked) tsf_def} data are consistent
  and the  @{docitem (unchecked) tsf_def} 
 continues correct enforcement of the  @{docitem (unchecked) sfr_def}s\<close>

Definition* [sec_att_def, tag="''security attribute''"] 
\<open>property of subjects, users (including external IT products), objects, 
 information, sessions and/or resources that is used in defining the @{docitem (unchecked) sfr_def}s 
 and whose values are used in enforcing the @{docitem (unchecked) sfr_def}s\<close>

Definition* [sec_def, tag="''security''"]
\<open>function policy set of rules describing specific security behaviour enforced 
 by the @{docitem (unchecked) tsf_def} and expressible as a set of @{docitem (unchecked) sfr_def}s\<close>

Definition* [sec_obj_def, tag="''security objective''"] 
\<open>statement of an intent to counter identified threats and/or satisfy identified 
 organisation security policies and/or assumptions\<close>

Definition* [sec_prob_def, tag ="''security problem''"] 
\<open>statement which in a formal manner defines the nature and scope of the security that 
the TOE is intended to address This statement consists of a combination of:
\begin{itemize}
\item threats to be countered by the TOE and its operational environment,
\item the OSPs enforced by the TOE and its operational environment, and
\item the assumptions that are upheld for the operational environment of the TOE.
\end{itemize}\<close>

Definition* [sr_def, tag="''security requirement''", short_tag="Some(''SR'')"] 
\<open>requirement, stated in a standardised language, which is meant to contribute 
 to achieving the security objectives for a TOE\<close>
(*<*)
text \<open>@{docitem  (unchecked) toeDef}\<close>
(*>*)
Definition* [st, tag="''Security Target''", short_tag="Some(''ST'')"]
\<open>implementation-dependent statement of security needs for a specific identified
 @{docitem (unchecked) toeDef}\<close>

Definition* [slct_def, tag="''selection''"] 
\<open>specification of one or more items from a list in a component\<close>

Definition* [smfrml_def, tag="''semiformal''"] 
\<open>expressed in a restricted syntax language with defined semantics\<close>

Definition* [spcfy_def, tag= "''specify''"] 
\<open>provide specific details about an entity in a rigorous and precise manner\<close>

Definition* [strct_conf_def, tag="''strict conformance''"] 
\<open>hierarchical relationship between a PP and an ST where all the requirements in the 
 PP also exist in the ST
 
 This relation can be roughly defined as “the ST shall contain all statements
 that are in the PP, but may contain more”. Strict conformance is expected to
 be used for stringent requirements that are to be adhered to in a single
 manner. \<close>

Definition* [st_eval_def, tag="''ST evaluation''"]
\<open>assessment of an ST against defined criteria\<close>

Definition* [subj_def, tag="''subject''"]
\<open>active entity in the TOE that performs operations on objects\<close>

Definition* [toe, tag= "''target of evaluation''"]
\<open>set of software, firmware and/or hardware possibly accompanied by guidance\<close>

Definition* [thrt_agnt_def, tag="''threat agent''"] 
\<open>entity that can adversely act on assets\<close>

Definition* [toe_eval_def, tag="''TOE evaluation''"] 
\<open>assessment of a TOE against defined criteria\<close>

Definition* [toe_res_def, tag="''TOE resource''"] 
\<open>anything useable or consumable in the TOE\<close>

Definition* [toe_sf_def, tag="''TOE security functionality''", short_tag= "Some(''TSF'')"] 
\<open>combined functionality of all hardware, software, and firmware of a TOE that must be relied upon 
 for the correct enforcement of the @{docitem  (unchecked) sfr_def}s\<close>

Definition* [tr_vrb_def, tag="''trace, verb''"] 
\<open>perform an informal correspondence analysis between two entities with only a 
 minimal level of rigour\<close>

Definition* [trnsfs_out_toeDef, tag="''transfers outside of the TOE''"] 
\<open>TSF mediated communication of data to entities not under the control of the TSF\<close>

Definition* [transl_def, tag= "''translation''"]
\<open> describes the process of describing security requirements in a
 standardised language.

use of the term translation in this context is not literal and does not imply
that every SFR expressed in standardised language can also be translated
back to the security objectives.\<close>

Definition* [trst_chan_def, tag="''trusted channel''"] 
\<open>a means by which a TSF and another trusted IT product
 can communicate with necessary confidence\<close>

Definition* [trst_it_prod_def, tag="''trusted IT product''"] 
\<open>IT product, other than the TOE, which has its security functional requirements administratively coordinated with the TOE
 and which is assumed to enforce its security functional requirements correctly
 An example of a trusted IT product would be one that has been separately
 evaluated.\<close>

Definition* [trst_path_def, tag="''trusted path''"] 
\<open>means by which a user and a TSF can communicate with the necessary confidence\<close>

Definition* [tsf_data_def, tag="''TSF data''"] 
\<open>data for the operation of the TOE upon which the enforcement of the SFR relies\<close>

Definition* [tsf_intrfc_def, tag="''TSF interface''"] 
\<open>means by which external entities (or subjects in the TOE but outside of the TSF) 
 supply data to the TSF, receive data from the TSF and invoke services from the TSF\<close>

Definition* [usr_def, tag="''user''"] \<open>see external entity\<close>

Definition* [usr_datat_def, tag="''user data''"] 
\<open>data for the user, that does not affect the operation of the TSF\<close>

Definition* [vrfy_def, tag="''verify''"] 
\<open>rigorously review in detail with an independent determination of
sufficiency
Also see “confirm”. This term has more rigorous connotations. The term
“verify” is used in the context of evaluator actions where an independent
effort is required of the evaluator.\<close>

Definition* [dev_def, tag="''Developer''"]
\<open>who respond to actual or perceived consumer security requirements in 
 constructing a @{docitem  (unchecked) toeDef}, reference this  CC\_Part\_3 
 when interpreting statements of assurance requirements and determining
 assurance approaches of @{docitem toe}s.\<close>

Definition*[evalu_def, tag="'' Evaluator''"]
\<open>who use the assurance requirements defined in CC\_Part\_3 
 as mandatory statement of evaluation criteria when determining the assurance 
 of @{docitem  (unchecked) toeDef}s and when evaluating @{docitem ppDef}s
 and @{docitem  (unchecked) stDef}s.\<close>


Definition*[toeDef] \<open>\<close>
Definition*[sfrs_def] \<open>\<close>
Definition*[sfr_def] \<open>\<close>
Definition*[stDef] \<open>\<close>
Definition*[sfp_def] \<open>\<close>
Definition*[tsf_def] \<open>\<close>

end
