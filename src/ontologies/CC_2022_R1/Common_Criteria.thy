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
  imports  "Isabelle_DOF.technical_report"
begin


text\<open>We re-use the class \<^typ>\<open>math_content\<close>, which provides also a framework for
semi-formal "math-alike" terminology, which we re-use by this definition.\<close>

doc_class semi_formal_content = math_content +
      status        :: status <= "semiformal" 
      mcc           :: math_content_class 



type_synonym sfc = semi_formal_content  

doc_class cc_term = semi_formal_content + 
      mcc          :: math_content_class <= "terminology"

type_synonym common_criteria_term = cc_term 

text\<open> in the following, all \<^theory_text>\<open>Definition*\<close> statements are interpreted as 
     \<^doc_class>\<open>cc_term\<close>s, i.e. semi-formal teminological definitions.\<close>

declare[[ Definition_default_class="cc_term"]]


text\<open> Excerpt of the BE EN 50128:2011, page 22. \<close>

section\<open>Terms and Definitions\<close>

declare_reference*[evaluator]
declare_reference*[developer]
Definition*[action]
\<open>documented activity of the @{cc_term (unchecked) \<open>evaluator\<close>}
 or  @{cc_term (unchecked) \<open>developer\<close>}\<close>

declare_reference*[entity]
declare_reference*[TSF]
Definition*[admministrator]
\<open> @{cc_term (unchecked) \<open>entity\<close>} that has a level of trust with respect to 
all policies implemented by the  @{cc_term (unchecked) \<open>TSF\<close>}\<close>

Definition*[API, short_name="''application programming interface''"]
\<open>\<close>

declare_reference*[threat_agent]
declare_reference*[asset]
Definition*[adverse_action]
\<open> \<^cc_term>\<open>action\<close> performed by a @{cc_term (unchecked) \<open>threat_agent\<close>} 
on an @{cc_term (unchecked) \<open>asset\<close>}\<close>

declare_reference*[TOE]
Definition*[asset]
\<open>  @{cc_term (unchecked) \<open>entity\<close>}  that the owner of 
the  @{cc_term (unchecked) \<open>TOE\<close>} presumably places value on\<close>

Definition*[assignement]
\<open>specification of an identified parameter in a functional or assurance component\<close>

declare_reference*[SFR]
Definition*[assurance]
\<open>grounds for confidence that a @{cc_term (unchecked) \<open>TOE\<close>} meets
the security functional requirements @{cc_term (unchecked) \<open>SFR\<close>}s \<close>

declare_reference*[SAR]
Definition*[AP, short_name="''assurance package''"]
\<open>named set of  @{cc_term (unchecked) \<open>SAR\<close>}s\<close>

Definition*[attack_potential]
\<open>measure of the effort needed to exploit a vulnerability in a @{cc_term (unchecked) \<open>TOE\<close>} \<close>

Definition*[attack_surface]
\<open>set of logical or physical interfaces to a target, consisting of points
 through which access to the target and its functions may be attempted\<close>

Definition*[augmentation]
\<open>addition of one or more requirements to a package\<close>

Definition*[autorized_user]
\<open> @{cc_term (unchecked) \<open>entity\<close>} who may, in accordance with the @{cc_term (unchecked) \<open>SFR\<close>}s,
 perform an operation on the  @{cc_term (unchecked) \<open>TOE\<close>}\<close>

declare_reference*[independent_entity]
declare_reference*[dependent_component]
Definition*[base_component]
\<open> @{cc_term (unchecked) \<open>independent_entity\<close>} in a multi-component product that provides
 services and resources to one or more  @{cc_term (unchecked) \<open>dependent_component\<close>}(s)\<close>

declare_reference*[PP]
declare_reference*[PP_module]
declare_reference*[PP_module_base]
declare_reference*[PP_config]
Definition*[base_PP, short_name="''base Protection Profile''"]
\<open> @{cc_term (unchecked) \<open>PP\<close>} specified in a  @{cc_term (unchecked) \<open>PP_module\<close>}, 
as part of that @{cc_term (unchecked) \<open>PP_module\<close>}’s @{cc_term (unchecked) \<open>PP_module_base\<close>},
used as a basis to build a @{cc_term (unchecked) \<open>PP_config\<close>}\<close>

Definition*[base_PP_module, short_name="''base PP-Module''"]
\<open>@{cc_term (unchecked) \<open>PP_module\<close>} specified in a different @{cc_term (unchecked) \<open>PP_module\<close>}, 
as part of that @{cc_term (unchecked) \<open>PP_module\<close>}’s  @{cc_term (unchecked) \<open>PP_module_base\<close>}, 
used as a basis to build a @{cc_term (unchecked) \<open>PP_config\<close>}\<close>

Definition*[base_TOE, short_name="''base target of evaluation''"]
\<open>@{cc_term (unchecked) \<open>base_component\<close>} which is itself the subject of an evaluation\<close>

Definition*[class_cc, short_name="''class''"]
\<open>〈taxonomy〉 set of families that share a common focus\<close>

Definition*[CD, short_name="''compact disk''"]
\<open>\<close>

Definition*[component]
\<open>〈taxonomy〉 smallest selectable set of elements on which requirements may be based OU
  <composition> @{cc_term (unchecked) \<open>entity\<close>} which provides resources and services in a product\<close>

declare_reference*[composed_TOE]
Definition*[component_TOE, short_name="''component target of evaluation''"]
\<open>(evaluated) @{cc_term (unchecked) \<open>TOE\<close>}
 that is a component of another @{cc_term (unchecked) \<open>composed_TOE\<close>}\<close>

Definition*[CAP, short_name="''composition assurance package''"]
\<open> \<^cc_term>\<open>AP\<close> consisting of components drawn predominately from the ACO \<^cc_term>\<open>class_cc\<close>,
 representing a point on the pre-defined scale for composition assurance\<close>

Definition*[composed_TOE, short_name="''composed target of evaluation''"]
\<open>@{cc_term (unchecked) \<open>TOE\<close>} comprising solely two or more separately identified components
 with a security relationship between their @{cc_term (unchecked) \<open>TSF\<close>}\<close>

Definition*[composed_evaluation, short_name="''composed evaluation''"]
\<open>evaluation of a \<^cc_term>\<open>composed_TOE\<close> using the specific evaluation technique applicable to \<^cc_term>\<open>composed_TOE\<close>s\<close>

declare_reference*[composite_product]
declare_reference*[composite_TOE]
Definition*[composite_evaluation, short_name="''composite evaluation''"]
\<open>evaluation of a @{cc_term (unchecked) \<open>composite_TOE\<close>}/@{cc_term (unchecked) \<open>composite_product\<close>}
 using the specific composite evaluation technique\<close>

Definition*[composite_product, short_name="''composite product''"]
\<open>product comprised of two or more components which can be organized in two layers:
 a layer of one already evaluated \<^cc_term>\<open>base_component\<close> (\<^cc_term>\<open>base_TOE\<close>)
 and a layer of one @{cc_term (unchecked) \<open>dependent_component\<close>}\<close>

Definition*[COMP, short_name="''composite product assurance package''"]
\<open>\<close>

Definition*[composite_TOE, short_name="''composite target of evaluation''"]
\<open>part of a \<^cc_term>\<open>composite_product\<close> including the \<^cc_term>\<open>base_TOE\<close>
 and the @{cc_term (unchecked) \<open>dependent_component\<close>}\<close>

Definition*[CM, short_name="''configuration management''"]
\<open>discipline applying technical and administrative direction and surveillance to:
 identify and document the functional and physical characteristics of a configuration item,
 control changes to those characteristics, record and report change processing
 and implementation status, and verify compliance with specified requirements\<close>

Definition*[CMS, short_name="''configuration management system''"]
\<open>set of procedures and tools (including their documentation) used by a @{cc_term (unchecked) \<open>developer\<close>}
 to develop and maintain configurations of their products during their life-cycles\<close>

Definition*[counter]
\<open>act on or respond to a particular threat so that the threat is eradicated or mitigated\<close>

declare_reference*[ST]
declare_reference*[PP_configuration]
Definition*[DC, short_name="''demonstrable conformance''"]
\<open>relation between a @{cc_term (unchecked) \<open>PP\<close>}/@{cc_term (unchecked) \<open>ST\<close>} (PP/ST)
 and a @{cc_term (unchecked) \<open>PP\<close>}, or an @{cc_term (unchecked) \<open>ST\<close>} and
 a @{cc_term (unchecked) \<open>PP_configuration\<close>}, where the PP/ST provides an equivalent or
 more restrictive solution that solves the generic security problem in the PP/PP-Configuration\<close>

declare_reference*[FP]
Definition*[dependency]
\<open>relationship between components such that a @{cc_term (unchecked) \<open>PP\<close>}, @{cc_term (unchecked) \<open>ST\<close>},
 @{cc_term (unchecked) \<open>FP\<close>} or \<^cc_term>\<open>AP\<close>} including a component
 also includes any other \<^cc_term>\<open>component\<close>s that are identified as being depended upon
 or include a rationale as to why they are not\<close>

declare_reference*[dependent_entity]
Definition*[dependent_component, short_name="''dependent component''"]
\<open>@{cc_term (unchecked)\<open>dependent_entity\<close>} in a multi-component product that relies on
 the provision of services and resources by one or more \<^cc_term>\<open>base_component\<close>s\<close>

Definition*[dependent_TOE, short_name="''dependent target of evaluation''"]
\<open>\<^cc_term>\<open>dependent_component\<close> which is itself the subject of an evaluation\<close>

Definition*[developper]
\<open>organization responsible for the development of the @{cc_term (unchecked)\<open>TOE\<close>}\<close>

declare_reference*[SPD]
declare_reference*[SO]
declare_reference*[operational_environment]
Definition*[direct_rationale, short_name="''direct rationale''"]
\<open>type of @{cc_term (unchecked)\<open>PP\<close>}, @{cc_term (unchecked)\<open>PP_module\<close>} or @{cc_term (unchecked)\<open>ST\<close>}
 in which the @{cc_term (unchecked)\<open>SPD\<close>} elements are mapped directly to
 the @{cc_term (unchecked)\<open>SFR\<close>}) and possibly to the @{cc_term (unchecked)\<open>SO\<close>}s
 for the @{cc_term (unchecked)\<open>operational_environment\<close>}\<close>

Definition*[DAC, short_name="''discretionary access control''"]
\<open>\<close>

Definition*[element]
\<open>〈taxonomy〉 self-contained description of a security need assigned to @{cc_term (unchecked)\<open>SAR\<close>}
 or @{cc_term (unchecked)\<open>SFR\<close>}\<close>

Definition*[entity]
\<open>identifiable item that is described by a set or collection of properties\<close>

Definition*[evaluation]
\<open>assessment of a @{cc_term (unchecked)\<open>PP_configuration\<close>}, @{cc_term (unchecked)\<open>PP\<close>},
 a @{cc_term (unchecked)\<open>ST\<close>}, or a @{cc_term (unchecked)\<open>TOE\<close>}, against defined criteria
\<close>

Definition*[EA, short_name="''evaluation activity''"]
\<open>activity derived from one or more work units\<close>

Definition*[EAL, short_name="''evaluation assurance level''"]
\<open>well-formed package of @{cc_term (unchecked)\<open>SAR\<close>} representing a point on the pre- defined assurance scale\<close>

declare_reference*[evaluation_scheme]
Definition*[evaluation_authority, short_name="''evaluation authority''"]
\<open>body operating an @{cc_term (unchecked)\<open>evaluation_scheme\<close>}\<close>

Definition*[EM, short_name="''evaluation method''"]
\<open>set of one or more \<^cc_term>\<open>EA\<close> for application in a specific context\<close>

Definition*[evaluation_scheme, short_name="''evaluation scheme''"]
\<open>rules, procedures and management to carrying evaluations of IT product security\<close>

declare_reference*[overall_verdict]
Definition*[ETR, short_name="''evaluation technical report''"]
\<open>documentation of the @{cc_term (unchecked)\<open>overall_verdict\<close>} and its justification, produced
 by the @{cc_term (unchecked)\<open>evaluator\<close>}, and submitted to an \<^cc_term>\<open>evaluation_authority\<close>\<close>

Definition*[ETR_COMP, short_name="''evaluation technical report for composite evaluation''"]
\<open>documentation intended to be used within the \<^cc_term>\<open>composite_evaluation\<close> approach and derived
 by the \<^cc_term>\<open>base_component\<close> @{cc_term (unchecked)\<open>evaluator\<close>} from the full \<^cc_term>\<open>ETR\<close> 
for the evaluated \<^cc_term>\<open>base_component\<close>\<close>

Definition*[evaluator]
\<open>individual assigned to perform evaluations in accordance with a given evaluation standard and
 associated evaluation methodology\<close>

Definition*[EC, short_name="''exact conformance''"]
\<open>hierarchical relationship between a @{cc_term (unchecked)\<open>PP\<close>} or @{cc_term (unchecked)\<open>PP_configuration\<close>}
 and a @{cc_term (unchecked)\<open>ST\<close>} where all the requirements in the ST are drawn only from the PP/PP- Configuration\<close>

Definition*[exploitable_vulnerability, short_name="''exploitable vulnerability''"]
\<open>weakness in the @{cc_term (unchecked)\<open>TOE\<close>} that can be used to violate the @{cc_term (unchecked)\<open>SFR\<close>}s
 in the @{cc_term (unchecked)\<open>operational_environment\<close>} for the  @{cc_term (unchecked)\<open>TOE\<close>}\<close>

Definition*[extended_security_requirement, short_name="''extended security requirement''"]
\<open>security requirement developed according to the rules in this document,
 but which are not listed in any part of the CC\<close>

Definition*[user, short_name="''external entity''"]
\<open>human technical system or one of its components interacting with the @{cc_term (unchecked)\<open>TOE\<close>}
 from outside of the TOE boundary\<close>

Definition*[family]
\<open>〈taxonomy〉 set of components that shares a similar goal but differs in emphasis or rigour\<close>

Definition*[FP, short_name="''functional package''"]
\<open>named set of @{cc_term (unchecked)\<open>SFR\<close>}s that may be accompanied by a @{cc_term (unchecked)\<open>SPD\<close>}
 and @{cc_term (unchecked)\<open>SO\<close>}s derived from that SPD
\<close>

declare_reference*[multi_assurance_evaluation]
Definition*[global_AP, short_name="''global assurance package''"]
\<open>\<^cc_term>\<open>AP\<close> that applies to the entire  @{cc_term (unchecked)\<open>TOE\<close>} in a
  @{cc_term (unchecked)\<open>multi_assurance_evaluation\<close>}\<close>

Definition*[guidance_documentation, short_name="''guidance documentation''"]
\<open>documentation that describes the delivery, preparation, operation, management and/or use of the @{cc_term (unchecked)\<open>TOE\<close>}\<close>

declare_reference*[refinement]
Definition*[implementation_representation, short_name="''implementation representation''"]
\<open>least abstract representation of the @{cc_term (unchecked)\<open>TSF\<close>}, specifically the one
 that is used to create the TSF itself without further design @{cc_term (unchecked)\<open>refinement\<close>}\<close>

Definition*[internally_consistent, short_name="''internally consistent''"]
\<open>no apparent contradictions exist between any aspects of an \<^cc_term>\<open>entity\<close>\<close>

Definition*[interpretation_cc, short_name="''interpretation''"]
\<open>clarification or amplification of a standard or an \<^cc_term>\<open>evaluation_scheme\<close> requirement\<close>

Definition*[iteration]
\<open>use of the same \<^cc_term>\<open>component\<close> to express two or more distinct requirements\<close>

Definition*[layering]
\<open>design technique where separate groups of components are hierarchically organized to have separate
 responsibilities such that a group of components depends on groups of components below it in
 the hierarchy for services, and provides its services to the groups of components above it\<close>

Definition*[module_cc, short_name="''module''"]
\<open>architectural unit specified at a level suitable for implementation of the unit\<close>

Definition*[multi_assurance_evaluation, short_name="''multi-assurance evaluation''"]
\<open>evaluation of a @{cc_term (unchecked)\<open>TOE\<close>} using a @{cc_term (unchecked)\<open>PP_configuration\<close>}
 where each PP- Configuration component is associated with its own set of assurance requirements\<close>

Definition*[object]
\<open>\<^cc_term>\<open>entity\<close>in the @{cc_term (unchecked)\<open>TOE\<close>} that contains or receives information, and
 upon which subjects perform operations\<close>

Definition*[operation]
\<open>〈on an \<^cc_term>\<open>object\<close>〉 specific type of \<^cc_term>\<open>action\<close> performed by a subject on an object
\<close>

Definition*[operational_environment, short_name="''operational environment''"]
\<open>environment in which the @{cc_term (unchecked)\<open>TOE\<close>} is operated, consisting of everything
 that is outside the TOE boundary\<close>

Definition*[optional_SFR, short_name="''optional Security Functional Requirement''"]
\<open>@{cc_term (unchecked)\<open>SFR\<close>} in a @{cc_term (unchecked)\<open>PP\<close>}, @{cc_term (unchecked)\<open>FP\<close>}, or
 @{cc_term (unchecked)\<open>PP_module\<close>} that contributes to a stated aspect of the PP’s security problem
 description but whose inclusion in a conformant PP’s or @{cc_term (unchecked)\<open>ST\<close>} list of
 SFRs is not mandatory\<close>

Definition*[OSP, short_name="''organizational security policy''"]
\<open>set of security rules, procedures, or guidelines for an organization\<close>

Definition*[overall_verdict, short_name="''overall verdict''"]
\<open>statement issued by an \<^cc_term>\<open>evaluator\<close> with respect to the result of an \<^cc_term>\<open>evaluation\<close>\<close>

Definition*[potential_vulnerability, short_name="''potential vulnerability''"]
\<open>suspected, but not confirmed, weakness
\<close>

Definition*[PP, short_name="''Protection Profile''"]
\<open>implementation-independent statement of security needs for a @{cc_term (unchecked)\<open>TOE\<close>} type\<close>

Definition*[PP_configuration, short_name="''Protection Profile Configuration''"]
\<open>implementation-independent statement of security needs for a @{cc_term (unchecked)\<open>TOE\<close>} type
 containing at least one \<^cc_term>\<open>PP\<close> and an additional non-empty set of @{cc_term (unchecked)\<open>PP_module\<close>}
 (with the associated PP-Modules Bases)\<close>

Definition*[PP_configuration_component, short_name="''Protection Profile Configuration component''"]
\<open>\<^cc_term>\<open>PP\<close> or @{cc_term (unchecked)\<open>PP_module\<close>} included in a \<^cc_term>\<open>PP_configuration\<close>\<close>

Definition*[PP_module, short_name="''Protection Profile module''"]
\<open>implementation-independent statement of security needs for a @{cc_term (unchecked)\<open>TOE\<close>} type
 complementary to one or more base \<^cc_term>\<open>PP\<close> and possibly some \<^cc_term>\<open>base_PP_module\<close>\<close>

Definition*[PP_module_base, short_name="''Protection Profile Module Base''"]
\<open>set of either \<^cc_term>\<open>PP_module\<close> or \<^cc_term>\<open>PP\<close> or both, specified by a PP- Module as a basis
 for building a \<^cc_term>\<open>PP_configuration\<close>\<close>

Definition*[refinement]
\<open>addition of details to a security component\<close>

Definition*[residual_vulnerability, short_name="''residual vulnerability''"]
\<open>weakness that cannot be exploited in the \<^cc_term>\<open>operational_environment\<close> for the
 @{cc_term (unchecked)\<open>TOE\<close>}, but that can be used to violate the @{cc_term (unchecked)\<open>SFR\<close>}s by
 an attacker with greater \<^cc_term>\<open>attack_potential\<close> than is anticipated in the operational
 environment for the TOE\<close>

Definition*[role]
\<open>pre-defined set of rules establishing the allowed interactions between a user and the @{cc_term (unchecked)\<open>TOE\<close>}\<close>

Definition*[SAR, short_name="''security assurance requirement''"]
\<open>security requirement that refers to the conditions and processes for the development and delivery
 of the @{cc_term (unchecked)\<open>TOE\<close>}, and the \<^cc_term>\<open>action\<close>s required of \<^cc_term>\<open>evaluator\<close>s
 with respect to evidence produced from these conditions and processes
\<close>

Definition*[security_attribute, short_name="''security attribute''"]
\<open>property of subjects, users, objects, information, sessions and/or resources that is used in
 defining the @{cc_term (unchecked)\<open>SFR\<close>}s and whose values are used in enforcing the SFRs
\<close>

Definition*[SFR, short_name="''security functional requirement''"]
\<open>security requirement, which contributes to fulfil the @{cc_term (unchecked)\<open>TOE\<close>}
 @{cc_term (unchecked)\<open>SPD\<close>} as defined in a specific @{cc_term (unchecked)\<open>ST\<close>} or in a \<^cc_term>\<open>PP\<close>\<close>

Definition*[SO, short_name="''security objective''"]
\<open>statement of an intent to \<^cc_term>\<open>counter\<close> identified threats and/or satisfy identified
 organization security policies and/or assumptions\<close>

Definition*[SPD, short_name="''security problem definition''"]
\<open>statement, which in a formal manner defines the nature and scope of the security that the
 @{cc_term (unchecked)\<open>TOE\<close>} is intended to address\<close>

Definition*[SR, short_name="''security requirement''"]
\<open>requirement, which is part of a @{cc_term (unchecked)\<open>TOE\<close>} security specification as defined
 in a specific @{cc_term (unchecked)\<open>ST\<close>} or in a \<^cc_term>\<open>PP\<close>\<close>

Definition*[ST, short_name="''Security Target''"]
\<open>implementation-dependent statement of security requirements for a @{cc_term (unchecked)\<open>TOE\<close>}
 based on a \<^cc_term>\<open>SPD\<close>\<close>

Definition*[selection]
\<open>specification of one or more items from a list in a component\<close>

Definition*[selection_based_SFR, short_name="''selection-based security functional requirement''"]
\<open>\<^cc_term>\<open>SFR\<close>s in a \<^cc_term>\<open>PP\<close>, \<^cc_term>\<open>PP_module\<close>, or \<^cc_term>\<open>FP\<close> that contributes to a state
 aspect of the PP’s, PP-Module’s or functional package’s \<^cc_term>\<open>SPD\<close> that is to be included
 in a conformant PP or ST if a selection choice identified in the PP/PP-Module/functional package
 indicates that it has an associated selection-based SFR\<close>

Definition*[single_assurance_evaluation, short_name="''single-assurance evaluation''"]
\<open>evaluation of a @{cc_term (unchecked)\<open>TOE\<close>} using one set of assurance requirements\<close>

Definition*[SC, short_name="''strict conformance''"]
\<open>hierarchical relationship between a \<^cc_term>\<open>PP\<close> and a PP/\<^cc_term>\<open>PP\<close> where all the requirements
 in the PP also exist in the PP/ST\<close>

Definition*[sub_TSF, short_name="''sub-TOE security functionality''"]
\<open>combined functionality of all hardware, software, and firmware of a @{cc_term (unchecked)\<open>TOE\<close>}
 that is relied upon for the correct enforcement of the \<^cc_term>\<open>SFR\<close>s defined in one
 \<^cc_term>\<open>PP_configuration\<close> component\<close>

Definition*[subject]
\<open>\<^cc_term>\<open>entity\<close> in the @{cc_term (unchecked)\<open>TOE\<close>} that performs operations on objects\<close>

Definition*[tailoring]
\<open>addition of one or more functional requirements to a \<^cc_term>\<open>FP\<close>, and/or the addition of one or
 more selections to a \<^cc_term>\<open>SFR\<close> in a functional package\<close>

Definition*[TOE, short_name="''target of evaluation''"]
\<open>set of software, firmware and/or hardware possibly accompanied by guidance, which is the subject of an evaluation\<close>

Definition*[threat_agent, short_name="''threat agent''"]
\<open>\<^cc_term>\<open>entity\<close> that has potential to exercise \<^cc_term>\<open>adverse_action\<close> on \<^cc_term>\<open>asset\<close>s
 protected by the \<^cc_term>\<open>TOE\<close>\<close>

Definition*[TSF, short_name="''TOE security functionality''"]
\<open>combined functionality of all hardware, software, and firmware of a \<^cc_term>\<open>TOE\<close> that is relied
 upon for the correct enforcement of the \<^cc_term>\<open>SFR\<close>s\<close>

Definition*[TOE_type, short_name="''TOE type''"]
\<open>set of characteristics common to a group of \<^cc_term>\<open>TOE\<close>\<close>

Definition*[translation]
\<open>process of describing security requirements in a standardized language\<close>

Definition*[vulnerability]
\<open>weakness in the \<^cc_term>\<open>TOE\<close> that can be used to violate the \<^cc_term>\<open>SFR\<close>s in some environment\<close>

Definition*[DPA, short_name="''differential power analysis''"]
\<open>\<close>

Definition*[DRBG, short_name="''deterministic random bit generator''"]
\<open>\<close>

Definition*[ES, short_name="''electromagnetic spectrum''"]
\<open>\<close>

Definition*[GAP, short_name="''global assurance package''"]
\<open>\<close>

Definition*[GB, short_name="''gygabyte''"]
\<open>\<close>

Definition*[GHz, short_name="''gigahertz''"]
\<open>\<close>

Definition*[GUI, short_name="''graphical user interface''"]
\<open>\<close>

define_shortcut* csp      \<rightleftharpoons> \<open>CSP\<close>
                 holcsp   \<rightleftharpoons> \<open>HOL-CSP\<close>
                 hol      \<rightleftharpoons> \<open>HOL\<close>
                 isabelle \<rightleftharpoons> \<open>Isabelle/HOL\<close>

(*text\<open>
  @{boxed_theory_text [display]
\<open>\<close>
}\<close>*)

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