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

(*<*)
theory 
  mini_odo
imports  
  "Isabelle_DOF-Ontologies.CENELEC_50128" 
  "Isabelle_DOF.technical_report"
  "Physical_Quantities.SI" "Physical_Quantities.SI_Pretty"
begin
use_template "scrreprt-modern"
use_ontology technical_report and "Isabelle_DOF-Ontologies.CENELEC_50128"
declare[[strict_monitor_checking=true]]
define_shortcut* dof     \<rightleftharpoons> \<open>\dof\<close>
                 isadof  \<rightleftharpoons> \<open>\isadof{}\<close>
(*>*)

title*[title::title]\<open>The CENELEC 50128 Ontology\<close> 
subtitle*[subtitle::subtitle]\<open>Case Study: An Odometer-Subsystem\<close> 

chapter*[casestudy::technical]\<open>An Odometer-Subsystem\<close>
text\<open>
  In our case study, we will follow the phases of analysis, design, and implementation of the 
  odometry function of a train. This \<^cenelec_term>\<open>SF\<close> processes data from an odometer to compute 
  the position,  speed, and acceleration of a train. This system provides the basis for many 
  safety critical decisions, \<^eg>, the opening of the doors. Due to its relatively small size, it 
  is a manageable, albeit realistic target for a comprehensive formal development: it covers a 
  physical model of the environment, the physical and architectural model of the odometer,
  but also the  \<^cenelec_term>\<open>SFRS\<close> aspects including the problem of numerical sampling and the 
  boundaries of efficient computations. The interplay between environment and measuring-device as 
  well as the implementation problems on a platform with limited resources makes the odometer a 
  fairly typical \<^cenelec_term>\<open>safety\<close> critical \<^cenelec_term>\<open>component\<close> of an embedded system.

  The case-study is presented in form of an \<^emph>\<open>integrated source\<close> in \<^isadof> containing all four
  reports from the phases:
    \<^item> \<^term>\<open>software_requirements\<close> with deliverable \<^doc_class>\<open>SWRS\<close> 
       (or long:\<^typ>\<open>software_requirements_specification\<close>(-report))
    \<^item> \<^term>\<open>software_architecture_and_design\<close> with deliverable \<^doc_class>\<open>SWDS\<close> 
      (or long: \<^typ>\<open>software_design_specification\<close>(-report))
    \<^item> \<^term>\<open>software_component_design\<close> with deliverable \<^doc_class>\<open>SWCDVR\<close>
      (or long: \<^typ>\<open>software_component_design_verification\<close>(-report).)
    \<^item> \<^term>\<open>component_implementation_and_testing\<close> with deliverable \<^doc_class>\<open>SWADVR\<close>
      (or long: \<^typ>\<open>software_architecture_and_design_verification\<close>(-report))

  The objective of this case study is to demonstrate deep-semantical ontologoies in 
  software developments targeting certifications, and in particular, how \<^isadof>'s 
  integrated source concept permits to assure \<^cenelec_term>\<open>traceability\<close>.

  \<^bold>\<open>NOTE\<close> that this case study has aspects that were actually covered by CENELEC 50126 - 
  the 'systems'-counterpart covering hardware aspects. Recall that the CENELEC 50128 covers
  software. 

  Due to space reasons, we will focus  on the analysis part of the integrated 
  document; the design and code parts will only be outlined in a final resume. The 
  \<^emph>\<open>ontological embedding\<close>, which represents a main contribution of this paper, will be presented 
  in the next two sections.

  We start with the capture of a number of informal documents available at the beginning of the
  development.
\<close>

section\<open>A CENELEC-conform development as an \<^emph>\<open>Integrated Source\<close>\<close>

text\<open>Accurate information of a train's location along a track is in an important prerequisite   
to safe railway operation. Position, speed and acceleration measurement usually lies on a 
set of independent measurements based on different physical principles---as a way to enhance 
precision and availability.  One of them is an \<^emph>\<open>odometer\<close>, which allows estimating a relative 
location while the train runs positions established by other measurements. \<close>

subsection\<open>Capturing ``Basic Principles of Motion and Motion Measurement.''\<close>
text\<open>
  A rotary encoder measures the motion of a train. To achieve this, the encoder's shaft is fixed to
  the trains wheels axle. When the train moves, the encoder produces a signal pattern directly 
  related to the trains progress.  By measuring the fractional rotation of the encoders shaft and 
  considering the wheels effective ratio, relative movement of the train can be calculated.

  \begin{wrapfigure}[8]{l}{4.6cm}
    \centering
    \vspace{-.5cm}
    \includegraphics[width=3.4cm]{figures/wheel-df}
    \caption{Motion sensing via an odometer.}
    \label{wheel-df}
  \end{wrapfigure}
  \autoref{wheel-df} shows that we model a train, seen from a pure kinematics standpoint, as physical 
  system characterized by a one-dimensional continuous distance function, which represents the 
  observable of the physical system.  Concepts like speed and acceleration were derived concepts 
  defined as their (gradient) derivatives. We assume the use of the meter, kilogram, and second 
  (MKS) system.

  This model is already based on several fundamental assumptions relevant for the correct
  functioning of the system and for its integration into the system as a whole. In 
  particular, we need to make the following assumptions explicit: \<^vs>\<open>-0.3cm\<close>\<close>

text*["perfect_wheel"::assumption]
\<open>\<^item> the wheel is perfectly circular with a given, constant radius. \<^vs>\<open>-0.3cm\<close>\<close>
text*["no_slip"::assumption]
\<open>\<^item> the slip between the trains wheel and the track negligible. \<^vs>\<open>-0.3cm\<close>\<close>
text*["constant_teeth_dist"::assumption]
\<open>\<^item>  the distance between all teeth of a wheel is the same and constant, and \<^vs>\<open>-0.3cm\<close>\<close>
text*["constant_sampling_rate"::assumption]
\<open>\<^item>  the sampling rate of positions is a given constant.\<close>

text\<open>
  These assumptions have to be traced throughout the certification process as

  \<^emph>\<open>derived requirements\<close> (or, in CENELEC terminology, as \<^emph>\<open>exported constraints\<close>), which is
  also reflected by their tracing throughout the body of certification documents. This may result
  in operational regulations, \<^eg>, regular checks for tolerable wheel defects. As for the
  \<^emph>\<open>no slip\<close>-assumption, this leads to the modeling of constraints under which physical 
  slip can be neglected: the device can only produce reliable results under certain physical
  constraints (speed and acceleration limits). Moreover, the \<^emph>\<open>no slip\<close>-assumption motivates
  architectural arrangements for situations where this assumption cannot be assured (as is the
  case, for example, of an emergency breaking) together with error-detection and error-recovery.
\<close>

subsection\<open>Capturing ``System Architecture.''\<close>

figure*["three_phase"::figure,relative_width="70",file_src="''figures/three-phase-odo.pdf''"]
\<open>An odometer with three sensors \<open>C1\<close>, \<open>C2\<close>, and \<open>C3\<close>.\<close>

text\<open>
  The requirements analysis also contains a document \<^doc_class>\<open>SYSAD\<close> 
  (\<^typ>\<open>system_architecture_description\<close>) that contains technical drawing of the odometer, 
  a timing diagram  (see \<^figure>\<open>three_phase\<close>), and tables describing the encoding of the position 
  for the possible signal transitions of the sensors \<open>C1\<close>, \<open>C2\<close>, and \<open>C3\<close>. 
\<close>

subsection\<open>Capturing ``System Interfaces.''\<close>
text\<open>
  The requirements analysis also contains a sub-document  \<^doc_class>\<open>FnI\<close>  (\<^typ>\<open>functions_and_interfaces\<close>)  
  describing the technical format of the output of the odometry function. 
  This section, \<^eg>, specifies the output \<^emph>\<open>speed\<close> as given by a \<^verbatim>\<open>int_32\<close> to be the 
  ``Estimation of the speed (in mm/sec) evaluated  over the latest \<open>N\<^sub>a\<^sub>v\<^sub>g\<close>  samples''
  where the speed refers to the physical speed of the train and \<open>N\<^sub>a\<^sub>v\<^sub>g\<close> a parameter of the
  sub-system configuration. \<close>

(*<*)
declare_reference*["df_numerics_encshaft"::figure] 
(*>*)
subsection\<open>Capturing ``Required Performances.''\<close>
text\<open>
  The given analysis document is relatively implicit on the expected precision of the measurements; 
  however, certain interface parameters like \<open>Odometric_Position_TimeStamp\<close>
  (a counter on the number of samplings) and \<open>Relative_Position\<close> are defined by as 
  unsigned 32 bit integer. These definitions imply that exported constraints concerning the acceptable 
  time of service as well the maximum distance before a necessary reboot of the subsystem. 
  For our case-study, we assume maximum deviation of the \<open>Relative_Position\<close> to the 
  theoretical distance.

  The requirement analysis document describes the physical environment, the architecture
  of the measuring device, and the required format and precision of the measurements of the odometry
  function as represented (see @{figure (unchecked) "df_numerics_encshaft"}).\<close>

figure*["df_numerics_encshaft"::figure,relative_width="76",file_src="''figures/df-numerics-encshaft.png''"]
\<open>Real distance vs. discrete distance vs. shaft-encoder sequence\<close>


subsection\<open>Capturing the ``Software Design Spec'' (Resume).\<close>
text\<open>
  The design provides a function that manages an internal first-in-first-out buffer of 
  shaft-encodings and corresponding positions. Central for the design is a step-function analyzing 
  new incoming shaft encodings, checking them and propagating two kinds of error-states (one allowing 
  recovery, another one, fatal, signaling, \<^eg>, a defect of the receiver hardware), 
  calculating the relative position, speed and acceleration.
\<close>

subsection\<open>Capturing the ``Software Implementation'' (Resume).\<close>
text\<open>
  While the design is executable on a Linux system, it turns out that the generated code from an 
  Isabelle model is neither executable on resource-constraint target platform, an ARM-based  
  Sabre-light card, nor certifiable, since the compilation chain via ML to C implies the 
  inclusion of a run-time system and quite complex libraries. 
  We adopted therefore a similar approach as used in the seL4 project~@{cite "Klein2014"}: we use a   
  hand-written implementation in C and verify it via 
  AutoCorres~@{cite "greenaway.ea:bridging:2012"}  against 
  the design model. The hand-written C-source is integrated into the Isabelle/HOL technically by 
  registering it in the build-configuration and logically by a trusted C-to-HOL compiler included 
  in AutoCorres.
\<close>

(*<*)
      definition teeth_per_wheelturn::nat  ("tpw") where "tpw \<equiv> SOME x. x > 0"
      definition wheel_diameter     ::"real[m]" ("w\<^sub>d") where "w\<^sub>d \<equiv> SOME x. x > 0" 
      definition wheel_circumference::"real[m]" ("w\<^sub>0") where "w\<^sub>0 \<equiv> pi *\<^sub>Q w\<^sub>d"
      definition \<delta>s\<^sub>r\<^sub>e\<^sub>s               ::"real[m]" where "\<delta>s\<^sub>r\<^sub>e\<^sub>s \<equiv> 1 / (2 * 3 * tpw) *\<^sub>Q w\<^sub>0 "
(*>*)


section\<open>Formal Enrichment of the Software Requirements Specification\<close>
text\<open>
  After the \<^emph>\<open>capture\<close>-phase, where we converted/integrated existing informal analysis and design 
  documents as well as code into an integrated Isabelle document, we entered into the phase of 
  \<open>formal enrichment\<close>. For example, from the assumptions in the architecture follow 
  the definitions:

      @{theory_text [display]\<open>
      definition teeth_per_wheelturn::nat  ("tpw") where "tpw \<equiv> SOME x. x > 0"
      definition wheel_diameter::"real[m]" ("w\<^sub>d") where "w\<^sub>d \<equiv> SOME x. x > 0" 
      definition wheel_circumference::"real[m]" ("w\<^sub>0") where "w\<^sub>0 \<equiv> pi *\<^sub>Q w\<^sub>d"
      definition \<delta>s\<^sub>r\<^sub>e\<^sub>s::"real[m]" where "\<delta>s\<^sub>r\<^sub>e\<^sub>s \<equiv> 1 / (2 * 3 * tpw) *\<^sub>Q w\<^sub>0 "
      \<close>}
 
  Here, \<open>real\<close> refers to the real numbers as defined in the HOL-Analysis  library, which provides 
  concepts such as Cauchy Sequences, limits, differentiability, and a very substantial part of 
  classical Calculus. \<open>SOME\<close> is the Hilbert choice operator from HOL; the definitions of the 
  model parameters admit all possible positive values as uninterpreted constants. Our 
  \<^assumption>\<open>perfect_wheel\<close> is translated into a calculation of the circumference of the
  wheel, while \<open>\<delta>s\<^sub>r\<^sub>e\<^sub>s\<close>, the resolution of the odometer, can be calculated 
  from the these parameters. HOL-Analysis permits to formalize the fundamental physical observables:
\<close>

(*<*)
type_synonym distance_function = "real[s] \<Rightarrow> real[m]" 
consts       Speed::"distance_function \<Rightarrow> real[s] \<Rightarrow> real[m\<cdot>s\<^sup>-\<^sup>1]"
consts       Accel::"distance_function \<Rightarrow> real[s] \<Rightarrow> real[m\<cdot>s\<^sup>-\<^sup>2]"
consts       Speed\<^sub>M\<^sub>a\<^sub>x::"real[m\<cdot>s\<^sup>-\<^sup>1]"

(* Non - SI conform common abrbreviations *)
definition   "kmh \<equiv> kilo *\<^sub>Q metre \<^bold>/ hour :: 'a::{field,ring_char_0}[m\<cdot>s\<^sup>-\<^sup>1]"
definition   "kHz \<equiv> kilo *\<^sub>Q hertz :: 'a::{field,ring_char_0}[s\<^sup>-\<^sup>1]"

(*>*)
text\<open>
      @{theory_text [display]\<open>
      type_synonym distance_function = "real[s]\<Rightarrow>real[m]"  
      definition Speed::"distance_function\<Rightarrow>real\<Rightarrow>real"  where "Speed f \<equiv> deriv f"
      definition Accel::"distance_function\<Rightarrow>real\<Rightarrow>real"  where "Accel f \<equiv> deriv (deriv f)" 
      \<close>}

which permits to constrain the central observable \<open>distance_function\<close> in a 
way that they describe the space of ``normal behavior'' where we expect the odometer to produce
reliable measurements over a \<open>distance_function df\<close> . 

The essence of the physics of the train is covered by the following definition:

     @{theory_text [display]\<open>
     definition normally_behaved_distance_function :: "(real \<Rightarrow> real) \<Rightarrow> bool"
     where  normally_behaved_distance_function df = 
            ( \<forall> t. df(t) \<in> \<real>\<^sub>\<ge>\<^sub>0  \<and>  (\<forall> t \<in> \<real>\<real>\<^sub>\<ge>\<^sub>0. df(t) = 0)  
             \<and> df differentiable on \<real>\<^sub>\<ge>\<^sub>0 \<and> (Speed df)differentiable on \<real>\<^sub>\<ge>\<^sub>0$ 
             \<and> (Accel df)differentiable on \<real>\<^sub>\<ge>\<^sub>0 
             \<and> (\<forall> t. (Speed df) t \<in> {Speed\<^sub>M\<^sub>i\<^sub>n .. Speed\<^sub>M\<^sub>a\<^sub>x})  
             \<and> (\<forall> t. (Accel df) t \<in> {Accel\<^sub>M\<^sub>i\<^sub>n .. Accel\<^sub>M\<^sub>a\<^sub>x}))
     \<close>}

which constrains the distance functions in the bounds described of the informal descriptions and
states them as three-fold differentiable function in certain bounds concerning speed and 
acceleration. Note that violations, in particular of the constraints on speed and acceleration, 
\<^emph>\<open>do\<close> occur in practice. In such cases, the global system adapts recovery strategies that are out 
of the scope of our model. Concepts like \<open>shaft_encoder_state\<close> (a triple with the sensor values 
\<open>C1\<close>, \<open>C2\<close>, \<open>C3\<close>)  were formalized as types, while tables were 
defined as recursive functions:

    @{theory_text [display]\<open>
    fun phase\<^sub>0 :: "nat \<Rightarrow> shaft_encoder_state"   where 
       "phase\<^sub>0 (0) =  \<lparr> C1 = False, C2 = False, C3 = True \<rparr>" 
      |"phase\<^sub>0 (1) =  \<lparr> C1 = True,  C2 = False, C3 = True \<rparr>" 
      |"phase\<^sub>0 (2) =  \<lparr> C1 = True,  C2 = False, C3 = False\<rparr>" 
      |"phase\<^sub>0 (3) =  \<lparr> C1 = True,  C2 = True,  C3 = False\<rparr>" 
      |"phase\<^sub>0 (4) =  \<lparr> C1 = False, C2 = True,  C3 = False\<rparr>" 
      |"phase\<^sub>0 (5) =  \<lparr> C1 = False, C2 = True,  C3 = True \<rparr>" 
      |"phase\<^sub>0 x   =  phase\<^sub>0(x - 6)"         
    definition Phase ::"nat\<Rightarrow>shaft_encoder_state" where Phase(x) = phase\<^sub>0(x-1)
    \<close>}

We now define shaft encoder sequences as translations of distance functions:

    @{theory_text [display]\<open>
    definition encoding::"distance_function\<Rightarrow>nat\<Rightarrow>real\<Rightarrow>shaft_encoder_state" 
      where   "encoding df init\<^sub>p\<^sub>o\<^sub>s \<equiv> \<lambda>x. Phase(nat\<lfloor>df(x) / \<delta>s\<^sub>r\<^sub>e\<^sub>s\<rfloor> + init\<^sub>p\<^sub>o\<^sub>s)"
    \<close>}

where \<open>init\<^sub>p\<^sub>o\<^sub>s\<close> is the initial position of the wheel. 
\<open>sampling\<close>'s were constructed from encoding sequences over discretized time points:

    @{theory_text [display]\<open>
     definition sampling::"distance_function\<Rightarrow>nat\<Rightarrow>real\<Rightarrow>nat\<Rightarrow>shaft_encoder_state" 
      where "sampling df init\<^sub>p\<^sub>o\<^sub>s \<delta>t \<equiv> \<lambda>n::nat. encoding df initinit\<^sub>p\<^sub>o\<^sub>s (n * \<delta>t)"
    \<close>}

parameter of the configuration of a system.

Finally, we can formally define the required performances. From the interface description
and the global model parameters such as wheel diameter, the number of teeth per wheel, the 
sampling frequency etc., we can infer the maximal time of service as well the maximum distance 
the device can measure.  As an example configuration, choosing:

   \<^item> \<^term>\<open>(1 *\<^sub>Q metre):: real[m]\<close>      for  \<^term>\<open>w\<^sub>d\<close>   (wheel-diameter), 
   \<^item> \<^term>\<open>100         :: real\<close>        for  \<^term>\<open>tpw\<close> (teeth per wheel), 
   \<^item> \<^term>\<open>80 *\<^sub>Q kmh   :: real[m\<cdot>s\<^sup>-\<^sup>1]\<close>  for  \<^term>\<open>Speed\<^sub>M\<^sub>a\<^sub>x\<close>,
   \<^item> \<^term>\<open>14.4 *\<^sub>Q kHz :: real[s\<^sup>-\<^sup>1]\<close>    for the sampling frequency,
 
results in an odometer resolution of \<^term>\<open>2.3 *\<^sub>Q milli *\<^sub>Q metre\<close>, a maximum distance of 
\<^term>\<open>9878 *\<^sub>Q kilo *\<^sub>Q metre\<close>, and a maximal system up-time of \<^term>\<open>123.4 *\<^sub>Q hour\<close>s.
The required precision of an odometer can be defined by a constant describing
the maximally allowed difference between \<open>df(n*\<delta>t)\<close>  and 
\<open>sampling df init\<^sub>p\<^sub>o\<^sub>s \<delta>t n\<close> for all \<open>init\<^sub>p\<^sub>o\<^sub>s \<in>{0..5}\<close>.
\<close>
(*<*)
ML\<open>val two_thirty2 = 1024 * 1024 * 1024 * 4;
   val dist_max = 0.0023 * (real two_thirty2) / 1000.0;
   val dist_h = dist_max / 80.0\<close>
(*>*)

section*[verific::technical]\<open>Verification of the Software Requirements Specification\<close>
text\<open>The original documents contained already various statements that motivate certain safety 
properties of the device. For example, the \<open>Phase\<close>-table excludes situations in which 
all sensors \<open>C1\<close>, \<open>C2\<close>, and \<open>C3\<close> are all ``off'' or situations in 
which sensors are ``on,'' reflecting a physical or electrical error in the odometer. It can be 
shown by a very small Isabelle case-distinction proof that this safety requirement follows indeed 
from the above definitions:

   @{theory_text [display]\<open>
      lemma Encoder_Property_1:(C1(Phase x) \<and> C2(Phase x) \<and> C3(Phase x))=False
        proof (cases x)
          case 0 then show ?thesis  by (simp add: Phase_def)
        next
          case (Suc n) then show ?thesis 
            by(simp add: Phase_def,rule_tac n = n in cycle_case_split,simp_all)
        qed    
   \<close>}

for all positions \<open>x\<close>. Similarly, it is proved that the table is indeed cyclic: 

   \<open>phase\<^sub>0 x = phase\<^sub>0(x mod 6)\<close> 

and locally injective:

   \<open>\<forall>x<6. \<forall>y<6. phase\<^sub>0 x = phase\<^sub>0 y \<longrightarrow> x = y\<close> 

These lemmas, building the ``theory of an odometer,'' culminate in a theorem
that we would like to present in more detail.

   @{theory_text [display]\<open>
      theorem minimal_sampling :
     assumes * : normally_behaved_distance_function df
       and  ** : \<delta>t * Speed\<^sub>M\<^sub>a\<^sub>x < \<delta>s\<^sub>r\<^sub>e\<^sub>s
     shows \<forall> \<delta>X\<le>\<delta>t. 0<\<delta>X \<longrightarrow> 
                \<exists>f. retracting (f::nat\<Rightarrow>nat) \<and> 
                    sampling df init\<^sub>p\<^sub>o\<^sub>s \<delta>X = (sampling df init\<^sub>p\<^sub>o\<^sub>s \<delta>t) o f
   
   \<close>}

This theorem states for \<open>normally_behaved_distance_function\<close>s that there is
a minimal sampling frequency assuring the safety of the measurements; samplings on 
some \<open>df\<close> gained from this minimal sampling frequency can be ``pumped up'' 
to samplings of these higher sampling frequencies; they do not contain more information.
Of particular interest is the second assumption, labelled ``\<open>**\<close>'' which  
establishes a lower bound from \<open>w\<^sub>0\<close>, \<open>tpw\<close>, 
\<open>Speed\<^sub>M\<^sub>a\<^sub>x\<close> for the sampling frequency. Methodologically, this represents 
an exported constraint that can not be represented \<^emph>\<open>inside\<close> the design model: it means that the 
computations have to be fast enough on the computing platform in order to assure that the 
calculations are valid. It was in particular this exported constraint that forced us to give up 
the original plan to generate the code from the design model and to execute this directly on the 
target platform. 

For our example configuration (1m diameter, 100 teeth per wheel, 80km/h max), this theorem justifies 
that 14,4 kHz is indeed enough to assure valid samplings.  Such properties are called 
``internal consistency of the software requirements specification'' in the CENELEC 
standard~@{cite "bsi:50128:2014"}, 7.2.4.22 and are usually addressed in an own report. 
\<close>

chapter*[ontomodeling::text_section]\<open>The CENELEC 50128 Ontology\<close>

text\<open>
  Modeling an ontology from a semi-formal text such as~@{cite"bsi:50128:2014"} is, 
  like any other modeling activity, not a simple one-to-one translation of some 
  concepts to some formalism. Rather, implicit and self-understood principles
  have to be made explicit, abstractions have to be made, and decisions about 
  the kind of desirable user-interaction may have an influence similarly to 
  design decisions influenced by strengths or weaknesses of a programming language. 
\<close>

section*[lhf::text_section]
\<open>Tracking Concepts and Definitions\<close>

text\<open>
  \<^isadof> is designed to annotate text elements with structured meta-information and to reference
  these text elements throughout the integrated source. A classical application of this capability 
  is the annotation of concepts and terms definitions---be them informal, semi-formal or formal---and 
  their consistent referencing. In the context of our CENELEC ontology, \<^eg>, we can translate the 
  third chapter of @{cite "bsi:50128:2014"} ``Terms, Definitions and Abbreviations'' directly 
  into our Ontology Definition Language (ODL). Picking one example out of 49, consider the definition 
  of the concept \<^cenelec_term>\<open>traceability\<close> in paragraphs 3.1.46 (a notion referenced 31 times in 
  the standard), which we translated directly into:

     @{theory_text [display]\<open>
         Definition*[traceability, short_name="''traceability''"]
         \<open>degree to which relationship can be established between two or more products of a 
          development  process, especially those having a predecessor/successor or 
          master/subordinate relationship to one another.\<close>
     \<close>}

  In the integrated source of the odometry study, we can reference in a text element to this
  concept as follows:

     @{theory_text [display]\<open>
          text*[...]\<open>  ... to assure <@>{cenelec_term traceability} for 
               <@>{requirement bitwiseAND}, we prove ... \<close>
     \<close>}

  
  \<^isadof> also uses the underlying ontology to generate the navigation markup inside the IDE, \<^ie>
  the presentation of this document element inside \<^isadof> is immediately hyperlinked against the
   @{theory_text \<open> Definition* \<close>}-element shown above; this serves as documentation of
  the standard for the development team working on the integrated source. The PDF presentation 
  of such links depends on the actual configurations for the document generation;  We will explain 
  this later. 
  CENELEC foresees also a number of roles, phases, safety integration levels, etc., which were
  directly translated into HOL enumeration types usable in ontological concepts of ODL.

     @{theory_text [display]\<open>
         datatype role =  
            PM  (* Program Manager *) |  RQM (* Requirements Manager *)
          | DES (* Designer *)        |  IMP (* Implementer *)        |  
          | VER (* Verifier *)        |  VAL (* Validator *)          |  ...
         datatype phase = 
            SYSDEV_ext (* System Development *) | SPl (* Software Planning     *)
          | SR    (* Software Requirement    *) | SA  (* Software Architecture *)
          | SDES  (* Software Design         *) | ...
    \<close>}

  Similarly, we can formalize the Table A.5: Verification and Testing of @{cite "bsi:50128:2014"}: 
  a classification of \<^emph>\<open>verification and testing techniques\<close>:

     @{theory_text [display]\<open>
        datatype vnt_technique = 
               formal_proof "thm list"    | stat_analysis 
             | dyn_analysis dyn_ana_kind  | ...
      \<close>}

  In contrast to the standard, we can parameterize \<open>formal_proof\<close> with a list of 
  theorems, an entity known in the Isabelle kernel. Here, \<^isadof>  assures for text elements 
  annotated with theorem names, that they refer indeed to established theorems in the Isabelle 
  environment. Additional checks could be added to make sure that these theorems have a particular 
  form.

  While we claim that this possibility to link to theorems (and test-results) is unique in the 
  world of systems attempting to assure \<^cenelec_term>\<open>traceability\<close>, referencing a particular 
  (proven) theorem is definitively not sufficient to satisfy the claimed requirement. Human 
  evaluators will always have  to check that the provided theorem \<open>adequately\<close> represents the claim; 
  we do not in the slightest suggest that their work is superfluous. Our framework allows to 
  statically check that tests or proofs  have been provided, at places where the ontology requires 
  them to be, and both assessors and developers  can rely on this check and navigate through 
  related information easily. It does not guarantee that  intended concepts for, \<^eg>, safety 
  or security have been adequately modeled. 
\<close>

section*[moe::text_section]
\<open>Major Ontological Entities: Requirements and Evidence\<close>
text\<open>
  We introduce central concept of a \<^emph>\<open>requirement\<close> as an ODL \<^theory_text>\<open>doc_class\<close> 
  based on the generic basic library \<^doc_class>\<open>text_element\<close> providing basic layout attributes.

     @{theory_text [display]\<open>
         doc_class requirement = text_element +
             long_name    :: "string option"
             is_concerned :: "role set"
      \<close>}

the groups of stakeholders in the CENELEC process. Therefore, the \<open>is_concerned\<close>-attribute 
allows expressing who ``owns'' this text-element. \<^isadof>  supports a role-based 
presentation, \<^eg>, different presentation styles of the integrated source may decide to highlight, 
to omit, to defer into an annex, text entities according to the role-set.  

Since ODL supports single inheritance, we can express sub-requirements and therefore a style
of requirement decomposition as advocated in GSN~@{cite "kelly.ea:goal:2004"}: 
 
     @{theory_text [display]\<open>
        doc_class sub_requirement = 
            decomposes :: "requirement"
            relates_to :: "requirement set"
      \<close>}
\<close>

section*[claimsreqevidence::text_section]\<open>Tracking Claims, Derived Requirements and Evidence\<close>
text\<open>An example for making explicit implicit principles,
consider the following statement @{cite "bsi:50128:2014"}, pp. 25.: \<^vs>\<open>-0.15cm\<close> 

\begin{quote}\small
The objective of software verification is to examine and arrive at a judgment based on 
evidence that output items (process, documentation, software or application) of a specific 
development phase fulfill the requirements and plans with respect to completeness, correctness 
and consistency.
\end{quote} \<^vs>\<open>-0.15cm\<close> 

The terms  \<^onto_class>\<open>judgement\<close> based on \<^term>\<open>evidence\<close> are used as a kind of leitmotif throughout 
the CENELEC standard, but they are neither explained nor even listed in the general glossary. 
However, the  standard is fairly explicit on the \<^emph>\<open>phase\<close>s and the organizational roles that 
different stakeholders  should have in the process. Our version to express this key concept of 
\<^onto_class>\<open>judgement\<close> , \<^eg>, by  the following concept:

     @{theory_text [display]\<open>
         doc_class judgement =    
            refers_to       :: requirement
            evidence        :: "vnt_technique list"
            status          :: status
            is_concerned    :: "role set" <= "{VER,ASR,VAL}" 
    \<close>}

As one can see, the role set is per default set to the verification team, the assessors and the 
validation team.

There are different views possible here: an alternative would be to define  \<^term>\<open>evidence\<close>
as ontological concept with  \<^typ>\<open>vnt_technique\<close>'s (rather than an attribute of judgement) 
and consider the basis of a summary containing the relation between requirements and relation:

     @{theory_text [display]\<open>
         doc_class summary =    
           based_on        :: "(requirement \<times> evidence) set"
           status          :: status
           is_concerned    :: "role set" <= "{VER,ASR,VAL}" 
    \<close>}

More experimentation will be needed to find out what kind of ontological modeling is most
adequate for developers in the context of \isadof. 
\<close>

section*[ontocontrol::text_section]\<open>Ontological Compliance\<close>

text\<open>From the variety of different possibilities for adding CENELEC annotations to the
integrated source, we will, in the following, point out three scenarios.\<close>

subsection\<open>Internal Verification of Claims in the Requirements Specification.\<close>
text\<open>In our case, the  \<^term>\<open>SR\<close>-team early on detected a property necessary
for error-detection of the device (c.f. @{technical verific}):

     @{theory_text [display]\<open>
          text*[encoder_props::requirement]\<open> The requirement specification team identifies the property:
              C1 & C2 & C3  = 0   (bitwise logical AND operation)
              C1 | C2 | C3  = 1   (bitwise logical OR operation) \<close>
    \<close>}

After the Isabelle proofs shown in @{technical verific}, we can either register the theorems
directly in an evidence statement: 

     @{theory_text [display]\<open>
          text*[J1::judgement, refers_to="@{docitem <open>encoder_props<close>}", 
                               evidence="[formal_proof[@{thm <open>Encoder_Property_1<close>},
                                                       @{thm <open>Encoder_Property_2<close>}]]"]
          \<open>The required encoder properties are in fact verified to be consistent
           with the formalization of @{term "phase\<^sub>0"}.\<close>
    \<close>}

The references \<open>@{...}\<close>, called antiquotation, allow us not only to reference to 
formal concepts, they are checked for consistency and there are also antiquotations that 
print the formally checked content (\<^eg>, the statement of a theorem). 
\<close>

subsection\<open>Exporting Claims of the Requirements Specification.\<close>

text\<open>By definition, the main purpose of the requirement specification is the identification of 
the safety requirements. As an example, we state the required precision of an odometric function: 
for any normally behaved distance function \<open>df\<close>, and any representable and valid 
sampling sequence that can be constructed for \<open>df\<close>, we require that the difference 
between the physical distance and distance calculable from the @{term Odometric_Position_Count}
is bound by the minimal resolution of the odometer.

   @{theory_text [display]\<open>
        text*[R5::safety_requirement]\<open>We can now state ... \<close>
        definition  Odometric_Position_Count_precise :: "(shaft_encoder_state list\<Rightarrow>output)\<Rightarrow>bool"
        where "Odometric_Position_Count_precise odofunction \<equiv>
                   (\<forall> df. \<forall>S.  normally_behaved_distance_function df 
                          \<longrightarrow> representable S
                          \<longrightarrow> valid_sampling S df
                          \<longrightarrow> (let pos = uint(Odometric_Position_Count(odofunction S))
                               in \<bar>df((length S - 1)*\<delta>t\<^sub>o\<^sub>d\<^sub>o) - (\<delta>s\<^sub>r\<^sub>e\<^sub>s * pos)\<bar> \<le> \<delta>s\<^sub>r\<^sub>e\<^sub>s))"

        update_instance*[R5::safety_requirement,
                         formal_definition:="[@{thm \<open>Odometric_Position_Count_precise_def\<close>}]"]    
   \<close>}

By \<^theory_text>\<open>update_instance*\<close>, we book the property \<open>Position_Count_precise_def\<close> as 
\<^onto_class>\<open>safety_requirement\<close>, a specific sub-class of \<^onto_class>\<open>requirement\<close>s
requesting a formal definition in Isabelle.\<close>

subsection\<open>Exporting Derived Requirements.\<close>

text\<open>Finally, we discuss the situation where the verification team discovered a critical side-condition 
for a major theorem necessary for the safety requirements; this was in our development the case for
the condition labelled ``\<open>**\<close>'' in @{docitem verific}. The current CENELEC standard clearly separates
``requirement specifications'' from ``verification reports,'' which is probably motivated 
by the overall concern of organizational separation and of document consistency. While this 
document organization is possible in \<^isadof>, it is in our experience often counter-productive 
in practice: organizations tend to defend their documents because the impact of changes is more and more
difficult to oversee. This effect results in a dramatic development slow-down and an increase of
costs. Furthermore, these barriers exclude situations where developers perfectly know, for example,
invariants, but can not communicate them to the verification team because the precise formalization
is not known in time. Rather than advocating document separation, we tend to integrate these documents,
keep proof as close as possible to definitions, and plead for consequent version control of the
integrated source, together with the proposed methods to strengthen the links between the informal
and formal parts by anti-quotations and continuous ontological checking. Instead of separation
of the documents, we would rather emphasize the \<^emph>\<open>separation of the views\<close> of the different 
document representations. Such views were systematically generated out of the integrated source in 
different PDF versions and for each version, document specific consistency guarantees can be 
automatically enforced.

In our case study, we define this condition as predicate, declare an explanation of it as
\<^onto_class>\<open>SRAC\<close> (CENELEC for: safety-related application condition; ontologically, this is a
derived class from  \<^onto_class>\<open>requirement\<close>.) and add the definition of the predicate into the
document instance as described in the previous section.\<close>



chapter\<open>Appendix\<close>
text\<open>
\<^item> \<open>@{thm refl}\<close> : @{thm refl}
\<^item> \<open>@{thm [source] refl}\<close> : @{thm [source] refl}
\<^item> \<open>@{thm[mode=Rule] conjI}\<close> : @{thm[mode=Rule] conjI}
\<^item> \<open>@{file "mini_odo.thy"}\<close> : @{file "mini_odo.thy"}
\<^item> \<open>@{value "3+4::int"}}\<close> : @{value "3+4::int"}
\<^item> \<open>@{const hd}\<close> : @{const hd}
\<^item> \<open>@{theory HOL.List}\<close> : @{theory HOL.List}s
\<^item> \<open>@{tserm "3"}\<close> : @{term "3"}
\<^item> \<open>@{type bool}\<close> : @{type bool}
\<^item> \<open>@{thm term [show_types] "f x = a + x"}\<close> : @{term [show_types] "f x = a + x"}
\<close>

text\<open>Examples for declaration of typed doc-classes "assumption" (sic!) and "hypothesis" (sic!!),
     concepts defined in the underlying ontology @{theory "Isabelle_DOF-Ontologies.CENELEC_50128"}. \<close>
text*[ass2::assumption, long_name="Some ''assumption one''"] \<open> The subsystem Y is safe. \<close>
text*[hyp1::hypothesis] \<open> \<open>P \<noteq> NP\<close> \<close>
  
text\<open>  
   A real example fragment from a larger project, declaring a text-element as a
   "safety-related application condition", a concept defined in the 
   @{theory "Isabelle_DOF-Ontologies.CENELEC_50128"} ontology:\<close>  

text*[hyp2::hypothesis]\<open>Under the assumption @{assumption \<open>ass2\<close>} we establish the following: ... \<close>

text*[ass122::SRAC, long_name="Some ''ass122''"] 
\<open> The overall sampling frequence of the odometer subsystem is therefore 14 khz, 
  which includes sampling, computing and result communication times... \<close>

text*[ass123::SRAC] 
\<open> The overall sampling frequence of the odometer subsystem is therefore 14 khz, 
  which includes sampling, computing and result communication times... \<close>

text*[ass124::EC, long_name="Some ''ass124''"] 
\<open> The overall sampling frequence of the odometer subsystem is therefore 14 khz, 
  which includes sampling, computing and result communication times... \<close>
  
text*[t10::test_result] 
\<open> This is a meta-test. This could be an ML-command that governs the external 
  test-execution via, \<^eg>, a makefile or specific calls to a test-environment or test-engine. \<close>


text \<open> Finally some examples of references to doc-items, i.e. text-elements 
       with declared  meta-information and status. \<close> 

text \<open> As established by @{test_result \<open>t10\<close>}\<close>
text \<open> the               @{test_result \<open>t10\<close>}                      
       as well as the    @{SRAC \<open>ass122\<close>}\<close>  
text \<open> represent a justification of the safety related applicability 
       condition @{SRAC \<open>ass122\<close>} aka exported constraint @{EC \<open>ass122\<close>}.\<close> 

text \<open> due to notational conventions for antiquotations, one may even write:

       "represent a justification of the safety related applicability
        condition \<^SRAC>\<open>ass122\<close> aka exported constraint \<^EC>\<open>ass122\<close>."\<close> 

(*<*)   
end
(*>*)
