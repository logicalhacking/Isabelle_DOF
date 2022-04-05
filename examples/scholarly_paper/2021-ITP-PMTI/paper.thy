(*<*)
theory "paper"
  imports "Isabelle_DOF.scholarly_paper"
begin

open_monitor*[this::article]

declare[[ strict_monitor_checking  = false]]
declare[[ Definition_default_class = "definition"]]
declare[[ Lemma_default_class      = "lemma"]]
declare[[ Theorem_default_class    = "theorem"]]

define_shortcut* hol      \<rightleftharpoons> \<open>HOL\<close>
                 isabelle \<rightleftharpoons> \<open>Isabelle/HOL\<close>
                 dof      \<rightleftharpoons> \<open>Isabelle/DOF\<close>
                 LaTeX    \<rightleftharpoons> \<open>LaTeX\<close>
                 html     \<rightleftharpoons> \<open>HTML\<close>
                 csp      \<rightleftharpoons> \<open>CSP\<close>      \<comment>\<open>obsolete\<close>
                 holcsp   \<rightleftharpoons> \<open>HOL-CSP\<close>  \<comment>\<open>obsolete\<close> 

ML\<open>

fun boxed_text_antiquotation name (* redefined in these more abstract terms *) =
    DOF_lib.gen_text_antiquotation name DOF_lib.report_text 
                           (fn ctxt => DOF_lib.string_2_text_antiquotation ctxt
                                       #> DOF_lib.enclose_env false ctxt "isarbox")

val neant = K(Latex.text("",\<^here>))

fun boxed_theory_text_antiquotation name (* redefined in these more abstract terms *) =
    DOF_lib.gen_text_antiquotation name DOF_lib.report_theory_text 
                           (fn ctxt => DOF_lib.string_2_theory_text_antiquotation ctxt 
                                        #> DOF_lib.enclose_env false ctxt "isarbox"
                                        (* #> neant *)) (*debugging *)

fun boxed_sml_text_antiquotation name  =
    DOF_lib.gen_text_antiquotation name (K(K())) 
                           (fn ctxt => Input.source_content 
                                        #> Latex.text 
                                        #> DOF_lib.enclose_env true ctxt "sml") 
                           (* the simplest conversion possible *)

fun boxed_pdf_antiquotation name =
    DOF_lib.gen_text_antiquotation name (K(K())) 
                           (fn ctxt => Input.source_content 
                                        #> Latex.text 
                                        #> DOF_lib.enclose_env true ctxt "out") 
                           (* the simplest conversion possible *)

fun boxed_latex_antiquotation name =
    DOF_lib.gen_text_antiquotation name (K(K())) 
                           (fn ctxt => Input.source_content 
                                        #> Latex.text 
                                        #> DOF_lib.enclose_env true ctxt "ltx") 
                           (* the simplest conversion possible *)

fun boxed_bash_antiquotation name =
    DOF_lib.gen_text_antiquotation name (K(K())) 
                           (fn ctxt => Input.source_content 
                                        #> Latex.text 
                                        #> DOF_lib.enclose_env true ctxt "bash") 
                           (* the simplest conversion possible *)
\<close>

setup\<open>(* std_text_antiquotation        \<^binding>\<open>my_text\<close> #> *)
      boxed_text_antiquotation         \<^binding>\<open>boxed_text\<close> #>
      (* std_text_antiquotation        \<^binding>\<open>my_cartouche\<close> #> *)
      boxed_text_antiquotation         \<^binding>\<open>boxed_cartouche\<close> #>
      (* std_theory_text_antiquotation \<^binding>\<open>my_theory_text\<close>#> *)
      boxed_theory_text_antiquotation  \<^binding>\<open>boxed_theory_text\<close> #>

      boxed_sml_text_antiquotation     \<^binding>\<open>boxed_sml\<close> #>
      boxed_pdf_antiquotation          \<^binding>\<open>boxed_pdf\<close> #>
      boxed_latex_antiquotation        \<^binding>\<open>boxed_latex\<close>#>
      boxed_bash_antiquotation         \<^binding>\<open>boxed_bash\<close> 
     \<close>

(*>*)

title*[tit::title]\<open>A Framework for Proving Ontology-Relations and Runtime Testing Ontology Instances\<close>


text*[idir::author,
        email       ="\<open>idir.aitsadoune@centralesupelec.fr\<close>",
        orcid       ="''0000-0002-6484-8276''",
        affiliation ="\<open>LMF, CentraleSupélec, Université Paris-Saclay, Paris, France\<close>"]\<open>Idir Ait-Sadoune\<close>

text*[nic::author,
        email       ="\<open>nicolas.meric@universite-paris-saclay.fr\<close>",
        orcid       ="''0000-0002-0756-7072''",
        affiliation ="\<open>LMF, Université Paris-Saclay, Paris, France\<close>"]\<open>Nicolas Méric\<close>
text*[bu::author,
        email       ="\<open>wolff@universite-paris-saclay.fr\<close>",
        affiliation = "\<open>LMF, Université Paris-Saclay, Paris, France\<close>"]\<open>Burkhart Wolff\<close>
           
text*[abs::abstract, keywordlist="[\<open>Ontologies\<close>,\<open>Formal Documents\<close>,\<open>Formal Development\<close>,\<open>Isabelle/HOL\<close>,\<open>Ontology Mapping\<close>]"]
\<open>  \<^dof> is a novel ontology framework on top of Isabelle 
   @{cite "brucker.ea:isabelledof:2019" and "brucker.ea:isabelle-ontologies:2018"}. 
   \<^dof>  allows for the formal development of ontologies as well as continuous checking that
   a formal document under development conforms to an underlying ontology. 
   Such a document may contain text and code elements as well as formal Isabelle definitions and proofs.
   Thus, \<^dof> is designed to annotate and interact with typed meta-data 
   within formal developments in Isabelle.  

%   While prior versions of \<^dof> provided already a mechanism to check ontological \<^emph>\<open>rules\<close>  
%   (in OWL terminology) or \<^emph>\<open>class invariants\<close> (in UML/OCL terminology) via hand-written SML test-code,
%   we provide in this paper a novel mechanism to specify \<^emph>\<open>invariants\<close> in \<^hol> via a reflection
%   mechanism. 
   In this paper we extend  \<^dof> with \<^emph>\<open>invariants\<close> via a reflection mechanism,
   which serve as equivalent to the concept of ontological \<^emph>\<open>rules\<close> (in OWL terminology) or
   \<^emph>\<open>class invariants\<close> (in UML/OCL terminology).
   This allows for both efficient run-time checking of abstract properties of formal
   content \<^bold>\<open>as well as\<close> formal proofs that establish mappings between different ontologies in 
   general and specific ontology instances in concrete cases. 
   With this feature widely called \<^emph>\<open>ontology mapping\<close> in the literature, our framework paves the 
   way for a deeper integration of ontological information in, for example,
   the articles of the Archive of Formal Proofs.
  
\<close>


section*[introheader::introduction]
       \<open> Introduction \<close>
text*[introtext::introduction]\<open>
The linking of \<^emph>\<open>formal\<close> and \<^emph>\<open>informal\<close> information is perhaps the most pervasive challenge 
in the digitization of knowledge and its propagation. Unsurprisingly, this problem reappears 
in the libraries with formalized mathematics and engineering such as the Isabelle Archive of 
Formal Proofs @{cite "AFP-ref22"}, which passed the impressive numbers of 650 articles, 
written by 420 authors at the beginning of 2022. Still, while the problem of logical consistency 
even under system-changes and pervasive theory evolution is technically solved via continuous 
proof-checking, the problem of knowledge retrieval and of linking semi-formal explanations to 
definitions and proofs remains largely open.

The \<^emph>\<open>knowledge\<close> problem of the increasingly massive \<^emph>\<open>digital information\<close> available
incites numerous research efforts summarized under the labels ``semantic web'', 
``integrated document management'', or any form of advanced ``semantic'' text processing. 
These technologies are increasingly important  in jurisprudence, medical research and 
life-sciences in order to tame their respective publication tsunamies. The central role 
in these technologies is played by \<^emph>\<open>document ontologies\<close>, \<^ie>, a machine-readable form 
of meta-data attached to document-elements as well as their document discourse. In order 
to make these techniques applicable to the area of \<^emph>\<open>formal theory development\<close>, 
the following is needed: \<^vs>\<open>0.2cm\<close>

\<^item> a general mechanism to define and develop \<^emph>\<open>domain-specific\<close> ontologies,
\<^item> ... that should be adapted to entities occurring in formal theories,
  \<^ie>, provide built-in support for types, terms, theorems, proofs, etc.,
\<^item> ways to annotate meta-data generated by ontologies to the document elements,
  as ``deep'' as possible, together with strong validation checks,
\<^item> a smooth integration into the theory document development process, and
\<^item> ways to relate ontologies and ontology-conform documents along different
  ontologies by \<^emph>\<open>ontological mappings\<close> and \<^emph>\<open>data translations\<close>
  @{footnote \<open>We follow throughout this text the terminology established in 
              @{cite "books/daglib/0032976"}, pp. 39 ff.\<close>}.
\<close>

text\<open>  \<^vs>\<open>-0.2cm\<close>
Recently, \<^dof> @{cite "brucker.ea:isabelledof:2019" and "brucker.ea:isabelle-ontologies:2018"}
\<^footnote>\<open>The official releases are available at \<^url>\<open>https://zenodo.org/record/3370483#.YfWg6S-B1qt\<close>, the
  developer version at \<^url>\<open>https://github.com/logicalhacking/Isabelle_DOF\<close>.\<close> 
has been designed as an Isabelle component that attempts to answer these needs. 
 \<^dof> generates from  ontology definitions directly integrated into Isabelle theories
typed meta-data, that may be annotated to a number of document elements and that were 
validated ``on-the-fly'' during the general continuous type and proof-checking process 
in an IDE (Isabelle/PIDE). Thus, we extend the document-centric view on code, definitions, 
proofs, text-elements, etc., prevailing in the Isabelle system framework.

In more detail, \<^dof> introduces a number of ``ontology aware'' text-elements with analogous 
syntax to standard ones. The difference is a bracket with meta-data of the form:
@{theory_text [display,indent=5, margin=70] 
\<open>text*[label::classid, attr\<^sub>1=E\<^sub>1, ... attr\<^sub>n=E\<^sub>n]\<open> some semi-formal text \<close>
ML*[label::classid, attr\<^sub>1=E\<^sub>1, ... attr\<^sub>n=E\<^sub>n]\<open> some SML code \<close>
...\<close>}
In these \<^dof> elements, a meta-data object is created and associated to it. This 
meta-data can be referenced via its label and used in further computations in text or code.
%; the details will be explained in the subsequent section. 

Admittedly, Isabelle is not the first system that comes into one's mind when writing a scientific 
paper, a book, or a larger technical documentation. However, it has a typesetting system inside 
which is in the tradition of document generation systems such as mkd, Document! X, Doxygen, 
Javadoc, etc., and which embed formal content such as formula pretty-prints into semi-formal text 
or code. The analogous mechanism the Isabelle system provides is a machine-checked macro 
called \<^emph>\<open>antiquotation\<close> that depends on the logical context of the document element.

With standard Isabelle antiquotations, for example, the following text element
of the integrated source will appear  in Isabelle/PIDE as follows:
@{theory_text [display,indent=5, margin=70] 
\<open>text\<open> According to the reflexivity axiom @{thm refl}, we obtain in \<Gamma>
      for @{term "fac 5"} the result @{value "fac 5"}.\<close>\<close>}
In the corresponding generated \<^LaTeX> or HTML output, this looks like this:
@{theory_text [display,indent=5, margin=70]
\<open>According to the reflexivity axiom \<open>x = x\<close>,
we obtain in \<Gamma> for \<open>fac 5\<close> the result \<open>120\<close>.\<close>}
where the meta-texts \<open>@{thm refl}\<close> (``give the presentation of theorem `refl'\,\!''), 
\<open>@{term "fac 5"}\<close> (``parse and type-check `fac 5' in the previous logical context'')
and \<open>@{value "fac 5"}\<close> (``compile and execute `fac 5' according to its
definitions'') are built-in antiquotations in \<^hol>. 

One distinguishing feature of \<^dof> is that specific antiquotations \<^emph>\<open>were generated from
an ontology\<close> rather than being hard-coded into the Isabelle system infrastructure.
\<close>

(*
text
\<open>

%too long !
This leads to an evolution strategy we call "integrate the document, strengthen the
links" (IDSL): integrate all sources into the Isabelle document model, and 
replace \<^emph>\<open>text\<close> by appropriate \<^emph>\<open>meta-text\<close> wherever you can.
Developers are rewarded for applying IDSL by specific IDE-support, 
by additional semantic checks and thus by a more robust document consistency 
which is easier to maintain under collaborative changes.
%For example, if someone changes the theorem name, an error would result when processing
%the text. On the other hand, \<open>@{value "fac 5"}\<close> would not guard against a change of definition 
%of \<open>fac\<close>. If this is desirable, an antiquotation like \<open>@{assert "fac 5 = 120"}\<close> would be more appropriate.
%too long !
Antiquotations do not only occur in text-elements in Isabelle; they are also heavily used 
in the code-elements of Isabelle's SML implementation, or were specifically supported in 
C-program contexts in Isabelle/C @{cite "Tuong-IsabelleC:2019"}. 

However, programming antiquotations on the intern Isabelle API's is nothing for the 
faint-hearted. Recently, \<^dof> @{cite "brucker.ea:isabelledof:2019" and "brucker.ea:isabelle-ontologies:2018"} 
has been designed as an Isabelle component that \<^emph>\<open>generates\<close> antiquotation languages
from a more abstract description, namely an \<^emph>\<open>ontology\<close> that provides typed meta-data
and typed reference mechanisms inside text- and ML-contexts. 

*)

text\<open>As novel contribution, this work extends prior versions of \<^dof> by 
\<^enum> support of antiquotions in a new class of contexts, namely \<^emph>\<open>term contexts\<close> 
  (rather than SML code or semi-formal text). Thus, annotations generated
  from  \<^dof> may also occur in \<open>\<lambda>\<close>-terms used to denote meta-data. 
\<^enum> formal, machine-checked invariants on meta-data, which correspond to the concept of 
  ``rules'' in OWL~ @{cite "OWL2014"} or ``constraints'' in UML, and which can be specified in 
  common \<^hol> \<open>\<lambda>\<close>-term syntax.
\<close>
text\<open> For example, the \<^dof> evaluation command taking a \<^hol>-expression:
@{theory_text [display,indent=5, margin=70]
\<open>value*[ass::Assertion, relvce=2::int]
      \<open>filter (\<lambda> \<sigma>. relvce \<sigma> > 2) @{Assertion-instances}\<close>\<close>}
where \<^dof> command \<open>value*\<close> type-checks, expands in an own validation phase
the \<open>Assertion-instances\<close>-term antiquotation, and evaluates the resulting \<^hol> expression
above. Assuming an ontology providing the class \<open>Assertion\<close> having at least the
integer attribute \<open>relvce\<close>, the command finally creates an instance of \<open>Assertion\<close> and 
binds this to the label \<open>ass\<close> for further use.

Beyond the gain of expressivity in \<^dof> ontologies, term-antiquotations pave the way 
for advanced queries of elements inside an integrated source, and invariants 
allow for formal proofs over the relations/translations of ontologies and ontology-instances.
The latter question raised scientific interest under the label ``ontology mapping'' for 
which we therefore present a formal solution. To sum up, we completed \<^dof> to
a fairly rich, ITP-oriented ontology language, which is a concrete proposal for the 
ITP community allowing a deeper structuring of mathematical libraries
such as the Archive of Formal Proofs (AFP).
\<close>

(*<*)
declare_reference*[casestudy::text_section]
(*>*)

section*[bgrnd::background,main_author="Some(@{docitem ''bu''}::author)"] \<open> Background\<close>
(*
subsection\<open>Isabelle/DOF Design and Implementation\<close>
text\<open>
  In this section, we provide a guided tour through the underlying technologies of this paper: 
  \begin{inparaenum} 
   \item Isabelle and Isabelle/HOL, 
   \item \<^dof> and its Ontology Definition Language (ODL).
  \end{inparaenum}
\<close>
subsection*[bgrnd_isabelle::text_section]\<open>Isabelle and HOL\<close>
text\<open>
  While still widely perceived as an interactive theorem proving environment, Isabelle 
  @{cite "nipkow.ea:isabelle:2002"} has become a generic system framework providing 
  an infrastructure for plug-ins. This comprises extensible 
  state components, extensible syntax, code-generation, and advanced documentation support. 
  The plugin Isabelle/HOL offers a modeling language similar to functional programming languages
  extended by a logic and automated proof and animation techniques.
\<close>
*)
subsection*[bgrnd_isadof::background]\<open>The \<^dof> Framework\<close>
text\<open>
  \<^dof>~@{cite "brucker.ea:isabelle-ontologies:2018" and 
              "brucker.ea:isabelledof:2019"} 
  is a document ontology framework that extends \<^isabelle>.
  \<^dof> offers basically two things: a language called Ontology Definition Language (ODL)
  to \<^emph>\<open>specify\<close> a formal ontology,
  and ways to \<^emph>\<open>annotate\<close> an integrated document written in \<^isabelle> with the specified
  meta-data. Additionally, \<^dof> generates from an ontology a family of 
  \<^emph>\<open>antiquotations\<close> allowing to establish  machine-checked links between classified entities. 
%  Unlike UML, however, \<^dof> allows for integrated documents with informal and formal elements
%  including the necessary management of logical contexts. 

  The perhaps most attractive aspect of \<^dof> is its deep integration into the IDE of Isabelle 
  (Isabelle/PIDE), which allows a hypertext-like navigation as well as fast user-feedback
  during development and evolution of the integrated source. This includes rich editing support, 
  including on-the-fly semantics checks, hinting, or auto-completion. 
  \<^dof> supports \<^LaTeX>-based document generation as well as ontology-aware ``views'' on 
  the integrated document, \<^ie>, specific versions of generated PDF addressing, 
  for example, different stake-holders. 
\<close>

(*<*)
figure*[isadof_screenshot::figure, relative_width="100", src="''figures/cicm2018-combined''"]\<open>
  The \<^dof> IDE (left) and the corresponding PDF(right).
\<close>
text*[description_scrrenshot::background]\<open>
  @{docitem \<open>isadof_screenshot\<close>} shows \<^dof> in action: the left-hand side shows the IDE of 
  \<^dof> in the context of a user session maintaining our case study 
  (see @{docitem (unchecked) "casestudy"}) 
  where a user is editing a semi-formal requirement. The right-hand side show the 
  generated PDF document that can be used within a certification process. 
\<close>
(*>*)

subsection*[bgrnd_ODL::background]\<open>A Guided Tour through ODL\<close>
text\<open>
  \<^dof> provides a strongly typed ODL that provides the usual 
  concepts of ontologies such as
  \<^item> \<^emph>\<open>document class\<close> (using the \<^theory_text>\<open>doc_class\<close> keyword) that describes a concept,
  \<^item> \<^emph>\<open>attributes\<close> specific to document classes (attributes might be initialized with default 
    values), and
  \<^item> a special link, the reference to a super-class,
    establishes an \<^emph>\<open>is-a\<close> relation between classes.
%  classes may refer to other classes via a regular expression in an optional \<^emph>\<open>where\<close> clause 
%    (a class with a where clause is called \<^emph>\<open>monitor\<close>).


  \fixIsarList The types of attributes are \<^hol>-types. Thus, ODL can refer to any predefined type 
  from the \<^hol> library, \<^eg>, \<^type>\<open>string\<close>, \<^type>\<open>int\<close> as well as parameterized types, \<^eg>, 
  \<^type>\<open>option\<close>,  \<^type>\<open>list\<close>. As a consequence of the Isabelle document model, ODL definitions 
  may be arbitrarily mixed with standard \<^hol> type definitions. Document class definitions are 
  \<^hol>-types, allowing for formal \<^emph>\<open>links\<close> to and between ontological concepts. For example, the 
  basic concept of requirements from CENELEC 50128~@{cite "bsi:50128:2014"} is captured in ODL as 
  follows:
  @{theory_text [display,indent=5, margin=70]
\<open>doc_class requirement = text_element +   (* derived from text_element    *)
          long_name   ::"string option"  (* an optional string attribute *) 
          is_concerned::"role set"       (* roles working with this req. *)\<close>}
  This ODL class definition maybe part of one or more Isabelle theory-files capturing the entire
  ontology definition. Isabelle's session management allows for pre-compiling them before being 
  imported in the actual target documentation required to be compliant to this ontology. 

%\vspace{-0.7cm}\<close>

side_by_side_figure*["text-elements"::side_by_side_figure,anchor="''fig-Req-Def-ex''",
                      caption="''A Text-Element as Requirement.''",relative_width="48",
                      src="''figures/Req-Def-ex''",anchor2="''fig-Req-Appl-ex''",
                      caption2="''Referencing a Requirement.''",relative_width2="48",
                      src2="''figures/Req-Appl-ex''"]\<open>Referencing a Requirement. \<close>

text\<open>\autoref{text-elements} shows an ontological annotation of a requirement and the referencing
  via an antiquotation \<^theory_text>\<open>requirement \<open>req1\<close>\<close> generated by \<^dof> from the above 
  class definition. Undefined or ill-typed references were rejected, the high-lighting displays 
  the hyperlinking which is activated on a click. Revising the actual definition of \<open>requirement\<close>, 
  it suffices to click on its keyword: the IDE will display the class-definition and its surrounding 
  documentation in the ontology.\<close>

(*

text\<open>\<^dof>'s generated antiquotations are part of a general mechanism of  
  Isabelle's standard antiquotations heavily used in various papers and technical reports.
  For example, in the following informal text, the antiquotation \<^verbatim>\<open>thm refl\<close> refers  
  to the reflexivity axiom from HOL: 
@{theory_text [display,indent=10, margin=70]
\<open>
  text<Open>According to the reflexivity axiom <@>{thm refl}, we obtain in \<Gamma>
         for <@>{term <Open>fac 5<Close>} the result <@>{value <Open>fac 5<Close>}.<Close>\<close>}
  In the PDF output, this is represented as follows:
  \begin{out}
  According to the reflexivity axiom $x = x$, we obtain in \<open>\<Gamma>\<close> for $\operatorname{fac} 5$ the result $120$.
  \end{out}
  The antiquotation \inlineisar|<@>{value <Open>fac 5<Close>}| refers to a function that is defined in the 
  preceding logical context (and parsed as inner syntax) to compute the value of $5!$, \ie, $120$. 
  Summing up, antiquotations can refer to formal content, can be type-checked before being displayed 
  and can be used for calculations before actually being typeset. All these features can be
  used for the calculation of attribute values (as in @{docitem \<open>text-elements\<close>}, observe the value 
  \<open>UNIV\<close> used to set the attribute \<open>is_concerned\<close> is a HOL-constant denoting the universal set).

  Finally, for each ontological concept, a custom representation, using \<^LaTeX>-notation, for the 
  generated PDF document can be defined. The latter includes, \<^eg>, the possibility to automatically 
  generated glossaries or lists of concepts. 
\<close>

*)
(*<*)
type_synonym A = int 
type_synonym B = int
record T =
  x :: A
  y :: B

term "\<lparr>x = a,y = b\<rparr>"
(*>*)

subsection\<open>Meta-Objects as Extensible Records\<close>
(* too fat ? what do we need of this ? *)
text\<open>
\<^isabelle> supports both fixed and schematic records at the level of terms and 
types. The notation for terms and types is as follows:
\<^item> fixed record terms     \<^term>\<open>\<lparr>x = a,y = b\<rparr>\<close>; fixed record types \<open>\<lparr>x::A, y::B\<rparr>\<close>,
\<^item> schematic record terms \<^term>\<open>\<lparr>x = a,y = b, \<dots> = m::'a\<rparr>\<close>;
  schematic record types: \<open>\<lparr>x::A, y::B, \<dots> = 'a\<rparr>\<close> which were usually abbreviated
  to \<^typ>\<open>'a T_scheme\<close>,
\<^item> selectors are written \<^term>\<open>x(R::'a T_scheme)\<close>, \<^term>\<open>y(R::'a T_scheme)\<close>, and
\<^item> updates were denoted \<^theory_text>\<open>r\<lparr>x := a\<rparr>\<lparr>y := b\<rparr>\<close> or just \<^term>\<open>r\<lparr>x:=a, y:=b\<rparr>\<close>.
\<close>

text\<open> ... where the so-called more-field \<open>\<dots>\<close> is used to ``fill-in'' record-extensions.
Schematic record types @{cite "naraschewski1998object"} allow for simulating object-oriented features such as 
(single-)inheritance while maintaining a compositional style of verification: 
it is possible to prove a property \<^term>\<open>P (a::'a T_scheme)\<close>
which will remain true for all extensions (which are just instances of the
\<^typ>\<open>'a T_scheme\<close>-type). 

\<close>

text\<open>In \<^dof>, \<^verbatim>\<open>onto_class\<close>es and the logically equivalent  \<^verbatim>\<open>doc_class\<close>es were
represented by schematic record types and instances thereof by schematic terms. 
Invariants of an \<^verbatim>\<open>onto_class\<close> are thus predicates over schematic record
types and can therefore be inherited in a subclass. \<^dof> handles the parametric  
polymorphism implicitly. 
\<close>

subsection\<open>Advanced Evaluation in Isabelle\<close>
text\<open>Besides the powerful, but relatively slow rewriting-based proof method 
\<^theory_text>\<open>simp\<close>, there are basically two other techniques for the evaluation of terms:
\<^item> evaluation via reflection into SML (\<^theory_text>\<open>eval\<close>), and
\<^item> normalization by evaluation @{cite "AehligHN12"} (\<^theory_text>\<open>nbe\<close>).\<close>

text\<open>
The former is based on a nearly one-to-one compilation of datatype specification 
constructs and recursive  function definitions into SML datatypes and functions.
The generated code is directly compiled by the underlying SML compiler of the 
Isabelle platform. This way, pattern-matching becomes natively compiled rather
than interpreted as in the matching process of \<^theory_text>\<open>simp\<close>. @{cite "AehligHN12"} 
describes scenarios where \<^theory_text>\<open>eval\<close> is five orders of magnitude faster than \<^theory_text>\<open>simp\<close>.
However, it is restricted to ground terms. 

The latter is based on a compilation of datatype specifications into a uniform
data-universe enriched by closures and explicit variables. Recursive function 
definitions in \<^hol> were compiled to SML functions where the argument terms
were represented in the data-universe. Pattern-matching is still compiled to
native functions executed if closures are completed.  \<^theory_text>\<open>nbe\<close> is not restricted
to ground terms, but lies in its efficiency between  \<^theory_text>\<open>simp\<close> and  \<^theory_text>\<open>eval\<close>.

\<^dof> uses a combination of these three techniques in order to check invariants
for ontological classes on the fly during editing, paving the way for both
a uniform specification language of ontological data --- namely \<^hol> --- as
well as the possibility to \<^emph>\<open>prove\<close> properties over and relations between
classes.\<close>


section*[invariants::technical,main_author="Some(@{docitem ''nic''}::author)"] 
\<open>Term-Context Support, Invariants and Queries in DOF\<close>

(*<*)
(* Ontology example for mathematical papers *)

doc_class myauthor =
  email :: "string" <= "''''"
doc_class mytext_section =
  authored_by :: "myauthor set" <= "{}"
  level :: "int option" <= "None"
doc_class myintro = mytext_section +
  authored_by :: "myauthor set"  <= "UNIV" 
  uses :: "string set"
  invariant author_finite :: "finite (authored_by \<sigma>)"
  and force_level :: "the (level \<sigma>) > 1"
doc_class myclaim = myintro +
  based_on :: "string list"
doc_class mytechnical = text_section +
  formal_results :: "thm list" 

datatype kind = expert_opinion | argument | "proof"

doc_class myresult = mytechnical +
  evidence :: kind
  property :: "thm list" <= "[]"
  invariant has_property :: "evidence \<sigma> = proof \<longleftrightarrow> property \<sigma> \<noteq> []"
doc_class myconclusion = text_section +
  establish :: "(myclaim \<times> myresult) set"
  invariant establish_defined :: "\<forall> x. x \<in> Domain (establish \<sigma>)
                      \<longrightarrow> (\<exists> y \<in> Range (establish \<sigma>). (x, y) \<in> establish \<sigma>)"

declare[[invariants_checking = true]]
declare[[invariants_checking_with_tactics = true]]

text*[church::myauthor, email="\<open>church@lambda.org\<close>"]\<open>\<close>

text*[proof1::myresult, evidence = "proof", property="[@{thm \<open>HOL.refl\<close>}]"]\<open>\<close>

text*[proof2::myresult, evidence = "proof", property="[@{thm \<open>HOL.sym\<close>}]"]\<open>\<close>

term*\<open>@{myauthor \<open>church\<close>}\<close>
(*term*\<open>@{myauthor \<open>churche\<close>}\<close>*)

value*\<open>email @{myauthor \<open>church\<close>}\<close>
(*value*\<open>email @{myauthor \<open>churche\<close>}\<close>*)

(*assert*\<open>@{myresult \<open>proof1\<close>} = @{myresult \<open>proof2\<close>}\<close>*)

(*text*[intro1::myintro, authored_by = "{@{myauthor \<open>church\<close>}}", level = "Some 0"]\<open>\<close>*)

(*text*[claimNotion::myclaim, authored_by = "{@{myauthor \<open>church\<close>}}", based_on= "[\<open>Notion1\<close>, \<open>Notion2\<close>]", level = "Some 0"]\<open>\<close>*)

text*[intro2::myintro, authored_by = "{@{myauthor \<open>church\<close>}}", level = "Some 2"]\<open>\<close>

declare[[invariants_checking = false]]
declare[[invariants_checking_with_tactics = false]]
(*>*)

text\<open>
  To offer a smooth integration into the \<^emph>\<open>formal\<close> theory development process,
  \<^isabelle> should be able to dynamically interpret the source document.
  But the specific antiquotations introduced by \<^dof> are not directly recognized
  by \<^isabelle>, and the process of term checking and evaluation must be enriched.
  Previous works~@{cite "brucker.ea:isabelle-ontologies:2018" and "brucker.ea:isabelledof:2019"}
  added a validation step for the SML and semi-formal text contexts.
  To support \<^dof> antiquotations in the term contexts, the validation step should
  be improved and a new step, which we call \<^emph>\<open>elaboration\<close> must be added to allow
  these antiquotations in \<open>\<lambda>\<close>-terms.
  The resulting process encompasses the following steps:
    \<^item> Parsing of the term which represents the object in \<^hol>,
    \<^item> Typeinference/Typechecking of the term,
    \<^item> Ontological validation of the term: the meta-data of term antiquotations is 
      parsed and checked in the logical context,
    \<^item> Elaboration of term antiquotations: depending of the antiquotation specific
      elaboration function, the antiquotations containing references were replaced,
      for example, by the object they refer to in the logical context,
    \<^item> Generation of markup information for the Isabelle/PIDE, and
    \<^item> Code generation:
      \<^item> Evaluation of \<^hol> expressions with ontological annotations,
      \<^item> Generation of ontological invariants processed simultaneously
        with the generation of the document (a theory in \<^hol>).

  \<^isabelle> provides inspection commands to type-check (the command \<^theory_text>\<open>term\<close>)
  and to evaluate a term (the command \<^theory_text>\<open>value\<close>).
  We provide the equivalent commands, respectively \<^theory_text>\<open>term*\<close> and \<^theory_text>\<open>value*\<close>, which 
  additionally support a validation and elaboration phase.
  We also provide an \<^theory_text>\<open>assert*\<close>-command which checks
  that the evaluation of a term returns \<^const>\<open>True\<close> and fails in other cases.
  Note that term antiquotations are admitted in all \<^dof> commands, not just
  \<^theory_text>\<open>term*\<close>, \<^theory_text>\<open>value*\<close> and \<^theory_text>\<open>assert*\<close>. 
\<close>

(*<*)
declare_reference*["type-checking-example"::side_by_side_figure]
(*>*)

text\<open>
  If we take back the example ontology for mathematical papers
  of~@{cite "brucker.ea:isabelledof:2019"} shown in \autoref{fig-ontology-example}
\begin{figure}
@{boxed_theory_text [display]
\<open>datatype kind = expert_opinion | argument | "proof"

doc_class myauthor =
  email :: "string" <= "''''"
doc_class mytext_section =
  authored_by :: "myauthor set" <= "{}"
  level :: "int option" <= "None"
doc_class myintro = mytext_section +
  authored_by :: "myauthor set"  <= "UNIV" 
  uses :: "string set"
  invariant author_finite :: "finite (authored_by \<sigma>)"
  and force_level :: "the (level \<sigma>) > 1"
doc_class myclaim = myintro +
  based_on :: "string list"
doc_class mytechnical = text_section +
  formal_results :: "thm list" 
doc_class myresult = mytechnical +
  evidence :: kind
  property :: "thm list" <= "[]"
  invariant has_property :: "evidence \<sigma> = proof \<longleftrightarrow> property \<sigma> \<noteq> []"
doc_class myconclusion = text_section +
  establish :: "(myclaim \<times> myresult) set"
  invariant establish_defined :: "\<forall> x. x \<in> Domain (establish \<sigma>)
                      \<longrightarrow> (\<exists> y \<in> Range (establish \<sigma>). (x, y) \<in> establish \<sigma>)"\<close>}
\caption{Excerpt of an example ontology for mathematical papers.}
\label{fig-ontology-example}
\end{figure}
  we can define some class instances for this ontology with the \<^theory_text>\<open>text*\<close> command,
  as in \autoref{fig-instances-example}.
\begin{figure}
@{boxed_theory_text [display]
\<open>text*[church::myauthor,email="\<open>church@lambda.org\<close>"]\<open>\<close>
text*[proof1::myresult,evidence="proof",property="[@{thm \<open>HOL.refl\<close>}]"]\<open>\<close>
text*[proof2::myresult,evidence="proof",property="[@{thm \<open>HOL.sym\<close>}]"]\<open>\<close>
text*[intro1::myintro,authored_by="{@{myauthor \<open>church\<close>}}",level="Some 0"]\<open>\<close>
text*[intro2::myintro,authored_by="{@{myauthor \<open>church\<close>}}",level="Some 2"]\<open>\<close>
text*[claimNotion::myclaim,authored_by="{@{myauthor \<open>church\<close>}}",
      based_on="[\<open>Notion1\<close>,\<open>Notion2\<close>]",level="Some 0"]\<open>\<close>\<close>}
\caption{Some instances of the classes of the ontology of \autoref{fig-ontology-example}.}
\label{fig-instances-example}
\end{figure}
  In the instance \<^theory_text>\<open>intro1\<close>, the term antiquotation  \<^theory_text>\<open>@{myauthor \<open>church\<close>}\<close>,
  or its equivalent notation \<^term>\<open>@{myauthor \<open>church\<close>}\<close>, denotes
  the instance \<^theory_text>\<open>church\<close> of the class \<^typ>\<open>myauthor\<close>,
  where \<^theory_text>\<open>church\<close> is a \<^hol>-string.
  One can now reference a class instance in a \<^theory_text>\<open>term*\<close> command.
  In the command  \<^theory_text>\<open>term*\<open>@{myauthor \<open>church\<close>}\<close>\<close>
  the term \<^term>\<open>@{myauthor \<open>church\<close>}\<close> is type-checked, \<^ie>, the command \<^theory_text>\<open>term*\<close> checks that
  \<^theory_text>\<open>church\<close> references a term of type \<^typ>\<open>myauthor\<close> against the global context.
  (see \<^side_by_side_figure>\<open>type-checking-example\<close>).
\<close>


side_by_side_figure*[
  "type-checking-example"::side_by_side_figure
  , anchor="''fig-term-type-checking-ex''"
  , caption="''church is an existing instance.''"
  , relative_width="48"
  , src="''figures/term-context-checking-example''"
  , anchor2="''fig-term-type-checking-failed-ex''"
  , caption2="''The churche instance is not defined.''"
  , relative_width2="48"
  , src2="''figures/term-context-failed-checking-example''"
]\<open>Type-checking of antiquotations in term context.\<close>

(*<*)
declare_reference*["evaluation-example"::side_by_side_figure]
(*>*)

text\<open>
  The command \<^theory_text>\<open>value*\<open>email @{author \<open>church\<close>}\<close>\<close>
  type-checks the antiquotation \<^term>\<open>@{myauthor \<open>church\<close>}\<close>,
  and then returns the value of the attribute \<^const>\<open>email\<close> for the \<^theory_text>\<open>church\<close> instance,
  \<^ie> the \<^hol> string \<^term>\<open>''church@lambda.org''\<close>
  (see \<^side_by_side_figure>\<open>evaluation-example\<close>).
\<close>

side_by_side_figure*[
  "evaluation-example"::side_by_side_figure
  , anchor="''fig-term-evaluation-ex''"
  , caption="''The evaluation succeeds and returns the value.''"
  , relative_width="48"
  , src="''figures/term-context-evaluation-example''"
  , anchor2="''fig-term-failed-evaluation-ex''"
  , caption2="''The evaluation fails, due to the undefined instance.''"
  , relative_width2="48"
  , src2="''figures/term-context-failed-evaluation-example''"
]\<open>Evaluation of antiquotations in a term context.\<close>

(*
figure*[
  "term-context-checking-example-figure"::figure
  , relative_width="99"
  , src="''figures/term-context-checking-example''"
]\<open>The invariant \<^theory_text>\<open>force_level\<close> of the class claim is inherited
  from the class \<^theory_text>\<open>introduction\<close> and is violated by the instance \<^theory_text>\<open>claimNotion\<close>.
\<close>

figure*[
  "term-context-evaluation-figure"::figure
  , relative_width="99"
  , src="''figures/term-context-evaluation-example''"
]\<open>The invariant \<^theory_text>\<open>force_level\<close> of the class claim is inherited
  from the class \<^theory_text>\<open>introduction\<close> and is violated by the instance \<^theory_text>\<open>claimNotion\<close>.
\<close>
*)

(*<*)
declare_reference*["term-context-equality-evaluation"::figure]
(*>*)

text\<open>
  Since term antiquotations are logically uninterpreted constants,
  it is possible to compare class instances logically. The assertion
  in the \<^figure>\<open>term-context-equality-evaluation\<close> fails:
  the two class instances \<^theory_text>\<open>proof1\<close> and \<^theory_text>\<open>proof2\<close> are not equivalent
  because their attribute \<^term>\<open>property\<close> differs.
  When \<^theory_text>\<open>assert*\<close> evaluates the term,
  the term antiquotations \<^term>\<open>@{thm \<open>HOL.refl\<close>}\<close> and \<^term>\<open>@{thm \<open>HOL.sym\<close>}\<close> are checked
  against the global context to validate that the \<^hol>-strings \<^term>\<open>\<open>HOL.refl\<close>\<close> and \<^term>\<open>\<open>HOL.sym\<close>\<close>
  reference existing theorems.

\<close>

figure*[
  "term-context-equality-evaluation"::figure
  , relative_width="80"
  , src="''figures/term-context-equality-evaluation-example''"
]\<open>Evaluation of the equivalence of two class instances.
\<close>

text\<open>
  The mechanism of term annotations is also used for the new concept of 
  invariant constraints which can be specified in common \<^hol> syntax.
  They were introduced by the keyword \<^theory_text>\<open>invariant\<close>
  in a class definition (recall \autoref{fig-ontology-example}).
  Following the constraints proposed in @{cite "brucker.ea:isabelle-ontologies:2018"}, 
  one can specify that any instance of a class \<^typ>\<open>myresult\<close>
  finally has a non-empty property list, if its \<^typ>\<open>kind\<close> is \<^const>\<open>proof\<close>
  (see the \<^theory_text>\<open>invariant has_property\<close>), or that 
  the relation between \<^typ>\<open>myclaim\<close> and \<^typ>\<open>myresult\<close> expressed in the attribute \<^const>\<open>establish\<close>
  must be defined when an instance
  of the class \<^typ>\<open>myconclusion\<close> is defined (see the \<^theory_text>\<open>invariant establish_defined\<close>).

  In \autoref{fig-ontology-example}, the \<^theory_text>\<open>invariant author_finite\<close> of the class \<^typ>\<open>myintro\<close> 
  enforces that the user defines the \<^const>\<open>authored_by\<close> set with some valid meta-data of type \<open>myauthor\<close>.
  The \<open>\<sigma>\<close> symbol is reserved and references the future class instance.
  By relying on the implementation of the Records
  in \<^isabelle>~@{cite "wenzel:isabelle-isar:2020"},
  one can reference an attribute of an instance using its selector function.
  For example, \<^term>\<open>establish \<sigma>\<close> denotes the value
  of the attribute \<^const>\<open>establish\<close>
  of the future instance of the class \<^typ>\<open>myconclusion\<close>.
\<close>

(*<*)
declare_reference*["invariant-checking-figure"::figure]
(*>*)

text\<open>
  The value of each attribute defined for the instances is checked at run-time
  against their class invariants.
  The instance \<^theory_text>\<open>proof1\<close> respects the \<^theory_text>\<open>invariant has_property\<close>,
  because we specify its attribute \<^const>\<open>evidence\<close> to the \<^typ>\<open>kind\<close> \<^const>\<open>proof\<close>,
  we also specify its attribute \<^const>\<open>property\<close> with a suited value
  as a \<^type>\<open>list\<close> of \<^type>\<open>thm\<close>.
  In \<^figure>\<open>invariant-checking-figure\<close>,
  we attempt to specify a new instance \<^theory_text>\<open>intro1\<close> of the class \<^typ>\<open>myintro\<close>.
  However, the invariant checking triggers an error because the
  constraint specified in the \<^theory_text>\<open>invariant force_level\<close> is not respected,
  when we specify the attribute \<^const>\<open>level\<close> of \<^theory_text>\<open>intro1\<close> to \<^term>\<open>Some (0::int)\<close>.
  The \<^theory_text>\<open>invariant force_level\<close> forces the value of the argument
  of the attribute \<^const>\<open>level\<close> to be greater than 1.
\<close>

figure*[
  "invariant-checking-figure"::figure
  , relative_width="99"
  , src="''figures/invariant-checking-violated-example''"
]\<open>The \<^theory_text>\<open>invariant force_level\<close> of the class \<^typ>\<open>myintro\<close> is violated by
  the instance \<^theory_text>\<open>intro1\<close>.\<close>

(*<*)
declare_reference*["inherited-invariant-checking-figure"::figure]
(*>*)

text\<open>
  Classes inherit the invariants from their super-class.
  As the class  \<^typ>\<open>myclaim\<close> is a subclass
  of the class \<^typ>\<open>myintro\<close>, it inherits the \<^typ>\<open>myintro\<close> invariants.
  Hence the \<^theory_text>\<open>invariant force_level\<close> is checked
  when the instance \<^theory_text>\<open>claimNotion\<close> is defined,
  like in \<^figure>\<open>inherited-invariant-checking-figure\<close>.
\<close>

figure*[
  "inherited-invariant-checking-figure"::figure
  , relative_width="99"
  , src="''figures/inherited-invariant-checking-violated-example''"
]\<open>The \<^theory_text>\<open>invariant force_level\<close> of the class \<^typ>\<open>myclaim\<close> is inherited
  from the class \<^typ>\<open>myintro\<close> and is violated by the instance \<^theory_text>\<open>claimNotion\<close>.
\<close>

(*<*)
value*\<open>map (myresult.property) @{myresult-instances}\<close>
value*\<open>map (mytext_section.authored_by) @{myintro-instances}\<close>

value*\<open>filter (\<lambda>\<sigma>. myresult.evidence \<sigma> = proof) @{myresult-instances}\<close>
value*\<open>filter (\<lambda>\<sigma>. the (mytext_section.level \<sigma>) > 1) @{myintro-instances}\<close>
value*\<open>filter (\<lambda>\<sigma>. myresult.evidence \<sigma> = argument) @{myresult-instances}\<close>
(*>*)

text\<open>
  Any class definition generates term antiquotations checking a class instance or
  the set of instances in a particular logical context; these references were
  elaborated to objects they refer to.
  This paves the way for a new mechanism to query the ``current'' instances presented
  as a \<^hol> \<^type>\<open>list\<close>.
  Arbitrarily complex queries can therefore be defined inside the logical language.
  Thus, to get the list of the properties of the instances of the class \<^typ>\<open>myresult\<close>,
  or to get the list of the authors of the instances of the  \<^typ>\<open>myintro\<close> class,
  it suffices to treat this meta-data as usual:
  @{theory_text [display,indent=5, margin=70]
\<open>value*\<open>map (myresult.property) @{myresult-instances}\<close>
value*\<open>map (mytext_section.authored_by) @{myintro-instances}\<close>\<close>}
  In order to get the list of the instances of the class \<^typ>\<open>myresult\<close>
  whose \<^const>\<open>evidence\<close> is a \<^const>\<open>proof\<close>, one can use the command:
  @{theory_text [display,indent=5, margin=70]
\<open>value*\<open>filter (\<lambda>\<sigma>. myresult.evidence \<sigma> = proof) @{myresult-instances}\<close>\<close>}
  Analogously, the list of the instances of the class \<^typ>\<open>myintro\<close> whose \<^const>\<open>level\<close> > 1,
  can be filtered by:
  @{theory_text [display,indent=5, margin=70]
\<open>value*\<open>filter (\<lambda>\<sigma>. the (mytext_section.level \<sigma>) > 1)
       @{myintro-instances}\<close>\<close>}
\<close>

section*["morphisms"::technical,main_author="Some(@{docitem ''idir''}::author)"] \<open>Proving Morphisms on Ontologies\<close>

(*<*)
(* Mapped_PILIB_Ontology example *)
term\<open>fold (+) S 0\<close>  

definition sum 
  where "sum S = (fold (+) S 0)"

datatype Hardware_Type = 
  Motherboard | 
  Expansion_Card | 
  Storage_Device | 
  Fixed_Media | 
  Removable_Media |
  Input_Device |
  Output_Device

(* Reference Ontology *)
onto_class Resource =
  name :: string

onto_class Electronic = Resource +
  provider :: string
  manufacturer :: string

onto_class Component = Electronic +
  mass :: int
  dimensions :: "int list" 

onto_class Informatic = Resource +
  description :: string

onto_class Hardware = Informatic +
  type :: Hardware_Type
  mass :: int
  composed_of :: "Component list" 
  invariant c1 :: "mass \<sigma> = sum(map Component.mass (composed_of \<sigma>))"

(* Local Ontology *)
onto_class Item =
  name :: string

onto_class Product = Item +
  serial_number :: int
  provider :: string
  mass :: int

onto_class Computer_Hardware = Product +
  type :: Hardware_Type
  composed_of :: "Product list" 
  invariant c2 :: "Product.mass \<sigma> = sum(map Product.mass (composed_of \<sigma>))"

definition Item_to_Resource_morphism :: "'a Item_scheme \<Rightarrow> Resource" 
           ("_ \<langle>Resource\<rangle>\<^sub>I\<^sub>t\<^sub>e\<^sub>m" [1000]999)
  where    "\<sigma> \<langle>Resource\<rangle>\<^sub>I\<^sub>t\<^sub>e\<^sub>m =  \<lparr>  Resource.tag_attribute = 0::int , 
                                 Resource.name = name \<sigma> \<rparr>" 
  
definition Product_to_Component_morphism :: "'a Product_scheme \<Rightarrow> Component"
           ("_ \<langle>Component\<rangle>\<^sub>P\<^sub>r\<^sub>o\<^sub>d\<^sub>u\<^sub>c\<^sub>t" [1000]999)
  where "  \<sigma> \<langle>Component\<rangle>\<^sub>P\<^sub>r\<^sub>o\<^sub>d\<^sub>u\<^sub>c\<^sub>t = \<lparr> Resource.tag_attribute = 1::int ,
                                 Resource.name = name \<sigma> ,
                                 Electronic.provider  = Product.provider \<sigma> ,
                                 Electronic.manufacturer  = ''no manufacturer'' ,
                                 Component.mass = Product.mass \<sigma> ,
                                 Component.dimensions = [] \<rparr>" 

definition Computer_Hardware_to_Hardware_morphism :: "'a Computer_Hardware_scheme \<Rightarrow> Hardware"
           ("_ \<langle>Hardware\<rangle>\<^sub>C\<^sub>o\<^sub>m\<^sub>p\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>H\<^sub>a\<^sub>r\<^sub>d\<^sub>w\<^sub>a\<^sub>r\<^sub>e" [1000]999)
           where "\<sigma> \<langle>Hardware\<rangle>\<^sub>C\<^sub>o\<^sub>m\<^sub>p\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>H\<^sub>a\<^sub>r\<^sub>d\<^sub>w\<^sub>a\<^sub>r\<^sub>e =
                  \<lparr>  Resource.tag_attribute = 2::int ,
                     Resource.name = name \<sigma> ,
                     Informatic.description = ''no description'', 
                     Hardware.type = Computer_Hardware.type \<sigma> ,
                     Hardware.mass = mass \<sigma> ,
                     Hardware.composed_of = map Product_to_Component_morphism 
                                                (Computer_Hardware.composed_of \<sigma>)
                   \<rparr>" 

lemma inv_c2_preserved :
  "c2_inv \<sigma> \<Longrightarrow> c1_inv (\<sigma> \<langle>Hardware\<rangle>\<^sub>C\<^sub>o\<^sub>m\<^sub>p\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>H\<^sub>a\<^sub>r\<^sub>d\<^sub>w\<^sub>a\<^sub>r\<^sub>e)"
  unfolding c1_inv_def c2_inv_def 
            Computer_Hardware_to_Hardware_morphism_def Product_to_Component_morphism_def  
  by (auto simp: comp_def)

lemma Computer_Hardware_to_Hardware_morphism_total :
  "Computer_Hardware_to_Hardware_morphism ` ({X::Computer_Hardware. c2_inv X}) \<subseteq> ({X::Hardware. c1_inv X})"
  using inv_c2_preserved 
  by auto

(*>*)

text\<open>
The \<^dof> framework does not assume that all documents refer to the same ontology. 
Each document may even build its local ontology without any external reference. 
It may also be based on several reference ontologies (\<^eg>, from the  \<^dof> library). 

Since ontological instances possess \<^emph>\<open>representations inside the logic\<close>,
the relationship between a local ontology and a reference ontology can be formalised
using a morphism function also inside the logic. 
More precisely, the instances of local ontology classes may be described as the image of a 
transformation applied to one or several other instances of class(es) belonging to another 
ontology. 

Thanks to the morphism relationship, the obtained class may either import meta-data 
(definitions are preserved)  or map meta-data (the properties are different but 
are semantically equivalent) that are defined in the referenced class(es). 
It may also provide additional properties. This means that morphisms may be injective, 
surjective, bijective, and thus describe abstract relations between ontologies.
This raises the question of invariant preservation.
\<close>

text\<open>
\begin{figure}
@{boxed_theory_text [display]
\<open>definition sum where "sum S = (fold (+) S 0)"

datatype Hardware_Type = Motherboard | Expansion_Card | Storage_Device ...

onto_class Resource =
  name :: string
onto_class Electronic = Resource +
  provider :: string
  manufacturer :: string
onto_class Component = Electronic +
  mass :: int
  dimensions :: "int list" 
onto_class Informatic = Resource +
  description :: string
onto_class Hardware = Informatic +
  type :: Hardware_Type
  mass :: int
  composed_of :: "Component list" 
  invariant c1 :: "mass \<sigma> = sum(map Component.mass (composed_of \<sigma>))"\<close>}
\caption{An extract of a reference ontology.}
\label{fig-Reference-Ontology-example}
\end{figure}

To illustrate this process, we use the reference ontology (considered as a standard) described 
in the listing  \autoref{fig-Reference-Ontology-example}, defining the \<^typ>\<open>Resource\<close>,
\<^typ>\<open>Electronic\<close>, \<^typ>\<open>Component\<close>, \<^typ>\<open>Informatic\<close> and \<^typ>\<open>Hardware\<close> concepts (or classes). 
Each class contains a set of attributes or properties and some local invariants. 

In our example, we focus on the \<^typ>\<open>Hardware\<close> class containing a \<^const>\<open>mass\<close> attribute
and composed of a list of components with a \<^const>\<open>mass\<close> attribute formalising
the mass value of each component.
The \<^typ>\<open>Hardware\<close> class also contains a local \<^theory_text>\<open>invariant c1\<close>
to define a constraint linking the global mass of a \<^typ>\<open>Hardware\<close> object
with the masses of its own components.  
\<close>

text\<open>
\begin{figure}
@{boxed_theory_text [display]
\<open>onto_class Item =
  name :: string
onto_class Product = Item +
  serial_number :: int
  provider :: string
  mass :: int
onto_class Computer_Hardware = Product +
  type :: Hardware_Type
  composed_of :: "Product list" 
  invariant c2 :: "Product.mass \<sigma> = sum(map Product.mass (composed_of \<sigma>))"\<close>}
\caption{An extract of a local (user)  ontology.}
\label{fig-Local-Ontology-example}
\end{figure}

For the sake of the argument, we have defined a simple ontology to classify Hardware objects.
This ontology is described in \autoref{fig-Local-Ontology-example} and 
defines the \<^typ>\<open>Item\<close>, \<^typ>\<open>Product\<close> and \<^typ>\<open>Computer_Hardware\<close> concepts.
As for the reference ontology, we focus on the \<^typ>\<open>Computer_Hardware\<close> 
class defined as a list of products characterised by their mass value.
This class contains a local \<^theory_text>\<open>invariant c2\<close> to guarantee that its own mass value
equals the sum of all the masses of the products composing the object.
\<close>


text\<open>
\begin{figure}
@{boxed_theory_text [display]
\<open>

definition Item_to_Resource_morphism :: "'a Item_scheme \<Rightarrow> Resource" 
           ("_ \<langle>Resource\<rangle>\<^sub>I\<^sub>t\<^sub>e\<^sub>m" [1000]999)
  where    "\<sigma> \<langle>Resource\<rangle>\<^sub>I\<^sub>t\<^sub>e\<^sub>m =  \<lparr>  Resource.tag_attribute = 0::int , 
                                 Resource.name = name \<sigma> \<rparr>" 
  
definition Product_to_Component_morphism :: "'a Product_scheme \<Rightarrow> Component"
           ("_ \<langle>Component\<rangle>\<^sub>P\<^sub>r\<^sub>o\<^sub>d\<^sub>u\<^sub>c\<^sub>t" [1000]999)
  where "  \<sigma> \<langle>Component\<rangle>\<^sub>P\<^sub>r\<^sub>o\<^sub>d\<^sub>u\<^sub>c\<^sub>t = \<lparr> Resource.tag_attribute = 1::int ,
                                 Resource.name = name \<sigma> ,
                                 Electronic.provider  = Product.provider \<sigma> ,
                                 Electronic.manufacturer  = '''' ,
                                 Component.mass = Product.mass \<sigma> ,
                                 Component.dimensions = [] \<rparr>" 

definition Computer_Hardware_to_Hardware_morphism ::
             "'a Computer_Hardware_scheme \<Rightarrow> Hardware"
             ("_ \<langle>Hardware\<rangle>\<^sub>C\<^sub>o\<^sub>m\<^sub>p\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>H\<^sub>a\<^sub>r\<^sub>d\<^sub>w\<^sub>a\<^sub>r\<^sub>e" [1000]999)
           where "\<sigma> \<langle>Hardware\<rangle>\<^sub>C\<^sub>o\<^sub>m\<^sub>p\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>H\<^sub>a\<^sub>r\<^sub>d\<^sub>w\<^sub>a\<^sub>r\<^sub>e =
                  \<lparr>  Resource.tag_attribute = 2::int ,
                     Resource.name = name \<sigma> ,
                     Informatic.description = ''no description'', 
                     Hardware.type = Computer_Hardware.type \<sigma> ,
                     Hardware.mass = mass \<sigma> ,
                     Hardware.composed_of =
                                      map Product_to_Component_morphism 
                                          (Computer_Hardware.composed_of \<sigma>) \<rparr>"\<close>}
\caption{An extract of a mapping definition.}

\label{fig-mapping-example}
\end{figure}


To check the coherence of our local ontology, we define a relationship between the local ontology 
and the reference ontology using morphism functions (or mapping rules as in ATL framework~@{cite "atl"}
or EXPRESS-X language~@{cite "BGPP95"}). These rules are applied to define the relationship 
between one class of the local ontology to one or several other class(es) described in the reference 
ontology. 

\<^const>\<open>Product_to_Component_morphism\<close> and \<^const>\<open>Computer_Hardware_to_Hardware_morphism\<close>
definitions, detailed in \autoref{fig-mapping-example},
specify how \<^typ>\<open>Product\<close> or \<^typ>\<open>Computer_Hardware\<close> objects are mapped to \<^typ>\<open>Component\<close> 
or \<^typ>\<open>Hardware\<close> objects defined in the reference ontology.
This mapping shows that the structure of a (user) ontology may be arbitrarily different
from the one of a standard ontology it references. 
\<close>

text\<open>
The advantage of using the \<^dof> framework compared to approaches like ATL or EXPRESS-X is 
the possibility of formally verifying the \<^emph>\<open>mapping rules\<close>. \<^ie>  proving the preservation 
of invariants, as we will demonstrate in the following example.\<close>

text\<open>
\begin{figure}
@{boxed_theory_text [display]
\<open>lemma inv_c2_preserved :
  "c2_inv \<sigma> \<Longrightarrow> c1_inv (\<sigma> \<langle>Hardware\<rangle>\<^sub>C\<^sub>o\<^sub>m\<^sub>p\<^sub>u\<^sub>t\<^sub>e\<^sub>r\<^sub>H\<^sub>a\<^sub>r\<^sub>d\<^sub>w\<^sub>a\<^sub>r\<^sub>e)"
  unfolding c1_inv_def c2_inv_def 
            Computer_Hardware_to_Hardware_morphism_def 
            Product_to_Component_morphism_def  
  using comp_def by (auto)

lemma Computer_Hardware_to_Hardware_morphism_total :
 "Computer_Hardware_to_Hardware_morphism ` ({X::Computer_Hardware. c2_inv X}) 
    \<subseteq> ({X::Hardware. c1_inv X})"
  using inv_c2_preserved by auto\<close>}
\caption{Proofs establishing the Invariant Preservation.}
\label{fig-xxx}
\end{figure}
\<close>
text\<open>The example proof in \autoref{fig-xxx} for a simple, but typical example of reformatting
meta-data into another format along an ontological mapping are nearly trivial: after unfolding
the invariant and the morphism definitions, the preservation proof is automatic.  
\<close>

(*
section*[ontoexample::text_section,main_author="Some(@{docitem ''idir''}::author)"] 
\<open>Mathematics Example : An Extract from OntoMath\textsuperscript{PRO}\<close>

(*<*)
(* OntoMathPro_Ontology example *)

datatype dc = creator string | title string

datatype owl =
    backwardCompatibleWith string
  | deprecated string
  | incompatibleWith string
  | priorVersion string
  | versionInfo string
  
datatype rdfs =
    comment string
  | isDefinedBy string
  | label string
  | seeAlso string

datatype annotation = DC dc | OWL owl |  RDFS rdfs

onto_class Top =
  Annotations :: "annotation list"

onto_class Field_of_mathematics =
  Annotations :: "annotation list" <= "[RDFS (label ''Field of mathematics'')]"
  invariant restrict_annotation_F ::"set (Annotations \<sigma>) \<subseteq>
                                              range (RDFS o label) \<union> range (RDFS o comment)"

onto_class Mathematical_knowledge_object =
  Annotations :: "annotation list"
  invariant restrict_annotation_M ::"set (Annotations \<sigma>) \<subseteq>
                                              range (RDFS o label) \<union> range (RDFS o comment)"

onto_class assoc_F_M =
  contains:: "(Field_of_mathematics \<times> Mathematical_knowledge_object) set"
  invariant contains_defined :: "\<forall> x. x \<in> Domain (contains \<sigma>)
                                              \<longrightarrow> (\<exists> y \<in> Range (contains \<sigma>). (x, y) \<in> contains \<sigma>)"

onto_class assoc_M_F =
  belongs_to :: "(Mathematical_knowledge_object \<times> Field_of_mathematics) set"
  invariant belong_to_defined :: "\<forall> x. x \<in> Domain (belongs_to \<sigma>)
                                           \<longrightarrow> (\<exists> y \<in> Range (belongs_to \<sigma>). (x, y) \<in> belongs_to \<sigma>)"

onto_class assoc_M_M =
  is_defined_by :: "(Mathematical_knowledge_object \<times> Mathematical_knowledge_object) set"
  invariant is_defined_by_defined :: "\<forall> x. x \<in> Domain (is_defined_by \<sigma>)
                                    \<longrightarrow> (\<exists> y \<in> Range (is_defined_by \<sigma>). (x, y) \<in> is_defined_by \<sigma>)"
(*typedef 'a A'_scheme =
  "{x :: 'a A_scheme. "
*)

onto_class assoc_M_M' =
  "defines" :: "(Mathematical_knowledge_object \<times> Mathematical_knowledge_object) set"
  invariant defines_defined :: "\<forall> x. x \<in> Domain (defines \<sigma>)
                                    \<longrightarrow> (\<exists> y \<in> Range (defines \<sigma>). (x, y) \<in> defines \<sigma>)"

onto_class assoc_M_M_see_also =
  see_also :: "(Mathematical_knowledge_object rel) set" 
  invariant see_also_trans :: "\<forall> r \<in> (see_also \<sigma>). trans r"
  invariant see_also_sym :: "\<forall> r \<in> (see_also \<sigma>). sym r"

onto_class Problem = Mathematical_knowledge_object +
  Annotations :: "annotation list"
  
onto_class Method = Mathematical_knowledge_object +
  Annotations :: "annotation list"

onto_class assoc_Problem_Method =
  is_solved_by :: "(Problem \<times> Method) set"
  invariant is_solved_by_defined :: "\<forall> x. x \<in> Domain (is_solved_by \<sigma>)
                                    \<longrightarrow> (\<exists> y \<in> Range (is_solved_by \<sigma>). (x, y) \<in> is_solved_by \<sigma>)"

onto_class assoc_Method_Problem =
  solves :: "(Method \<times> Problem) set"
  invariant solves_defined :: "\<forall> x. x \<in> Domain (solves \<sigma>)
                                    \<longrightarrow> (\<exists> y \<in> Range (solves \<sigma>). (x, y) \<in> solves \<sigma>)"

(*>*)

text\<open>
  The \<^emph>\<open>OntoMath\textsuperscript{PRO}\<close> ontology~@{cite "Nevzorova2014OntoMathPO"}
  is an OWL ontology of mathematical knowledge concepts.
  It possesses the \<^emph>\<open>is-a\<close> semantics for hierarchies of mathematical knowledge elements,
  and defines these elements as two hierarchies of classes:
  a taxonomy of the fields of mathematics and a taxonomy of mathematical knowledge objects.
  It defines two main type of relations for these two taxonomies:
  directed relations between elements of the two hierarchies
  like \<^const>\<open>belongs_to\<close>, \<^const>\<open>contains\<close>, \<^const>\<open>defines\<close>, \<^const>\<open>is_defined_by\<close>, \<^const>\<open>solves\<close>,
  \<^const>\<open>is_solved_by\<close>, and a symmetric transitive associative relation \<^const>\<open>see_also\<close>
  between two mathematical knowledge objects.
  It also represents links with external resources
  such as DBpedia~@{cite "10.1007/978-3-540-76298-0_52"}
  with annotations properties~@{cite "Parsia:12:OWO"}.
  \<^dof> covers a wide range of the OWL concepts used by the OntoMath\textsuperscript{PRO} ontology.
  We can represent the annotations properties as datatypes and
  then attach them as an attributes list to a class.
  For example the declaration:
@{theory_text [display,indent=5, margin=70] \<open>
datatype dc = creator string | title string
datatype owl =   backwardCompatibleWith string
               | deprecated string
               | incompatibleWith string
               | priorVersion string
               | versionInfo string
datatype rdfs =   comment string
                | isDefinedBy string
                | label string
                | seeAlso string
datatype annotation = DC dc | OWL owl |  RDFS rdfs

onto_class Field_of_mathematics =
  Annotations :: "annotation list" <= "[RDFS (label ''Field of mathematics'')]"
  invariant restrict_annotation_F ::"set (Annotations \<sigma>) \<subseteq>
                                       range (RDFS o label)
                                       \<union> range (RDFS o comment)"
\<close>}
  defines the class \<^typ>\<open>Field_of_mathematics\<close> with an attribute \<^theory_text>\<open>Annotations\<close>
  which is a \<^type>\<open>list\<close> of \<^typ>\<open>annotation\<close>s.
  We can even constrain the type of allowed \<^typ>\<open>annotation\<close>s with an invariant.
  Here the \<^theory_text>\<open>invariant restrict_annotation_F\<close> forces the \<^typ>\<open>annotation\<close>s to be
  a \<^const>\<open>label\<close> or a \<^const>\<open>comment\<close>.
  Subsumption relation is straightforward.
  The OntoMath\textsuperscript{PRO} ontology defines
  a \<^typ>\<open>Problem\<close> and a \<^typ>\<open>Method\<close>
  as subclasses of the class \<^typ>\<open>Mathematical_knowledge_object\<close>.
  It gives in \<^dof>:
@{theory_text [display,indent=5, margin=70] \<open>
onto_class Problem = Mathematical_knowledge_object +
  Annotations :: "annotation list"
  
onto_class Method = Mathematical_knowledge_object +
  Annotations :: "annotation list"
\<close>}
  We can express the relations between the two taxonomies
  with association \<^theory_text>\<open>onto_class\<close>es which specify
  the relation as an attribute and enforces the relation with an \<^theory_text>\<open>invariant\<close>.
  The two directed relations \<^const>\<open>is_solved_by\<close> and \<^const>\<open>solves\<close>
  between \<^typ>\<open>Problem\<close> and a \<^typ>\<open>Method\<close> can be represented in \<^dof> like this:
@{theory_text [display,indent=5, margin=70] \<open>
onto_class assoc_Problem_Method =
  is_solved_by :: "(Problem \<times> Method) set"
  invariant is_solved_by_defined :: "\<forall> x. x \<in> Domain (is_solved_by \<sigma>)
              \<longrightarrow> (\<exists> y \<in> Range (is_solved_by \<sigma>). (x, y) \<in> is_solved_by \<sigma>)"

onto_class assoc_Method_Problem =
  solves :: "(Method \<times> Problem) set"
  invariant solves_defined :: "\<forall> x. x \<in> Domain (solves \<sigma>)
              \<longrightarrow> (\<exists> y \<in> Range (solves \<sigma>). (x, y) \<in> solves \<sigma>)"
\<close>}
  where the attributes \<^const>\<open>is_solved_by\<close> and \<^const>\<open>solves\<close> define the relations
  of the classes and the invariants \<^theory_text>\<open>is_solved_by_defined\<close> and \<^theory_text>\<open>solves_defined\<close> enforce
  the existence of the relations when one define instances of the classes.

  \<^dof> allows to define ontologies and specify constraints
  on their concepts.
  Additionally it dynamically checks at run-time the concepts when defining instances.
  It offers an environment to define and test ontologies in an integrated document,
  where all the knowledge and the proof-checking can be specified,
  and thus can help to find the right trade-off between plain vocabularies and 
  highly formalized models.
\<close>
*)

section*[concl::conclusion]\<open>Conclusion\<close>
text\<open>We presented \<^dof>, an ontology framework 
deeply integrating continuous-check\slash continuous-build functionality into
the formal development process in \<^hol>. The novel feature of term-contexts in \<^dof>,
which permits term-antiquotations elaborated in the parsing process, paves the
way for the abstract specification of meta-data constraints as well the possibility
of advanced search in the meta-data of document elements. Thus it profits and
extends  Isabelle's document-centric view on formal development.

Many ontological languages such as OWL as well as the meta-modeling technology 
available for UML/OCL provide concepts for semantic rules and constraints, but
leave the validation checking usually to external tools (if implementing them at all).
This limits their practical usefulness drastically. Our approach treats invariants as 
first-class citizens, and turns them into an object of formal study in, for example, 
ontological mappings. Such a technology exists, to our knowledge, for the first time.

Our experiments with adaptations of existing ontologies from engineering and mathematics
show that \<^dof>'s ODL has sufficient expressive power to cover all aspects
of languages such as OWL (with perhaps the exception of multiple inheritance on classes).
However, these ontologies have been developed specifically \<^emph>\<open>in\<close> OWL and target
its specific support, the Protégé editor @{cite "protege"}. We argue that \<^dof> might ask 
for a re-engineering of these ontologies: less deep hierarchies, rather deeper structure 
in meta-data and stronger invariants.
\<close>


subsection*[rw::related_work]\<open>Related Work\<close>

text\<open>There are a number of approaches to use ontologies for structuring the link between
information and knowledge, and to make it amenable to 
 ``semantic'' search in or consistency checking of documents:

\<^item> The search engine \<^url>\<open>http://shinh.org/wfs\<close> uses a quite brute-force, 
  but practical approach. It is getting its raw-data from Wikipedia and PlanetMath 
  and similar sites, and uses clever text-based search methods in 
  a large number of formulas, agnostic of their logical context, and of formal proof.

\<^item> The OAF project @{cite "KohlhaseR21"} comes closest to our ideal of wide-spread
  use of ontologies for search in mathematical libraries.
  The project developed a common ontological format, called  OMDoc/MMT, and 
  developed six \<^emph>\<open>export\<close> functions from major ITP systems into it. The more difficult task to 
  develop \<^emph>\<open>import\<close> functions has not been addressed, not to mention the construction
  of imported proofs in a native tactic proof format. Rather, the emphasis was put on building
  a server infrastructure based on conventional, rather heavy-weight database and OWL technology.
  Our approach targets so far only one ITP system and its libraries, and emphasizes 
  type-safeness, expressive power and ``depth'' of meta-data, which is adapted
  to the specific needs of ITP systems and theory developments.

\<^item> There are meanwhile a number of proposals of ontologies targeting mathematics: 
  \<^item>  OntoMath\textsuperscript{PRO} @{cite "Nevzorova2014OntoMathPO"} proposes a 
     ``taxonomy of the fields of mathematics'' (pp 110). In total, 
     OntoMath\textsuperscript{PRO} contains the daunting number of 3,449 classes, which is in part due to 
     the need to compensate the lack of general datatype definition methods for meta-data.
     It is inspired from a translation of the Russian Federal Standard for Higher Education 
     on mathematics for master students,
     which makes it nevertheless an interesting starting point for a future development
     of a mathematics ontology in the \<^dof> framework.
  \<^item> Other ontologies worth mentioning are DBpedia @{cite "10.1007/978-3-540-76298-0_52"}, 
    which provides with the \<^emph>\<open>SPARQL endpoint\<close>  \<^url>\<open>http://dbpedia.org/sparql\<close> a search engine, 
    and the more general ScienceWISE \<^footnote>\<open>\<^url>\<open>http://sciencewise.info/ontology/\<close>.\<close>
    that allows users to introduce their own category concepts. 
    Both suffer from the lack of deeper meta-data modeling, and the latter is still at the beginning 
    (ScienceWISE marks the Mathematics part as ``under construction'').

%   \<^url>\<open>https://github.com/CLLKazan/OntoMathPro\<close> 
%
% ITEM The "Ontology for Engineering Mathematics" 
%  \<^url>\<open>https://tomgruber.org/writing/an-ontology-for-engineering-mathematics\<close> is
%  is  unfortunately only a half-baked approach to model physical quantities
%  and SI-measurements. Instead of using ontologies for this purpose, there
%  exist approaches based on strong type systems 
\<close>

subsection*[fw::related_work]\<open>Future Work\<close>
text\<open> We plan to complement \<^dof> with incremental LaTeX generation and a previewing facility
that will further increase the usability of our framework for the ontology-conform editing
of formal content, be it in the engineering or the mathematics domain
(this paper has been edited in \<^dof>, of course).

Another line of future application is to increase the ``depth'' of built-in term antiquotations such
as \<^theory_text>\<open>@{typ \<open>'\<tau>\<close>}\<close>, \<^theory_text>\<open>@{term \<open>a + b\<close>}\<close> and \<^theory_text>\<open>@{thm \<open>HOL.refl\<close>}\<close>, which are currently implemented 
just as validations in the current logical context. In the future, they could  optionally be expanded 
to the types, terms and theorems (with proof objects attached) in a meta-model of the Isabelle Kernel 
such as the one presented in @{cite "10.1007/978-3-030-79876-5_6"} (also available in the AFP). 
This will allow for definitions of query-functions in, \<^eg>, proof-objects, and pave the way 
to annotate them with typed meta-data. Such a technology could be relevant for the interoperability 
of proofs across different ITP platforms.
\<close>

(*<*)
close_monitor*[this]

end
(*>*) 
