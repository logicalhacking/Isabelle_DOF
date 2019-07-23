(*<*)
theory "04_RefMan"
  imports "03_GuidedTour" (* apparently inaccessible; for railroads "Isar_Ref.Base" *)

begin
(*>*)

chapter*[isadof::technical,main_author="Some(@{docitem ''bu''}::author)"]
\<open> \isadof : Syntax and Semantics\<close>
   
text\<open> \isadof is embedded in the underlying generic
document model of Isabelle as described in @{docitem "sec:background"}.  
Recall that the document language can be extended dynamically, \ie, new
\<open>user-defined\<close> can be introduced at run-time.  This is similar to
the definition of new functions in an interpreter. \isadof as a system plugin is
is a number of new command definitions in Isabelle's document model.

\isadof consists consists basically of three components:
\<^item> an own \<^emph>\<open>family of text-element\<close> such as @{command "title*"}, @{command "chapter*"}  
  @{command "text*"}, etc., which can be annotated with meta-information defined in the 
  underlying  ontology definition and allow to build a \<^emph>\<open>core\<close> document,
\<^item> the \<^emph>\<open>ontology definition\<close> which is an Isabelle theory file with definitions
  for document-classes and all auxiliary datatypes 
  (we call this the Ontology Definition Language (ODL))  
\<^item> the \<^emph>\<open>layout definition\<close> for the given ontology exploiting this meta-information.
\<close>

text\<open> Note that the document core \<^emph>\<open>may\<close>, but \<^emph>\<open>must\<close> not
use Isabelle definitions or proofs for checking the formal content---the 
present paper is actually an example of a document not containing any proof.
Consequently, the document editing and checking facility provided by 
\isadof addresses the needs of common users for an advanced text-editing environment,
neither modeling nor proof knowledge is inherently required.

We expect authors of ontologies to have experience in the use of \isadof, basic
modeling (and evtl. SML programming) experience and, last but not least, domain knowledge
of the ontology to be modeled. Users with experience in UML-like meta-modeling 
will feel familiar with most concepts; however, we expect  no need for insight 
in the Isabelle proof language, for example, or other more advanced concepts.

The document generation process of \isadof is currently restricted to \LaTeX, which means
that the layout is defined by a set of \LaTeX{} style files. Several layout 
definitions for one ontology are possible which paves the way for different \<^emph>\<open>views\<close> on
the same integrated document, addressing the needs of different purposes 
and/or target readers. Conceiving new style files will definitively require knowledge
over \LaTeX{} and some knowledge over the Isabelle document generation process.

The situation is roughly similar to \LaTeX{}-users, who usually have minimal knowledge about 
the content in  style-files (\<^verbatim>\<open>.sty\<close>-files). In the document core authors \<^emph>\<open>can\<close>  use \LaTeX{}  
commands in  their source, but this limits the possibility of using different representation 
technologies, \eg, HTML, and increases the risk of arcane error-messages in the generated \LaTeX{}.
Using low-level \LaTeX{} commands is at the users risk. A correctly checked \isadof document
should typeset, provided that a few basic pitfalls are avoided: no dangling \<^verbatim>\<open>{\<close> or \<^verbatim>\<open>}\<close>, no 
spontaneous unprotected \<^verbatim>\<open>_\<close>, etc. It is also helpful to execute the final
@{command "check_doc_global"} command to check the global reference stucture.
\<close>



section\<open>Ontology Modeling in ODL\<close>


text\<open>As already mentioned, ODL has some similarities to meta-modeling languages
such as UML class models: It builds upon concepts like class, inheritance, class-instances, 
attributes, references to instances, and class-invariants. Some more advanced concepts like 
advanced type-checking, referencing to formal entities of Isabelle, and monitors are due
to its specific application in the Isabelle context.  

Conceptually, ontologies specified in ODL consist of:

\<^item> \<^emph>\<open>document classes\<close> (syntactically marked by the
  \inlineisar{doc_class} keyword) that describe concepts;
\<^item> an optional document base class expressing single inheritance
  class extensions;
\<^item> \<^emph>\<open>attributes\<close> specific to document classes, where
  
  \<^item> attributes are HOL-typed;
  \<^item> attributes of instances of document elements are mutable;
  \<^item> attributes can refer to other document classes, thus, document
    classes must also be HOL-types (such attributes are called
    \<^emph>\<open>links\<close>);
  \<^item> attribute values were denoted by HOL-terms;
\<^item> a special link, the reference to a super-class, establishes an
  \<^emph>\<open>is-a\<close> relation between classes;
\<^item> classes may refer to other classes via a regular expression in a
  \<^emph>\<open>where\<close> clause (classes with a where clauses are
  called \<^emph>\<open>monitor classes\<close>);
\<^item> attributes may have default values in order to facilitate notation.

\<close>

text\<open>
 The \isadof ontology specification language consists basically on a notation for
document classes, where the attributes were typed with HOL-types and can be instantiated 
by terms HOL-terms, \ie, the actual parsers and type-checkers of the Isabelle system were reused.
This has the particular advantage that \isadof commands can be arbitrarily mixed with 
Isabelle/HOL commands providing the machinery for type declarations and term specifications such
as enumerations. In particular, document class definitions provide:
\<^item>  a HOL-type for each document class as well as inheritance, 
\<^item>  support for attributes with HOL-types and optional default values,
\<^item>  support for overriding of attribute defaults but not overloading, and
\<^item>  text-elements annotated with document classes; they are mutable 
   instances of document classes.
\<close>

text\<open>
Attributes referring to other ontological concepts are called \<^emph>\<open>links\<close>.
The HOL-types inside the document specification language support built-in types for Isabelle/HOL 
\inlineisar+typ+'s,  \inlineisar+term+'s, and \inlineisar+thm+'s reflecting internal Isabelle's 
internal types  for these entities; when denoted in HOL-terms to instantiate an attribute, for 
example, there is a  specific syntax (called \<^emph>\<open>inner syntax antiquotations\<close>) that is checked by 
\isadof for consistency.

Document classes can have a \inlineisar+where+ clause containing a regular 
expression over class names. Classes with such a \inlineisar+where+ were called \<^emph>\<open>monitor classes\<close>.
While document classes and their inheritance relation structure meta-data of text-elements
in an object-oriented manner, monitor classes enforce structural organization
of documents via the language specified by the regular expression 
enforcing a sequence of text-elements that must belong to the corresponding classes. 
\<close>

text\<open>
A major design decision of ODL is to denote attribute values by HOL-terms and
HOL-types. Consequently, ODL can refer to any predefined
type defined in the HOL library, \eg, \inlineisar+string+ or
\inlineisar+int+ as well as parameterized types, \eg, %
\inlineisar+_ option+, \inlineisar+_ list+, \inlineisar+_ set+, or
products \inlineisar+_ \<times> _+. As a consequence of the document
model, ODL definitions may be arbitrarily intertwined with standard
HOL type definitions. Finally, document class definitions result in
themselves in a HOL-types in order to allow \<^emph>\<open>links\<close> to and
between ontological concepts.
\<close>



section*["odl-manual"::technical]\<open>The ODL Manual\<close>
subsection*["odl-manual0"::technical]\<open>Some Isabelle/HOL Specification Constructs Revisited\<close>
text\<open>The \isadof ontology definition language (ODL) is an extension of Isabelle/HOL;
document class definitions can therefore be arbitrarily mixed with standard HOL
specification constructs. In order to spare the user of ODL a lenghty analysis of
@{cite "isaisarrefman19" and "datarefman19" and "functions19"}, we  present 
syntax and semantics of the specification constructs that are most likely relevant for
the developer of ontologies. Note that our presentation is actually a simplification
of the original sources following the needs of our target audience here; for a full-
blown account, the reader is referred to the original descriptions.\<close>

text\<open>
\<^item> \<open>name\<close> : 
     with the syntactic category of \<open>name\<close>'s we refer to alpha-numerical identifiers 
     (called \<open>short_id\<close>'s in @{cite "isaisarrefman19"}) and identifiers
     in \inlineisar+" ... "+ which might additionally contain certian ``quasi-letters'' such 
     as \inlineisar+_+, \inlineisar+-+, \inlineisar+.+, etc. Details in @{cite "isaisarrefman19"}.
\<^item> \<open>tyargs\<close> : 
     \<^rail>\<open>  typefree | ('(' (typefree * ',') ')')\<close>
     \<open>typefree\<close> denotes fixed type variable(\<open>'a\<close>, \<open>'b\<close>, ...) (c.f. @{cite "isaisarrefman19"})
\<^item> \<open>dt_name\<close> :
     \<^rail>\<open>  (tyargs?) name (mixfix?)\<close>   
     The syntactic entity \<open>name\<close> denotes an identifier, \<open>mixfix\<close> denotes the usual 
     parenthesized mixfix notation (see @{cite "isaisarrefman19"}).
     The \<open>name\<close>'s referred here are type names such as \<^verbatim>\<open>int\<close>, \<^verbatim>\<open>string\<close>, \<^verbatim>\<open>list\<close>, \<^verbatim>\<open>set\<close>, etc. 
\<^item> \<open>type_spec\<close> :
     \<^rail>\<open>  (tyargs?) name\<close>
     The \<open>name\<close>'s referred here are type names such as \<^verbatim>\<open>int\<close>, \<^verbatim>\<open>string\<close>, \<^verbatim>\<open>list\<close>, \<^verbatim>\<open>set\<close>, etc. 
\<^item> \<open>type\<close> :
     \<^rail>\<open>  (( '(' ( type * ',')  ')' )? name) | typefree \<close>     
\<^item> \<open>dt_ctor\<close> :
     \<^rail>\<open> name (type*) (mixfix?)\<close>
\<^item> \<open>datatype_specification\<close> :
     \<^rail>\<open> @@{command "datatype"} dt_name '=' (dt_ctor * '|' )\<close>
\<^item> \<open>type_synonym_specification\<close> :
     \<^rail>\<open> @@{command "type_synonym"} type_spec '=' type\<close>
\<^item> \<open>constant_definition\<close> :
     \<^rail>\<open> @@{command "definition"} name '::' type 'where' '"' name '=' expr '"'\<close>
\<^item> \<open>expr\<close> :

     the syntactic category \<open>expr\<close> here denotes the very rich ``inner-syntax'' language of 
     mathematical  notations for $\lambda$-terms in Isabelle/HOL. Example expressions are:
     \inlineisar|1+2| (arithmetics), \inlineisar|[1,2,3]| (lists), \inlineisar|''ab c''| (strings), 
     \inlineisar|{1,2,3}| (sets), \inlineisar|(1,2,3)| (tuples), 
     \inlineisar|\<forall> x. P(x) \<and> Q x = C| (formulas), etc. 
     For a comprehensive overview, consult the summary ``What's in Main'' 
     @{cite "nipkowMain19"}.
\<close>

text\<open>Other specification constructs, which are potentially relevant for an (advanced) ontology
developer, might be recursive function definitions with pattern-matching @{cite "functions19"}, 
extensible record specifications, @{cite "isaisarrefman19"} and abstract type declarations.\<close>


subsection*["odl-manual1"::technical]\<open>The Command Syntax for Document Class Specifications\<close>
text\<open>
\<^item> \<open>class_id\<close> : \<open>class_id\<close>'s are type-\<open>name\<close>'s that have been introduced via
  a \<open>doc_class_specification\<close>.
\<^item> \<open>doc_class_specification\<close> : 
     \<^rail>\<open> @@{command "doc_class"} class_id '=' (class_id '+')? (attribute_decl+) \<newline>
           (accepts_clause rejects_clause?)?\<close>
     document classes whose specification contains an \<open>accepts_clause\<close> are called 
     \<^emph>\<open>monitor classes\<close> or \<^emph>\<open>monitors\<close> for short. 
\<^item> \<open>attribute_decl\<close> :
     \<^rail>\<open> name '::' '"' type '"' default_clause? \<close>
\<^item> \<open>accepts_clause\<close> :
     \<^rail>\<open> 'accepts' '"' regexpr '"'\<close>
\<^item> \<open>rejects_clause\<close> :
     \<^rail>\<open> 'rejects' (class_id * ',') \<close>
\<^item> \<open>default_clause\<close> :
     \<^rail>\<open> '<=' '"' expr '"' \<close>
\<^item> \<open>regexpr\<close> :
     \<^rail>\<open> '\<lfloor>' class_id '\<rfloor>' | '(' regexpr ')' | (regexpr '||' regexpr) | (regexpr '~~' regexpr)
            | ('\<lbrace>' regexpr '\<rbrace>') | ( '\<lbrace>' regexpr '\<rbrace>\<^sup>*')  \<close>
     regular expressions describe sequences of \<open>class_id\<close>s (and indirect sequences of document
     items corresponding to the \<open>class_id\<close>s). The constructors for alternative, sequence, 
     repetitions and non-empty sequence follow in the top-down order of the above diagram. 
\<close> 


subsection*["odl-design"::example]\<open>An Ontology Example\<close>

text\<open>We illustrate the design of \dof by modeling a small ontology
  that can be used for writing formal specifications that, \eg, could
  build the basis for an ontology for certification documents used in
  processes such as Common Criteria~@{cite "cc:cc-part3:2006"} or CENELEC
  50128~@{cite "bsi:50128:2014"}.@{footnote \<open>The \isadof distribution
    contains an ontology for writing documents for a certification
    according to CENELEC 50128.\<close>} Moreover, in examples of certification
  documents, we refer to a controller of a steam boiler that is
  inspired by the famous steam boiler formalization
  challenge~@{cite "abrial:steam-boiler:1996"}.\<close>

text\<open>
\begin{isar}[float,mathescape,label={lst:doc},caption={An example ontology modeling
simple certification documents, including scientific papers such
as~@{cite "brucker.ea:isabelle-ontologies:2018"}; also recall
\autoref{fig:dof-ide}.}]
doc_class title  = short_title :: "string option" <= "None"
doc_class author = email      :: "string" <= "''''"

datatype classification = SIL0 | SIL1 | SIL2 | SIL3 | SIL4
    
doc_class abstract =
    keywordlist :: "string list"      <= []
    safety_level :: "classification"  <= "SIL3" 
doc_class text_section = 
    authored_by :: "author set"       <= "{}"
    level       :: "int  option"      <= "None"   

type_synonym notion = string

doc_class introduction = text_section +
    authored_by :: "author set"       <= "UNIV"
    uses :: "notion set"
doc_class claim = introduction +
    based_on :: "notion list"
doc_class technical = text_section +
    formal_results  :: "thm list"
doc_class "d$$efinition" = technical +
    is_formal :: "bool"
    property  :: "term list"          <= "[]"

datatype kind = expert_opinion | argument | proof

doc_class result = technical +
    evidence  :: kind 
    property  :: "thm list"           <= "[]"
doc_class example = technical +
    referring_to :: "(notion + d$$efinition) set" <=  "{}"
doc_class "conclusion" = text_section +
    establish   :: "(claim \<times> result) set"
\end{isar}%$

\<close>
text\<open>
  \autoref{lst:doc} shows an example ontology for mathematical papers
  (an extended version of this ontology was used for writing
  @{cite "brucker.ea:isabelle-ontologies:2018"}, also recall
  \autoref{fig:dof-ide}). The commands \inlineisar+datatype+ (modeling
  fixed enumerations) and \inlineisar+type_synonym+ (defining type
  synonyms) are standard mechanisms in HOL systems.  Since ODL is an
  add-on, we have to quote sometimes constant symbols (\eg,
  \inlineisar+"proof"+) to avoid confusion with predefined keywords. ODL
  admits overriding (such as \inlineisar+authored_by+ in the document
  class \inlineisar+introduction+), where it is set to another library
  constant, but no overloading. All \inlineisar+text_section+ elements
  have an optional \inlineisar+level+ attribute, which will be used in
  the output generation for the decision if the context is a section
  header and its level (\eg, chapter, section, subsection). While
  \<open>within\<close> an inheritance hierarchy overloading is prohibited,
  attributes may be re-declared freely in independent parts (as is the
  case for \inlineisar+property+).\<close>

subsection*["sec:advanced"::technical]\<open>Advanced ODL Concepts\<close>
subsubsection\<open>Meta-types as Types\<close>

text\<open>To express the dependencies between text elements to the formal
  entities, \eg, \inlinesml+term+ ($\lambda$-term), \inlinesml+typ+, or
  \inlinesml+thm+, we represent the types of the implementation language
  \<^emph>\<open>inside\<close> the HOL type system.  We do, however, not reflect the data of
  these types. They are just declared abstract types, 
  ``inhabited'' by special constant symbols carrying strings, for
  example of the format \inlineisar+<AT>{thm <string>}+. When HOL
  expressions were used to denote values of \inlineisar+doc_class+
  instance attributes, this requires additional checks after
  conventional type-checking that this string represents actually a
  defined entity in the context of the system state
  \inlineisar+\<theta>+.  For example, the \inlineisar+establish+
  attribute in the previous section is the power of the ODL: here, we model
  a relation between \<^emph>\<open>claims\<close> and \<^emph>\<open>results\<close> which may be a
  formal, machine-check theorem of type \inlinesml+thm+ denoted by, for
  example: \inlineisar+property = "[<AT>{thm ''system_is_safe''}]"+ in a
  system context \inlineisar+\<theta>+ where this theorem is
  established. Similarly, attribute values like 
  \inlineisar+property = "<AT>{term \<Open>A \<leftrightarrow> B\<Close>}"+
  require that the HOL-string \inlineisar+A \<leftrightarrow> B+ is 
  again type-checked and represents indeed a formula in $\theta$. Another instance of 
  this process, which we call \<open>second-level type-checking\<close>, are term-constants
  generated from the ontology such as 
  \inlineisar+<AT>{definition <string>}+. For the latter, the argument string
  must be checked that it  represents a reference to a text-element
  having the type \inlineisar+definition+ according to the ontology in @{example "odl-design"}.\<close>


subsubsection*["sec:monitors"::technical]\<open>ODL Monitors\<close>
text\<open>We call a document class with an accept-clause a
  \<^emph>\<open>monitor\<close>.  Syntactically, an accept-clause contains a regular
  expression over class identifiers. We can extend our
  \inlineisar+tiny_cert+ ontology with the following example:
  \begin{isar}
  doc_class article = 
      style_id :: string   <= "''CENELEC50128''"
      accepts "(title ~~ \<lbrace>author\<rbrace>\<bsup>+\<esup> ~~ abstract ~~ \<lbrace>introduction\<rbrace>\<bsup>+\<esup>  ~~
               \<lbrace>technical || example\<rbrace>\<bsup>+\<esup> ~~ \<lbrace>conclusion\<rbrace>\<bsup>+\<esup>)"
  \end{isar}
  Semantically, monitors introduce a behavioral element into ODL: 
  \begin{isar}
  open_monitor*[this::article]  (* begin of scope of monitor "this" *)
    ...
  close_monitor*[this]          (* end of scope of monitor "this"   *)
  \end{isar}
  Inside the scope of a monitor, all instances of classes mentioned in its accept-clause (the
  \<^emph>\<open>accept-set\<close>) have to appear in the order specified by the
  regular expression; instances not covered by an accept-set may freely
  occur. Monitors may additionally contain a reject-clause with a list
  of class-ids (the reject-list). This allows specifying ranges of
  admissible instances along the class hierarchy:
  \begin{compactitem}
  \item a superclass in the reject-list and a subclass in the
    accept-expression forbids instances superior to the subclass, and
  \item a subclass $S$ in the reject-list and a superclass $T$ in the
    accept-list allows instances of superclasses of $T$ to occur freely,
    instances of $T$ to occur in the specified order and forbids
    instances of $S$.
  \end{compactitem}
  Monitored document sections can be nested and overlap; thus, it is
  possible to combine the effect of different monitors. For example, it
  would be possible to refine the \inlineisar+example+ section by its own
  monitor and enforce a particular structure in the presentation of
  examples.
  
  Monitors manage an implicit attribute \inlineisar+trace+ containing
  the list of ``observed'' text element instances belonging to the
  accept-set. Together with the concept of ODL class invariants, it is
  possible to specify properties of a sequence of instances occurring in
  the document section. For example, it is possible to express that in
  the sub-list of \inlineisar+introduction+-elements, the first has an
  \inlineisar+introduction+ element with a \inlineisar+level+ strictly
  smaller than the others. Thus, an introduction is forced to have a
  header delimiting the borders of its representation. Class invariants
  on monitors allow for specifying structural properties on document
  sections.\<close>


subsubsection*["sec:class_inv"::technical]\<open>ODL Class Invariants\<close>
text\<open>
Ontological classes as described so far are too liberal in many
situations. For example, one would like to express that any instance
of a \inlineisar+result+ class finally has a non-empty property list,
if its \inlineisar+kind+ is \inlineisar+proof+, or that the
\inlineisar+establish+ relation between \inlineisar+claim+ and
\inlineisar+result+ is surjective.

In a high-level syntax, this type of constraints could be expressed, \eg, by:
\begin{isar}
(* 1 *) \<forall> x \<in> result. x@kind = proof \<leftrightarrow> x@kind \<noteq> []
(* 2 *) \<forall> x \<in> conclusion. \<forall> y \<in> Domain(x@establish)
                  \<rightarrow> \<exists> y \<in> Range(x@establish). (y,z) \<in> x@establish
(* 3 *) \<forall> x \<in> introduction. finite(x@authored_by)
\end{isar}
%% @{cartouche [display=true] \<open>  
%%(* 1 *)     \<forall> x \<in> result. x@kind = proof \<leftrightarrow> x@kind \<noteq> [] 
%%(* 2 *)     \<forall> x \<in> conclusion. \<forall> y \<in> Domain(x@establish) 
%%                        \<rightarrow> \<exists> y\<in> Range(x@establish). (y,z) \<in> x@establish  
%%(* 3 *)     \<forall> x \<in> introduction. finite(x@authored_by)
%%\<close>}
%% \fixme{experiment... }
where \inlineisar+result+, \inlineisar+conclusion+, and
%%  where \<open>result\<close>, \<open>conclusion\<close>, and
\inlineisar+introduction+ are the set of all possible instances of
these document classes.  All specified constraints are already checked
in the IDE of \dof while editing; it is however possible to delay a
final error message till the closing of a monitor (see next
section). The third constraint enforces that the
%% user sets the \<open>authored_by\<close> set, otherwise an error will be
user sets the \inlineisar+authored_by+ set, otherwise an error will be
reported.
\<close>
text\<open>
For the moment, there is no high-level syntax for the definition of
class invariants. A formulation, in SML, of the first class-invariant
in \autoref{sec:class_inv} is straight-forward:
\begin{sml}
fun check_result_inv oid {is_monitor:bool} ctxt =
  let val kind = compute_attr_access ctxt "kind" oid <AT>{here} <AT>{here}
      val prop = compute_attr_access ctxt "property" oid <AT>{here} <AT>{here}
      val tS = HOLogic.dest_list prop
  in  case kind_term of
       <AT>{term "proof"} => if not(null tS) then true
                          else error("class result invariant violation")
      | _ => false
  end
 val _ = Theory.setup (DOF_core.update_class_invariant
                                "tiny_cert.result" check_result_inv)
\end{sml}
The \inlinesml{setup}-command (last line) registers the
\inlineisar+check_result_inv+ function into the \isadof kernel, which
activates any creation or modification of an instance of
\inlineisar+result+.  We cannot replace \inlineisar+compute_attr_access+
by the corresponding antiquotation
\inlineisar+<AT>{docitem_value kind::oid}+, since \inlineisar+oid+ is
bound to a variable here and can therefore not be statically expanded.

Isabelle's code generator can in principle generate class invariant code
from a high-level syntax. Since class-invariant checking can result in an
efficiency problem ---they are checked on any edit--- and since invariant
programming involves a deeper understanding of ontology modeling and the
\isadof implementation, we backed off from using this technique so far.

\<close>

section*["core-manual"::technical]\<open>Annotatable Text-Elements for Core-Documents\<close>
text\<open>In general, all standard text-elements from the Isabelle document model such
as @{command "chapter"}, @{command "section"}, @{command "text"}, have in the \isadof
implementation their counterparts in the family of text-elements that are "ontology-aware",
\ie they dispose on a meta-argument list that allows to define that a test-element
\<^enum> has an identity as a text-object labelled as \<open>obj_id\<close>
\<^enum> belongs to a document class \<open>class_id\<close> that has been defined earlier
\<^enum> has its class-attributes set with particular values
  (which are denotable in Isabelle/HOL mathematical term syntax)
\<close>

subsection\<open>Annotating with Ontology Meta-Data: Outer Syntax\<close>
text\<open>\dof introduces its own family of text-commands, which allows 
having side effects of the global context \inlineisar+\<theta>+ and thus to 
store and manage own meta-information. Among others, \dof provides the commands
\inlineisar+section*[<meta-args>]\<Open>...\<Close>+, 
\inlineisar+subsection*[<meta-args>]\<Open>...\Cclose>+, or
\inlineisar+text*[<meta-args>]\<Open>...\<Close>+. Here, the argument 
\inlineisar+<meta-args>+ is a syntax for declaring instance, class and
attributes for this text element, following the scheme
\begin{isar}
  <ref> :: <class_id>, attr_1 = <expr>, ..., attr_n = <expr>  
\end{isar}
The \inlineisar+<class_id>+ can be  omitted, which
represents the implicit superclass \inlineisar+text+, where
\inlineisar+attr_i+ must be declared attributes in the class and where
the HOL \inlineisar+<expr>+ must have the corresponding HOL type. Attributes
from a class definition may be left undefined; definitions of
attribute values \<^emph>\<open>override\<close> default values or values of
super-classes. Overloading of attributes is not permitted in
\dof. 
\<close>

text\<open>
We can now annotate a text as follows. First, we have to place a
particular document into the context of our conceptual example
ontology (\autoref{lst:doc}):
\begin{isar}
theory Steam_Boiler
  imports
    tiny_cert  (* The ontology defined in Listing 1.1. *)
begin
\end{isar}
This opens a new document (theory), called
\texttt{Steam\_Boiler} that imports our conceptual example ontology
``\texttt{tiny\_cert}'' (stored in a file
\texttt{tiny\_cert.thy}).\footnote{The usual import-mechanisms of the
  Isabelle document model applies also to ODL: ontologies can be
  extended, several ontologies may be imported, a document can
  validate several  ontologies.}

\noindent Now we can continue to annotate our text as follows:
\begin{isar}
title*[a] \<Open>The Steam Boiler Controller\<Close>
abstract*[abs, safety_level="SIL4", keywordlist = "[''controller'']"]\<Open>
  We present a formalization of a program which serves to control the
  level of water in a steam boiler.
\<Close>

section*[intro::introduction]\<Open>Introduction\<Close>
text\<Open>We present ...\<Close>

section*[T1::technical]\<Open>Physical Environment\<Close>
text\<Open>
  The system comprises the following units
  [*] the steam-boiler
  [*] a device to measure the quantity of water in the steam-boiler
  [*] ... 
\<Close>
\end{isar}

\<close>

text\<open>
Where \inlineisar+title*[a ...]+ is a predefined macro for
\inlineisar+text*[a::title,...]\<Open>...\<Close>+ (similarly \inlineisar+abstract*+). 
The macro \inlineisar+section*+ assumes a class-id referring to a class that has 
a \inlineisar+level+ attribute. We continue our example text:
\begin{isar}[mathescape]
text*[c1::contrib_claim, based_on="[''pumps'',''steam boiler'']" ]\<Open>
  As indicated in <@>{introduction "intro"}, we the water level of the
  boiler is always between the minimum a$$nd the maximum allowed level.
\<Close>
\end{isar}
\<close>
text\<open>
The first text element in this example fragment \<^emph>\<open>defines\<close> the
text entity \inlineisar+c1+ and also references the formerly defined
text element \inlineisar+intro+ (which will be represented in the PDF
output, for example, by a text anchor ``Section 1'' and a hyperlink to
its beginning). The antiquotation \inlineisar+<@>{introduction ...}+,
which is automatically generated from the ontology, is immediately
validated (the link to \inlineisar+intro+ is defined) and type-checked (it
is indeed a link to an \inlineisar+introduction+
text-element). Moreover, the IDE automatically provides editing and
development support such as auto-completion or the possibility to
``jump'' to its definition by clicking on the antiquotation. The
consistency checking ensures, among others, that the final document
will not contain any ``dangling references'' or references to entities of
another type.
\<close>
text\<open>
\dof as such does not require a particular evaluation strategy;
however, if the underlying implementation is based on a
declaration-before-use strategy, a mechanism for forward declarations
of references is necessary:  
\begin{isar}
declare_reference* [<meta-args>]
\end{isar}
This command declares the existence of a text-element and allows for
referencing it, although the actual text-element will occur later in
the document.
\<close>


subsection\<open>Editing Documents with Ontology Meta-Data: Inner Syntax\<close>
text\<open>We continue our running example as follows:
\begin{isar}[mathescape]
text*[d1::definition]\<Open>
  We define the water level <AT>{term "level"} of a system state
  <AT>{term "\<sigma>"} of the steam boiler as follows: 
\<Close>
definition level :: "state \<rightarrow> real" where
          "level \<sigma> =  level0 + ..." 
update_instance*[d1::definition,
                 property += "[<AT>{term ''level \<sigma> =  level0 + ...''}]"]

text*[only::result,evidence="proof"]\<Open>
  The water level is never lower than <AT>{term "level0"}:
\<Close>
theorem level_always_above_level_0: "\<forall> \<sigma>. level \<sigma> \<geq> level0"
  unfolding level_def
  by auto
update_instance*[only::result,
                 property += "[<AT>{thm ''level_always_above_level_0''}]"]
\end{isar}
\<close>
text\<open>
As mentioned earlier, instances of document classes are mutable. We
use this feature to modify meta-data of these text-elements and
``assign'' them to the property-list afterwards and add results
from Isabelle definitions and proofs. The notation
\inlineisar|A+=X| stands for \inlineisar|A := A + X|. This mechanism
can also be used to define the required relation between \<^emph>\<open>claims\<close>
and \<^emph>\<open>results\<close> required in the \inlineisar|establish|-relation
required in a \inlineisar|summary|.
\<close>

subsection*["core-manual1"::technical]\<open>Annotatable Test-Elements: Syntax\<close>

text\<open>The syntax of toplevel \isadof commands reads as follows: 
\<^item> \<open>annotated_text_element\<close> :
\<^rail>\<open>
    (  ( @@{command "title*"}
       | @@{command "subtitle*"}
       | @@{command "chapter*"} 
       | @@{command "section*"} | @@{command "subsection*"} 
       | @@{command "subsubsection*"} | @@{command "paragraph*"} | @@{command "subparagraph*"} 
       | @@{command "text*"} | @@{command "figure*"} | @@{command "side_by_side_figure*"}
       | @@{command "open_monitor*"} | @@{command "close_monitor*"} 
       | @@{command "Definition*"} | @@{command "Lemma*"} 
       | @@{command "Theorem*"}  | @@{command "Conjecture*"} 
       ) 
       \<newline>
       '[' meta_args ']' '\<open>' text '\<close>'
     ) 
     | change_status_command
     | inspection_command
  \<close>
\<^item> \<open>meta_args\<close> : 
   \<^rail>\<open>(obj_id ('::' class_id) ((attribute '=' term)) * ',')\<close>
\<^item> \<open>rich_meta_args\<close> :
   \<^rail>\<open> (obj_id ('::' class_id) ((attribute (('=' | '+=') term)) * ','))\<close>
\<^item> \isadof\<open>change_status_command\<close> :
  \<^rail>\<open>  (@@{command "update_instance*"} '[' rich_meta_args ']')
       |  (@@{command "declare_reference*"} (obj_id ('::' class_id)))\<close>
\<^item> \isadof\<open>inspection_command\<close> :
   \<^rail>\<open>  @@{command "print_doc_classes"}
        |  @@{command "print_doc_items"} 
        |  @@{command "check_doc_global"}\<close>
\<close>

subsection*["commonlib"::technical]\<open>Common Ontology Library (COL)\<close>



subsection*["core-manual2"::technical]\<open>Examples\<close>


(*<*)
end
(*>*) 
  
