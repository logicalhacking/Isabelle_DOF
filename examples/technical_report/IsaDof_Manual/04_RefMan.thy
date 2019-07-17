(*<*)
theory "04_RefMan"
  imports "03_GuidedTour"
begin
(*>*)

chapter*[isadof::technical,main_author="Some(@{docitem ''bu''}::author)"]
\<open> \isadof : Syntax and Semantics of Commands\<close>
   
text\<open> An \isadof document consists of three components: 
\<^item> the \<^emph>\<open>ontology definition\<close> which is an Isabelle theory file with definitions
  for document-classes and all auxiliary datatypes.  
\<^item> the \<^emph>\<open>core\<close> of the document itself which is an Isabelle theory
  importing the ontology definition. \isadof provides an own family of text-element
  commands such as \inlineisar+title*+, \inlineisar+chapter*+,  \inlineisar+text*+, etc., 
  which can be annotated with meta-information defined in the underlying  ontology definition.
\<^item> the \<^emph>\<open>layout definition\<close> for the given ontology exploiting this meta-information.
\<close>
text\<open>\isadof is a novel Isabelle system component providing specific support for all these 
three parts. Note that the document core \<^emph>\<open>may\<close>, but \<^emph>\<open>must\<close> not 
use Isabelle definitions or proofs for checking the formal content---the 
present paper is actually an example of a document not containing any proof.

 The document generation process of \isadof is currently restricted to \LaTeX, which means
that the layout is defined by a set of \LaTeX{} style files. Several layout 
definitions for one ontology are possible and pave the way that different \<^emph>\<open>views\<close> for
the same central document were generated, addressing the needs of different purposes `
and/or target readers. 

 While the ontology and the layout definition will have to be developed by an expert
with knowledge over Isabelle and \isadof and the back end technology depending on the layout 
definition, the core is intended to require only minimal knowledge of these two. The situation
is similar to \LaTeX{}-users, who usually have minimal knowledge about the content in 
style-files (\<^verbatim>\<open>.sty\<close>-files). In the document core authors \<^emph>\<open>can\<close>  use \LaTeX{}  commands in 
their source, but this limits the possibility of using different representation technologies, 
\eg, HTML, and increases the risk of arcane error-messages in generated \LaTeX{}. 

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


section*[install::technical]\<open>Installation\<close>
text\<open>
To start using \isadof, one creates an Isabelle project (with the name 
\inlinebash{IsaDofApplications}):
\begin{bash}
  isabelle DOF_mkroot -o scholarly_paper -t lncs -d  IsaDofApplications
\end{bash}
where the \inlinebash{-o scholarly_paper} specifies the ontology for writing scientific articles and 
\inlinebash{-t lncs} specifies the use of Springer's \LaTeX-configuration for the Lecture Notes in 
Computer Science series. The project can be formally checked, including the generation of the 
article in PDF using the  following command:
\begin{bash}
  isabelle build -d . IsaDofApplications
\end{bash}
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

subsection*["core-manual1"::technical]\<open>Syntax\<close>

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

section*["odl-manual"::technical]\<open>The ODL Manual\<close>

subsection*["odl-manual1"::technical]\<open>The ODL Command Syntax\<close>

section*["odl-design"::technical]\<open>The Design of ODL\<close>

subsection*[onto_future::technical]\<open> Monitor Classes \<close>  
(*
text\<open> Besides sub-typing, there is another relation between
document classes: a class can be a \<^emph>\<open>monitor\<close> to other ones,
which is expressed by the occurrence of a \inlineisar+where+ clause
in the document class definition containing a regular
expression (see @{example (unchecked) \<open>scholar_onto\<close>}).
While class-extension refers to data-inheritance of attributes,
a monitor imposes structural constraints -- the order --
in which instances of monitored classes may occur. \<close>
*)
text\<open>
The control of monitors is done by the commands:
\<^item> \inlineisar+open_monitor* +  <doc-class>
\<^item> \inlineisar+close_monitor* + <doc-class> 
\<close>
text\<open>
where the automaton of the monitor class is expected
to be in a final state. In the final state, user-defined SML 
Monitors can be nested, so it is possible to "overlay" one or more monitoring 
classes and imposing different sets of structural constraints in a 
Classes which are neither directly nor indirectly (via inheritance) mentioned in the 
monitor are \<^emph>\<open>independent\<close> from a monitor; instances of independent test elements 
may occur freely. \<close>


subsection*["odl-manual2"::technical]\<open>Examples\<close>




(*<*)
end
(*>*) 
  
