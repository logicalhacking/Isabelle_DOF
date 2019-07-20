(*<*)
theory "05_DesignImpl"
  imports "04_isaDofImpl"
begin
(*>*)

chapter*[impl2::technical,main_author="Some(@{docitem ''bu''}::author)"]
   \<open>\isadof: Design and Implementation\<close>
text\<open>
In this section, we present the design and implementation of \isadof.
\subsection{Document Ontology Modeling with \isadof}
First, we introduce an own language to define ontologies.
Conceptually, ontologies consist of:
\begin{compactitem}  
\item a \emph{document class} that describes a concept, \ie, it
  represents set of \emph{instances} of a document class,
  i.e. references to document elements;
\item \emph{attributes} specific to document classes;
\item attributes should be typed (arbitrary HOL-types);
\item attributes can refer to other document classes,
  thus, document classes must also be HOL-types
  (Such attributes were called \emph{links});
\item a special link, the reference to a super-class,
  establishes an \emph{is-a} relation between classes;
\item classes may refer to other classes via a regular expression in a
  \emph{where} clause (classes with such an optional where clauses are
  called \emph{monitor classes});
\item attributes may have default values in order to facilitate notation.
\end{compactitem}
\<close>
text\<open>

For ontology modeling, we chose a syntax roughly similar to
Isabelle/HOL's extensible records.  We present the syntax implicitly
by a conceptual example, that serves to introduce the key-features of
the modeling language:
\begin{isar}
doc_class A =
   x :: "string"  

doc_class B =
   y :: "string list"             <= "[]"

doc_class C = B +
   z :: "A option"                <= "None"

datatype enum = "X1" | "X2" | "X3
   
doc_class D = B +
   a1 :: enum                     <= "X2"
   a2 :: int                      <= "0"

doc_class F  = 
   r :: "thm list"
   b :: "(A \<times> B) set"      <= "{}"

doc_class M = 
   trace :: "(A + C + D + F) list"
   where "A . (C | D)* . [F]"
\end{isar}
Isabelle uses a two level syntax: the \emph{outer syntax} which is
defined and extended using the mechanisms described in
\autoref{sec:plugins} and the \emph{inner syntax}, is used to define
type and term expressions of the Isabelle framework. Since we reuse a
lot of infrastructure of HOL (with respect to basic type library
definitions), parsing and type-checking have been specialized to HOL
and extensions thereof.  The ``switch'' between outer and inner syntax
happens with the quote symbols
\inlineisar+"..."+. % In exceptional cases, the latter can be
% omitted --- notably, if the type or term consists only of one type
% constructor symbol or constant symbol respectively.
%
\<close>
text\<open>
The above ontology specification contains the document classes
\inlineisar+A+, \inlineisar+B+, \inlineisar+C+, \inlineisar+D+,
\inlineisar+F+, and \inlineisar+M+ with the respective attributes
\inlineisar+x+, \inlineisar+y+, \inlineisar+z+, \inlineisar+a1+,
\inlineisar+a2+, \inlineisar+b+ and \inlineisar+trace+.
\inlineisar+C+ and \inlineisar+D+ is are sub-classes from
\inlineisar+B+ as states the class extension \inlineisar*B + ... *.

\enlargethispage{2\baselineskip}
\<close>
text\<open>
Each attribute is typed within the given context; the general HOL
library provides the types \inlineisar+string+, \inlineisar+_ list+,
\inlineisar+_ option+, and \inlineisar+_ set+.  On the fly, other
special purpose types can be defined. We reuse here the Isabelle/HOL
\inlineisar+datatype+-statement, which can be mixed arbitrarily in
between the ontology definitions (like any other Isabelle/HOL command)
to define an enumeration type.  Document classes---similar to
conventional class-definitions as in object-oriented
programming---\emph{induce} an implicit HOL type; for this reason the
class \inlineisar+C+ can have an attribute that refers to the
\inlineisar+A+ attribute classes. Document classes that contain
attributes referring to induced class types are called
\emph{links}. Links can be complex: the class \inlineisar+F+, for
example, contains a set of pairs, \ie, a relation between
\inlineisar+A+ and \inlineisar+B+ document instances. Each attribute
may be assigned (via \inlineisar+<=+) to a default value represented
by a HOL expression, whose syntax is either defined by library
operations or constant declarations like the
\inlineisar+datatype+-statement.
\<close>
text\<open>
The document class \inlineisar+M+ is a \emph{monitor class}, \ie, a
class possessing a \inlineisar+where+ clause containing a regular
expression consisting of the class identifier \inlineisar+A+,
\inlineisar+B+, etc. Its use is discussed in \autoref{sec:monitor-class}.
\<close>

subsection*[editing::example]\<open>Editing a Document with Ontology-Conform Meta-Data\<close>
text\<open>
As already mentioned, Isabelle/Isar comes with a number of standard
\emph{text commands} such as \inlineisar+section{* ... *}+ or
\inlineisar+text{* ... *}+ that offer the usual text structuring
primitives for documents.  From the user point-of-view, text commands
offer the facility of spell-checking and IDE support for text
antiquotations (as discussed before), from a system point of view,
they are particular since they are not conceived to have side effects
on the global (formal) context, which is exploited in Isabelle's
parallel execution engine.\<close>

text\<open>
\isadof introduces an own family of text-commands based on the
standard command API of the Isar engine, which allows having
side effects of the global context and thus to store and manage own
meta-information (the standard text-command interface turned out not
to be flexible enough, and a change of this API conflicts with our
goal of not changing Isabelle itself). \isadof, \eg, provides
\inlineisar+section*[<meta-args>]{* ... *}+,
\inlineisar+subsection*[<meta-args>]{* ... *}+,
or \inlineisar+text*[<meta-args>]{* ... *}+, where
\inlineisar+<meta-args>+ is a syntax to declaring instance, class and
attributes for this text element. The syntax for
\inlineisar+<meta-args>+ follows the scheme:
\begin{isar}
  <ref> :: <class_id>, attr_1 = "<expr>", ..., attr_n = "<expr>"
\end{isar}
where the \inlineisar+<class_id>+ can be optionally omitted which represents
the implicit superclass \inlineisar+text+, where \inlineisar+attr_i+ must
be declared attributes in the class and where the \inlineisar+"<expr>"+
must have the corresponding type. Attributes from a class definition may
be left undefined; definitions of attribute values \emph{override} default
values or values of super-classes. Overloading of attributes, however, is not
permitted in \isadof. \<close>

text\<open>
We can annotate a text as follows. First, we have to place a
particular document into the context of our conceptual example
ontology shown above:
\begin{isar}
theory Concept_Example
  imports Isabelle_DOF.Conceptual
begin
\end{isar}
which is contained contained a theory file
\verb+ontologies/Conceptual.thy+ in the \isadof distribution.  Then we can continue to annotate
our text as follows:
\begin{isar}
  section*[a::A, x = "''alpha''"] {* Lorem ipsum dolor sit amet, ... *}
  
  text*[c1::C, x = "''beta''"] 
  {* ... suspendisse non arcu malesuada mollis, nibh morbi, ...  *}
  
  text*[d:D, a2="10"]{* Lorem ipsum dolor sit amet, consetetur  ...*}
\end{isar}\<close>

text\<open>
Let's consider the last line:
this text is the instance \inlineisar+d+ which belongs to class
\inlineisar+D+, and the default of its attribute \inlineisar+a2+ is
overridden to the value \inlineisar+"10"+. Instances are mutable in
\isadof, the subsequent \isadof command:
\begin{isar}
  update_instance*[d::D, a1 := X2, a2 := "20"]
\end{isar}
This changes the attribute values of \verb+d+. The typing
annotation \verb+D+ is optional here (if present, it is checked).\<close>

text\<open>
Document instances were used to reference textual content; in the
generated \LaTeX{} (PDF) and HTML documents they were supported by
hyperlinks. Since Isabelle/Isar has a top-down evaluation and
validation strategy for the global document, a kind of forward
declaration for references is sometimes necessary.
\begin{isar}
  declare_reference* [<meta-args>]
\end{isar}
This declares the existence of a text-element and allows for
referencing it, although the actual text-element will occur later in
the document.\<close>


subsection*[ontolinks::technical]\<open>Ontology-Conform Logical Links: \isadof Antiquotations\<close>
text\<open>
Up to this point, the world of the formal and the informal document
parts are strictly separated. The main objective of \isadof are ways
to establish machine-checked links between these two universes by
instantiating automatically Isabelle/Isar's concept of
\emph{antiquoations}. The simplest form of link appears in the
following command:
\begin{isar}
  text{* ... in ut tortor ... @ {docitem_ref {*a*}} ... @ {A {*a*}}*}  
\end{isar}\<close>
text\<open>
This standard text-command contains two \isadof antiquotations; the
first represents just a link to the text-element \inlineisar$a$.
The second contains additionally the implicit constraint that the
reference to \inlineisar$a$ must also belong to the
\inlineisar$A$-class; the following input:
\begin{isar}
  text{* ...  ...  ... @ {C (*a*}}*}
\end{isar}
results in the detection of an ontological inconsistency which will be
reported in PIDE at editing time. Of course, any modification of the
ontology or changes in the labeling of the meta-information will lead
to the usual re-checking of the Isabelle/Isar engine. A natural
representation of these semantic links inside \isadof documents would
be hyperlinks in generated PDF or HTML files.
\enlargethispage{2\baselineskip}\<close>

text\<open>
Besides text antiquotations from Isabelle/Isar, we introduced a novel
concept that we call \emph{inner syntax antiquotations}. It is a
crucial technical feature for establishing links between text-items as
well as document meta-data and formal entities of Isabelle such as
types, terms and theorems (reflecting the fundamental types
\inlineisar+typ+, \inlineisar+term+ and \inlineisar+thm+ of the
Isabelle kernel.) We start with a slightly simpler case is the
establishment of links between text-elements:
\begin{isar}  
section*[f::F] {* Lectus accumsan velit ultrices, ... }*}

update_instance*[f,b:="{(@ {docitem  ''a''}::A,@ {docitem  ''c1''}::C), 
                        (@ {docitem  ''a''},@ {docitem  ''c1''})}"] 
\end{isar}\<close>

text\<open>

This example shows the construction of a relation between text
elements \emph{inside} HOL-expressions with the usual syntactic and
semantic machinery for sets, pairs, (thus: relations).  Inside the
world of HOL-terms, we can refer to items of the ``meta-world'' by a
particular form of antiquotations called \emph{inner syntax
  antiquotations}. Similarly, but conceptually different, it is
possible to refer in \isadof HOL-expressions to theorems of the
preceding context. Thus, it is possible to establish a theorem (or a
type or term), in the example below, by a proof ellipse in Isabelle:
\begin{isar}  
  theorem some_proof : "P" sorry

  update_instance*[f,r:="[@ {thm ''some_proof''}]"]
\end{isar}\<close>
text\<open>
The resulting theorem is stored in a theorem list as part of the
meta-information of a section.  Technically, theorems were introduced
in \isadof as abstract HOL types and some unspecified (Skolem)
HOL-constants with a particular infix-syntax. They are introduced for
example by:
\begin{isar}
  typedecl "thm"
  consts mk_thm  :: "string \<Rightarrow> thm"  ("@{thm _}")   
\end{isar}
which introduces a new type \inlineisar+thm+ reflecting the internal
Isabelle type for established logical facts and the above notation to
the inner syntax parser. The \inlineisar+doc_class F+ in our schematic
example uses already this type.  Whenever these expressions occur
inside an inner-syntax HOL-term, they are checked by the HOL parser
and type-checker as well as an \isadof checker that establishes that
\inlineisar+some_proof+ indeed refers to a known theorem of this name
in the current context.
% (this is, actually, the symmetry axiom of the equality in HOL).
To our knowledge, this is the first ontology-driven framework for
editing mathematical and technical documents that focuses particularly
on documents mixing formal and informal content---a type of documents
that is very common in technical certification processes. We see
mainly one area of related works: IDEs and text editors that support
editing and checking of documents based on an ontology.  There is a
large group of ontology editors (\eg, Prot{\'e}g{\'e}~\cite{protege},
Fluent Editor~\cite{cognitum}, NeOn~\cite{neon}, or
OWLGrEd~\cite{owlgred}). With them, we share the support for defining
ontologies as well as auto-completion when editing documents based on
an ontology. While our ontology definitions are, currently, based on a
textual definition, widely used ontology editors (\eg,
OWLGrEd~\cite{owlgred}) also support graphical notations. This could
be added to \isadof in the future. A unique feature of \isadof is the
deep integration of formal and informal text parts. The only other
work in this area wea are aware of is rOntorium~\cite{rontorium}, a plugin
for Prot{\'e}g{\'e} that integrates R~\cite{adler:r:2010} into an
ontology environment. Here, the main motivation behind this
integration is to allow for statistically analyze ontological
documents. Thus, this is complementary to our work.\<close>

text\<open>
There is another form of antiquotations, so-called ML-antiquotations
in Isabelle, which we do not describe in detail in this paper. With
this specific antiquotations, it is possible to refer to the HOL-term
of all the attributes of the doc-item; by writing specific ML-code,
arbitrary user-defined criteria can be implemented establishing that
all meta-data of a document satisfies a particular validation. For
example, in the context of an ontology for scientific papers, we could
enforce that terms or theorems have a particular form or correspond to
``claims'' (contributions) listed in the introduction of the paper.
\<close>

subsection*["sec:monitor-class"::technical]\<open>Monitor Document Classes\<close>
text\<open>
\autoref{lst:example} shows our conceptual running example in all
details. While inheritance on document classes allows for structuring
meta-data in an object-oriented manner, monitor classes such as
\inlineisar+M+ impose a structural relation on a document.  The
\inlineisar+where+ clause permits to write a regular expression on
class names; the class names mentioned in the where clause are called
the ``controlled'' ones.  The expression specifies that all
text-elements that are instances of controlled classes to occur in the
sequential order specified by the \inlineisar+where+-clause. Start and
end were marked by the corresponding monitor commands. Note that
monitors may be nested.
\<close>
text\<open>
\begin{isar}[float, caption={Our running example},label={lst:example}]
 theory Concept_Example
   imports "Isabelle_DOF.Conceptual"
 begin
 
 open_monitor*[struct::M]  
 
 section*[a::A, x = "''alpha''"] {* Lorem ipsum dolor sit amet, ... *}
 
 text*[c1::C, x = "''beta''"] 
 {* ... suspendisse non arcu malesuada mollis, nibh morbi, ...  *}
   
 text*[d::D, a1 = "X3"] 
 {* ... phasellus amet id massa nunc, pede suscipit repellendus, ... *}
 
 text*[c2::C, x = "''delta''"] 
 {* ... in ut tortor eleifend augue pretium consectetuer.  *}
 
 section*[f::F] {* Lectus accumsan velit ultrices, ...  @ {docitem_ref {*a*} }*}
   
 theorem some_proof : "P" sorry
     
 update_instance*[f,r:="[@ {thm ''some_proof''}]"]
 
 text{* ..., mauris amet, id elit aliquam aptent id,  ... *}
   
 update_instance*[f,b:="{(@ {docitem  ''a''}::A,@ {docitem  ''c1''}::C), 
                         (@ {docitem  ''a''},   @ {docitem  ''c1''})}"] 
   
 close_monitor*[struct]
\end{isar}
\<close>

section\<open>Document Generation\<close>
text\<open>
Up to know, we discussed the definition of ontologies and their
representation in an interactive development environment, \ie,
JEdit/PIDE. In many application areas, it is desirable to also
generate a ``static'' document, \eg, for long-term archiving. Isabelle
supports the generation of both HTML and PDF documents. Due to its
standardization, the latter (in particular in the variant PDF/A) is
particularly suitable for ensuring long-term access. Hence, our
prototype focuses currently on the generation of consistent PDF
documents.\<close>

text\<open>
Technically, the PDF generation is based on \LaTeX{} (this is mostly
hidden from the end users) as standard text formatting such as
itemize-lists or italic and bold fonts can be written in JEdit without
in a ``what-you-see-is-what-you-get''-style. We extended the \LaTeX{}
generation of Isabelle in such a way that for each ontological concept
that is formally defined in \isadof, is mapped to a dedicated
\LaTeX-command. This \LaTeX-command is responsible for the actual
typesetting of the concept as well as for generating the necessary
label and references. For each defined ontology, we need to define a
\LaTeX-style that defines these commands. For the standard commands
such as \inlineisar|section*[...]{* ... *}|, default implementations
are provided by \isadof.  For example, the following is the \LaTeX{}
definition for processing \inlineisar|section*[...]{* ... *}|: 
\begin{ltx}
\newkeycommand\isaDofSection[reference=,class_id=][1]{%
  \isamarkupsection{#1}\label{\commandkey{reference}}%
}
\end{ltx}\<close>
text\<open>
This command gets all meta-arguments of the concepts a swell as the
actual arguments. The layout is delegated to Isabelle's standard
sectioning commands
(\inlineltx|\isamarkupsection{#1}|). Additionally, a label for
linking to this section is generated.
\enlargethispage{2\baselineskip}
\<close>
text\<open>
Considering an ontology defining the concepts for writing scientific
papers, a potential definition for typesetting abstracts (where an
abstract includes a list of keywords) is:
\begin{ltx}
\newkeycommand\isaDofTextAbstract[reference=,class_id=,keywordlist=][1]{%
  \begin{isamarkuptext}%
    \begin{abstract}\label{\commandkey{reference}}%
      #1
      
      \ifthenelse{\equal{\commandkey{keywordlist}}{}}{}{%      
        \medskip\noindent{\textbf{Keywords:}} \commandkey{keywordlist}%
      }  
    \end{abstract}%
  \end{isamarkuptext}%
}
\end{ltx}
Our generated \LaTeX{} is conceptually very close
SALT~\cite{DBLP:conf/esws/GrozaHMD07}--- but instead of writing
\LaTeX{} manually it is automatically generated and, additionally, can
also guarantee the consistency of the formal (mathematical/logical)
content.
\<close>

(*<*) 
end
(*>*)
