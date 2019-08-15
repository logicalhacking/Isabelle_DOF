(*<*)
theory 
  "04_RefMan"
  imports 
    "03_GuidedTour" 
    "Isabelle_DOF.Isa_COL"
begin
(*>*)

chapter*[isadof_ontologies::text_section]\<open>Developing Ontologies\<close>

text\<open>
  In this chapter, we explain the concepts for modeling new ontologies, developing a document 
  representation for them, as well as developing new document templates. 
\<close>

section*[infrastructure::text_section]\<open>Overview and Technical Infrastructure\<close>
text\<open>
  \isadof is embedded in the underlying generic document model of Isabelle as described in
  @{docitem "dof"}. Recall that the document language can be extended dynamically, \ie, new
  \<open>user-defined\<close> can be introduced at run-time.  This is similar to the definition of new functions 
  in an interpreter. \isadof as a system plugin is is a number of new command definitions in 
  Isabelle's document model.

  \isadof consists consists basically of four components:
  \<^item> an own \<^emph>\<open>family of text-element\<close> such as @{command "title*"}, @{command "chapter*"}  
    @{command "text*"}, etc., which can be annotated with meta-information defined in the 
    underlying  ontology definition and allow to build a \<^emph>\<open>core\<close> document,
  \<^item> the \<^emph>\<open>ontology definition\<close> which is an Isabelle theory file with definitions
    for document-classes and all auxiliary datatypes 
    (called Ontology Definition Language (ODL)),
  \<^item> the ontology-specific \<^emph>\<open>layout definition\<close>, exploiting this meta-information, and 
  \<^item> the generic \<^emph>\<open>layout definition\<close> for documents following, \eg, the format guidelines of 
    publishers or standardization bodies. 
\<close>

text\<open> 
  The list of fully supported (\ie, supporting both interactive ontological modeling and 
  document generation) ontologies and the list of supported document templates can be 
  obtained by calling \inlinebash|isabelle mkroot_DOF -h| (see @{docitem "first_project"}).
  Note that the postfix \inlinebash|-UNSUPPORTED| denoted experimental ontologies or templates 
  for which further manual setup steps might be required or that are not fully tested. Also note 
  that the \LaTeX-class files required by the templates need to be already installed on your 
  system. This is mostly a problem for publisher specific templates (\eg, Springer's 
  \path{llncs.cls}), which, due to copyright restrictions, cannot be distributed legally.
\<close>

subsection\<open>Ontologies\<close>
text\<open>
  The document core \<^emph>\<open>may\<close>, but \<^emph>\<open>must\<close> not use Isabelle definitions or proofs for checking the 
  formal content---this manual is actually an example of a document not containing any proof.
  Consequently, the document editing and checking facility provided by \isadof addresses the needs 
  of common users for an advanced text-editing environment, neither modeling nor proof knowledge is 
  inherently required.

  We expect authors of ontologies to have experience in the use of \isadof, basic modeling (and, 
  potentially, some basic SML programming) experience, basic \LaTeX{} knowledge, and, last but not 
  least, domain knowledge of the ontology to be modeled. Users with experience in UML-like 
  meta-modeling will feel familiar with most concepts; however, we expect  no need for insight in 
  the Isabelle proof language, for example, or other more advanced concepts.

  Technically, ontologies\index{ontology!directory structure} are stored in a directory 
  \inlinebash|src/ontologies| and consist of a Isabelle theory file and a \LaTeX-style file:
\begin{center}
\begin{minipage}{.9\textwidth}
\dirtree{%
.1 .
.2 src.
.3 ontologies\DTcomment{Ontologies}.
.4 ontologies.thy\DTcomment{Ontology Registration}.
.4 CENELEC\_50128\DTcomment{CENELEC\_50128}.
.5 CENELEC\_50128.thy.
.5 DOF-CENELEC\_50128.sty.
.4 scholarly\_paper\DTcomment{scholarly\_paper}.
.5 scholarly\_paper.thy.
.5 DOF-scholarly\_paper.sty.
.4 \ldots.
}
\end{minipage}
\end{center}
\<close>
text\<open>
  Developing a new ontology ``\inlinebash|foo|'' requires, from a technical perspective, the 
  following steps:
  \<^item> create a new sub-directory \inlinebash|foo| in the directory \inlinebash|src/ontologies|
  \<^item> definition of the ontological concepts, using \isadof's Ontology Definition Language (ODL), in 
    a new theory file \path{src/ontologies/foo/foo.thy}.  
  \<^item> definition of the document representation for the ontological concepts in a \LaTeX-style 
    file \path{src/ontologies/foo/DOF-foo.sty}
  \<^item> registration (as import) of the new ontology in the file. 
   \path{src/ontologies/ontologies.thy}. 
  \<^item> activation of the new document setup by executing the install script. You can skip the lengthy 
    checks for the AFP entries and the installation of the Isabelle patch by using the 
    \inlinebash|--skip-patch-and-afp| option:
  
  \begin{bash}
ë\prompt{\isadofdirn}ë ./install --skip-patch-and-afp
  \end{bash}
\<close>

subsection\<open>Document Templates\<close>
text\<open>
  Document-templates\index{document template} define the overall layout (page size, margins, fonts, 
  etc.) of the generated documents and are the the main technical means for implementing layout 
  requirements that are, \eg, required by publishers or standardization bodies. Document-templates 
  are stored in a directory 
  \path{src/document-templates}:\index{document template!directory structure}
\begin{center}
\begin{minipage}{.9\textwidth}
\dirtree{%
.1 .
.2 src.
.3 document-templates\DTcomment{Document templates}.
.4 root-lncs.tex.
.4 root-scrartcl.tex.
.4 root-scrreprt-modern.tex.
.4 root-scrreprt.tex.
}
\end{minipage}
\end{center}
\<close>

text\<open>
  Developing a new document template ``\inlinebash|bar|'' requires the following steps:
  \<^item> develop a new \LaTeX-template \inlinebash|src/document-templates/root-bar.tex|
  \<^item> activation of the new document template  by executing the install script. You can skip the lengthy 
    checks for the AFP entries and the installation of the Isabelle patch by using the 
    \inlinebash|--skip-patch-and-afp| option:
  
  \begin{bash}
ë\prompt{\isadofdirn}ë ./install --skip-patch-and-afp
  \end{bash}
\<close>


text\<open>
  As the document generation of \isadof is based 
  on \LaTeX, the \isadof document templates can (and should) make use of any \LaTeX-classes provided
  by publishers or standardization bodies.
\<close>

section\<open>The Ontology Definition Language (ODL)\<close>

text\<open>
  ODL shares some similarities with meta-modeling languages such as UML class 
  models: It builds upon concepts like class, inheritance, class-instances, attributes, references 
  to instances, and class-invariants. Some concepts like  advanced type-checking, referencing to 
  formal entities of Isabelle, and monitors are due to its specific application in the 
  Isabelle context. Conceptually, ontologies specified in ODL consist of:
  \<^item> \<^emph>\<open>document classes\<close> (\inlineisar{doc_class}) that describe concepts;
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
    \<^emph>\<open>where\<close> clause;
  \<^item> attributes may have default values in order to facilitate notation.
\<close>

text\<open>
  The \isadof ontology specification language consists basically on a notation for document classes, 
  where the attributes were typed with HOL-types and can be instantiated by terms HOL-terms, \ie, 
  the actual parsers and type-checkers of the Isabelle system were reused. This has the particular 
  advantage that \isadof commands can be arbitrarily mixed with Isabelle/HOL commands providing the 
  machinery for type declarations and term specifications such
  as enumerations. In particular, document class definitions provide:
  \<^item> a HOL-type for each document class as well as inheritance, 
  \<^item> support for attributes with HOL-types and optional default values,
  \<^item> support for overriding of attribute defaults but not overloading, and
  \<^item> text-elements annotated with document classes; they are mutable 
    instances of document classes.
\<close>

text\<open>
  Attributes referring to other ontological concepts are called \<^emph>\<open>links\<close>. The HOL-types inside the 
  document specification language support built-in types for Isabelle/HOL \inlineisar+typ+'s,  
  \inlineisar+term+'s, and \inlineisar+thm+'s reflecting internal Isabelle's  internal types for 
  these entities; when denoted in HOL-terms to instantiate an attribute, for example, there is a  
  specific syntax (called \<^emph>\<open>inner syntax antiquotations\<close>) that is checked by 
  \isadof for consistency.

  Document classes\bindex{document class}\index{class!document@see document class} support 
  \inlineisar+where+-clauses\index{where clause} containing a regular expression over class 
  names. Classes with a \inlineisar+where+ were called 
  \<^emph>\<open>monitor classes\<close>.\bindex{monitor class}\index{class!monitor@see monitor class} While document 
  classes and their inheritance relation structure meta-data of text-elements in an object-oriented 
  manner, monitor classes enforce structural organization of documents via the language specified 
  by the regular expression enforcing a sequence of text-elements.

  A major design decision of ODL is to denote attribute values by HOL-terms and HOL-types. 
  Consequently, ODL can refer to any predefined type defined in the HOL library, \eg, 
  \inlineisar+string+ or \inlineisar+int+ as well as parameterized types, \eg, \inlineisar+_ option+, 
  \inlineisar+_ list+, \inlineisar+_ set+, or products \inlineisar+_ \<times> _+. As a consequence of the 
  document model, ODL definitions may be arbitrarily intertwined with standard HOL type definitions. 
  Finally, document class definitions result in themselves in a HOL-types in order to allow \<^emph>\<open>links\<close> 
  to and between ontological concepts.
\<close>

subsection*["odl-manual0"::technical]\<open>Some Isabelle/HOL Specification Constructs Revisited\<close>
text\<open>
  As ODL is an extension of Isabelle/HOL, document class definitions can therefore be arbitrarily 
  mixed with standard HOL specification constructs. To make this manual self-contained, we present 
  syntax and semantics of the specification constructs that are most likely relevant for the 
  developer of ontologies (for more details, see~@{cite "wenzel:isabelle-isar:2019"}.  Our 
  presentation is a simplification of the original sources following the needs of ontology developers 
  in \isadof:
  \<^item> \<open>name\<close>:\index{name@\<open>name\<close>}
     with the syntactic category of \<open>name\<close>'s we refer to alpha-numerical identifiers 
     (called \<open>short_id\<close>'s in @{cite "wenzel:isabelle-isar:2019"}) and identifiers
     in \inlineisar+" ... "+ which might contain certain ``quasi-letters'' such 
     as \inlineisar+_+, \inlineisar+-+, \inlineisar+.+. See~@{cite "wenzel:isabelle-isar:2019"} for details.
  \<^item> \<open>tyargs\<close>:\index{tyargs@\<open>tyargs\<close>} 
     \<^rail>\<open>  typefree | ('(' (typefree * ',') ')')\<close>
     \<open>typefree\<close> denotes fixed type variable(\<open>'a\<close>, \<open>'b\<close>, ...) (see~@{cite "wenzel:isabelle-isar:2019"})
  \<^item> \<open>dt_name\<close>:\index{dt\_npurdahame@\<open>dt_name\<close>}
     \<^rail>\<open>  (tyargs?) name (mixfix?)\<close>   
     The syntactic entity \<open>name\<close> denotes an identifier, \<open>mixfix\<close> denotes the usual 
     parenthesized mixfix notation (see @{cite "wenzel:isabelle-isar:2019"}).
     The \<open>name\<close>'s referred here are type names such as \<^verbatim>\<open>int\<close>, \<^verbatim>\<open>string\<close>, \<^verbatim>\<open>list\<close>, \<^verbatim>\<open>set\<close>, etc. 
  \<^item> \<open>type_spec\<close>:\index{type_spec@\<open>type_spec\<close>}
     \<^rail>\<open>  (tyargs?) name\<close>
     The \<open>name\<close>'s referred here are type names such as \<^verbatim>\<open>int\<close>, \<^verbatim>\<open>string\<close>, \<^verbatim>\<open>list\<close>, \<^verbatim>\<open>set\<close>, etc. 
  \<^item> \<open>type\<close>:\index{type@\<open>type\<close>}
     \<^rail>\<open>  (( '(' ( type * ',')  ')' )? name) | typefree \<close>     
\clearpage
  \<^item> \<open>dt_ctor\<close>:\index{dt\_ctor@\<open>dt_ctor\<close>}
     \<^rail>\<open> name (type*) (mixfix?)\<close>
  \<^item> \<open>datatype_specification\<close>:\index{datatype\_specification@\<open>datatype_specification\<close>}
     \<^rail>\<open> @@{command "datatype"} dt_name '=' (dt_ctor * '|' )\<close>
  \<^item> \<open>type_synonym_specification\<close>:\index{type\_synonym\_specification@\<open>type_synonym_specification\<close>}
     \<^rail>\<open> @@{command "type_synonym"} type_spec '=' type\<close>
  \<^item> \<open>constant_definition\<close> :\index{constant\_definition@\<open>constant_definition\<close>}
     \<^rail>\<open> @@{command "definition"} name '::' type 'where' '"' name '=' \<newline> expr '"'\<close>
  \<^item> \<open>expr\<close>:\index{expr@\<open>expr\<close>}
     the syntactic category \<open>expr\<close> here denotes the very rich ``inner-syntax'' language of 
     mathematical  notations for $\lambda$-terms in Isabelle/HOL. Example expressions are:
     \inlineisar|1+2| (arithmetics), \inlineisar|[1,2,3]| (lists), \inlineisar|''ab c''| (strings), 
     \inlineisar|{1,2,3}| (sets), \inlineisar|(1,2,3)| (tuples), 
     \inlineisar|\<forall> x. P(x) \<and> Q x = C| (formulas). For details, see~@{cite "nipkowMain19"}.
\<close>

text\<open>
  Advanced ontologies can, \eg,  use recursive function definitions with 
  pattern-matching~@{cite "functions19"}, extensible record 
  pecifications~@{cite "wenzel:isabelle-isar:2019"}, and abstract type declarations.
\<close>

text\<open>Note that \isadof works internally with fully qualified names in order to avoid 
confusions occurring otherwise, for example, in disjoint class hierarchies. This also extends to 
names for \inlineisar|doc_class|es, which must be representable as type-names as well since they
can be used in attribute types. Since theory names are lexically very liberal (\inlineisar|0.thy|
is a legal theory name), this can lead to subtle problems when constructing a class: \inlineisar|foo| 
can be a legal name for a type definition, the corresponding type-name \inlineisar|0.foo| is not.
For this reason, additional checks at the definition of a \inlineisar|doc_class| reject problematic
lexical overlaps.\<close>


subsection*["odl-manual1"::technical]\<open>Defining Document Classes\<close>
text\<open>
A document class\bindex{document class} can be defined using the @{command "doc_class"} keyword: 
\<^item> \<open>class_id\<close>:\index{class\_id@\<open>class_id\<close>} a type-\<open>name\<close> that has been introduced 
  via a \<open>doc_class_specification\<close>.
\<^item> \<open>doc_class_specification\<close>:\index{doc\_class\_specification@\<open>doc_class_specification\<close>}
     We call document classes with an \<open>accepts_clause\<close> 
     \<^emph>\<open>monitor classes\<close> or \<^emph>\<open>monitors\<close> for short.
     \<^rail>\<open> @@{command "doc_class"} class_id '=' (class_id '+')? (attribute_decl+) \<newline>
           (accepts_clause rejects_clause?)?\<close>
\<^item> \<open>attribute_decl\<close>:\index{attribute\_decl@\<open>attribute_decl\<close>}
     \<^rail>\<open> name '::' '"' type '"' default_clause? \<close>
\<^item> \<open>accepts_clause\<close>:\index{accepts\_clause@\<open>accepts_clause\<close>}
     \<^rail>\<open> 'accepts' '"' regexpr '"'\<close>
\<^item> \<open>rejects_clause\<close>:\index{rejects\_clause@\<open>rejects_clause\<close>}
     \<^rail>\<open> 'rejects' (class_id * ',') \<close>
\<^item> \<open>default_clause\<close>:\index{default\_clause@\<open>default_clause\<close>}
     \<^rail>\<open> '<=' '"' expr '"' \<close>
\<^item> \<open>regexpr\<close>:\index{regexpr@\<open>regexpr\<close>}
     \<^rail>\<open> '\<lfloor>' class_id '\<rfloor>' | '(' regexpr ')' | (regexpr '||' regexpr) | (regexpr '~~' regexpr)
            | ('\<lbrace>' regexpr '\<rbrace>') | ( '\<lbrace>' regexpr '\<rbrace>\<^sup>*')  \<close>
     Regular expressions describe sequences of \<open>class_id\<close>s (and indirect sequences of document
     items corresponding to the \<open>class_id\<close>s). The constructors for alternative, sequence, 
     repetitions and non-empty sequence follow in the top-down order of the above diagram. 
\<close> 

text\<open>
  \isadof provides a default document representation (\ie, content and layout of the generated 
  PDF) that only prints the main text, omitting all attributes. \isadof provides the 
  \inlineltx|\newisadof[]{}|\index{newisadof@\inlineltx{\newisadof}}\index{document class!PDF}
  command for defining a dedicated layout for a document class in \LaTeX. Such a document 
  class-specific \LaTeX-definition can not only provide a specific layout (\eg, a specific 
  highlighting, printing of certain attributes), it can also generate entries in in the table of 
  contents or an index. Overall, the \inlineltx|\newisadof[]{}| command follows the structure
  of the \inlineisar|doc_class|-command:

\begin{ltx}[escapechar=ë]
\newisadof{ë\<open>class_id\<close>ë}[label=,type=, ë\<open>attribute_decl\<close>ë][1]{%
  % ë\LaTeXë-definition of the document class representation
  \begin{isamarkuptext}%
  #1%
  \end{isamarkuptext}%
}
\end{ltx}

  The \<open>class_id\<close> is the full-qualified name of the document class and the list of \<open>attribute_decl\<close>
  needs to declare all attributes of the document class. Within the \LaTeX-definition of the document
  class representation, the identifier \inlineltx|#1| refers to the content of the main text of the 
  document class (written in \inlineisar|\<Open> ... \<Close>|) and the attributes can be referenced
  by their name using the \inlineltx|\commandkey{...}|-command (see the documentation of the 
  \LaTeX-package ``keycommand''~@{cite "chervet:keycommand:2010"} for details). Usually, the 
  representations definition needs to be wrapped in a 
  \inlineltx|\begin{isarmarkup}...\end{isamarkup}|-environment, to ensure the correct context 
  within Isabelle's \LaTeX-setup. 

  Moreover, \isadof also provides the following two variants of \inlineltx|\newisadof{}[]{}|:
  \<^item>  \inlineltx|\renewisadof{}[]{}|\index{renewisadof@\inlineltx{\renewisadof}} for re-defining 
     (over-writing) an already defined command, and  
  \<^item>  \inlineltx|\provideisadof{}[]{}|\index{provideisadof@\inlineltx{\provideisadof}} for providing 
     a definition if it is not yet defined. 
\<close>
text\<open>
  While arbitrary \LaTeX-commands can be used within these commands,
  special care is required for arguments containing special characters (\eg, the 
  underscore ``\_'') that do have a special meaning in \LaTeX.  
  Moreover, as usual, special care has to be taken for commands that write into aux-files
  that are included in a following \LaTeX-run. For such complex examples, we refer the interested 
  reader, in general, to  the style files provided in the \isadof distribution. In particular 
  the definitions of the concepts \inlineisar|title*| and \inlineisar|author*| in the file 
  \path{ontologies/scholarly_paper/DOF-scholarly_paper.sty} show examples of protecting special 
  characters in definitions that need to make use of a entries in an aux-file. 
\<close>

subsubsection\<open>Common Ontology Library (COL)\<close>

text\<open>\isadof uses the concept of implicit abstract classes (or: \emph{shadow classes}).
These refer to the set of possible \inlineisar+doc_class+ declarations that posses a number
of attributes with their types in common. Shadow classes represent an implicit requirement
(or pre-condition) on a given class to posses these attributes in order to work properly
for certain \isadof commands. 

shadow classes will find concrete instances in COL, but \isadof text elements do not \emph{depend}
on our COL definitions: Ontology developers are free to use to build own instances for these 
shadow classes, with own attributes and, last not least, own definitions of invariants independent
from ours.

In particular, these shadow classes are used at present in  \isadof:
\begin{isar}
DOCUMENT_ALIKES = 
   level         :: "int  option"    <=  "None" 

ASSERTION_ALIKES = 
    properties :: "term list"
  
FORMAL_STATEMENT_ALIKE =
    properties :: "thm list"
\end{isar}

These shadow-classes correspond to semantic macros 
 @{ML "ODL_Command_Parser.enriched_document_command"},
 @{ML "ODL_Command_Parser.assertion_cmd'"}, and
 @{ML "ODL_Command_Parser.enriched_formal_statement_command"}.\<close>

text\<open>  \isadof provides a Common Ontology Library (COL)\index{Common Ontology Library@see COL}\bindex{COL}
  that introduces ontology concepts that are either sample instances for shadow classes as we use
  them in our own document generation processes or, in some cases, are 
  so generic that they we expect them to be useful for all types of documents (figures, for example). 
\<close>


text\<open>
In particular it defines the super-class \inlineisar|text_element|: the
  root of all text-elements,

\begin{isar}
doc_class text_element = 
   level         :: "int  option"    <=  "None" 
   referentiable :: bool <= "False"
   variants      :: "String.literal set" <= "{STR ''outline'', STR ''document''}" 
\end{isar}

  Here, \inlineisar|level| defines the section-level (\eg, using a \LaTeX-inspired hierarchy:
  from \inlineisar|Some -1| (corresponding to \inlineltx|\part|) to 
  \inlineisar|Some 0| (corresponding to \inlineltx|\chapter|, respectively, \inlineisar|chapter*|) 
  to \inlineisar|Some 3| (corresponding to \inlineltx|\subsubsection|, respectively, 
  \inlineisar|subsubsection*|). Using an invariant, a derived ontology could, \eg, require that
  any sequence of technical-elements must be introduced by a text-element with a higher level
  (this would require that technical text section are introduce by a section element).

Similarly, we provide "minimal" instances of the \inlineisar+ASSERTION_ALIKES+ 
and \inlineisar+FORMAL_STATEMENT_ALIKE+ shadow classes:
\begin{isar}
doc_class assertions = 
    properties :: "term list"
  
doc_class "thms" =
    properties :: "thm list"
\end{isar}
\<close>

subsubsection\<open>Example: Text Elemens with Levels\<close>
text\<open>
  The category ``exported constraint (EC)'' is, in the file 
  \path{ontologies/CENELEC_50128/CENELEC_50128.thy} defined as follows:

\begin{isar}
doc_class requirement = text_element +
   long_name    :: "string option"
   is_concerned :: "role set"
doc_class AC = requirement +
   is_concerned :: "role set" <= "UNIV"
doc_class EC = AC  +
     assumption_kind :: ass_kind <= (*default *) formal
\end{isar}

  We now define the document representations, in the file 
  \path{ontologies/CENELEC_50128/DOF-CENELEC_50128.sty}. Let us assume that we want to 
  register the definition of ECs in a dedicated table of contents (\inlineltx{tos}) 
  and use an earlier defined environment \inlineltx|\begin{EC}...\end{EC}| for their graphical 
  representation. Note that the \inlineltx|\newisadof{}[]{}|-command requires the 
  full-qualified names, \eg,  \inlineisar|t$$ext.CENELEC_50128.EC| for the document class and 
  \inlineisar|CENELEC_50128.requirement.long_name| for the  attribute \inlineisar|long_name|, 
  inherited from the document class \inlineisar|requirement|. The document representation of ECs
  can now be defined as follows:

\begin{ltx}
\newisadof{text.CENELEC_50128.EC}%
[label=,type=%
,Isa_COL.text_element.level=%
,Isa_COL.text_element.referentiable=%
,Isa_COL.text_element.variants=%
,CENELEC_50128.requirement.is_concerned=%
,CENELEC_50128.requirement.long_name=%
,CENELEC_50128.EC.assumption_kind=][1]{%
\begin{isamarkuptext}%
   \ifthenelse{\equal{\commandkey{CENELEC_50128.requirement.long_name}}{}}{%
      % If long_name is not defined, we only create an entry in the table tos
      % using the auto-generated number of the EC 
      \begin{EC}%
          \addxcontentsline{tos}{chapter}[]{\autoref{\commandkey{label}}}%
    }{%
      % If long_name is defined, we use the long_name as title in the 
      % layout of the EC, in the table "tos" and as index entry. .
      \begin{EC}[\commandkey{CENELEC_50128.requirement.long_name}]%
        \addxcontentsline{toe}{chapter}[]{\autoref{\commandkey{label}}: %
              \commandkey{CENELEC_50128.requirement.long_name}}%
        \DOFindex{EC}{\commandkey{CENELEC_50128.requirement.long_name}}%
    }%
    \label{\commandkey{label}}% we use the label attribute as anchor 
    #1% The main text of the EC
  \end{EC}
\end{isamarkuptext}%
}
\end{ltx}
\<close>

subsubsection\<open>Example: Assertions\<close>
text\<open>Assertions are a common feature to validate properties of models, presented as a collection
of Isabelle/HOL definitions. They are particularly relevant for highlighting corner cases of a 
formal model.\<close>

definition last :: "'a list \<Rightarrow> 'a" where "last S = hd(rev S)"

text*[claim::assertions]\<open>For non-empty lists, our definition yields indeed the last element of a list.\<close>
assert*[claim::assertions] "last[4::int] = 4"
assert*[claim::assertions] "last[1,2,3,4::int] = 4"

text\<open>As an \inlineisar+ASSERTION_ALIKES+, the \inlineisar+assertions+ class possesses a 
\inlineisar+properties+ attribute. The \inlineisar+assert*+ command evaluates its argument;
in case it evaluates to true the property is added to the property list of the \inlineisar+claim+ - 
text-element. Commands like \inlineisar+Definitions*+ or \inlineisar+Theorem*+ work analogously.\<close>


subsection*["text-elements"::technical]\<open>Annotatable Top-level Text-Elements\<close>
text\<open>
  While the default user interface for class definitions via the  
  \inlineisar|text*\<Open> ... \<Close>|-command allow to access all features of the document 
  class, \isadof provides short-hands for certain, widely-used, concepts such as 
  \inlineisar|title*\<Open> ... \<Close>| or \inlineisar|section*\<Open> ... \<Close>|, \eg:

\begin{isar}
 title*[title::title]\<Open>Isabelle/DOF\<Close>
 subtitle*[subtitle::subtitle]\<Open>User and Implementation Manual\<Close>
 text*[adb:: author, email="\<Open>a.brucker@exeter.ac.uk\<Close>",
       orcid="\<Open>0000-0002-6355-1200\<Close>",
       http_site="\<Open>https://brucker.ch/\<Close>",
       affiliation="\<Open>University of Exeter, Exeter, UK\<Close>"] \<Open>Achim D. Brucker\<Close>
 text*[bu::author, email = "\<Open>wolff@lri.fr\<Close>",
       affiliation = "\<Open>Université Paris-Saclay, LRI, Paris, France\<Close>"]\<Open>Burkhart Wolff\<Close>
\end{isar}

  In general, all standard text-elements from the Isabelle document model such
  as @{command "chapter"}, @{command "section"}, @{command "text"}, have in the \isadof
  implementation their counterparts in the family of text-elements that are ontology-aware,
  \ie, they dispose on a meta-argument list that allows to define that a test-element
  that has an identity as a text-object labelled as \<open>obj_id\<close>, belongs to a document class 
  \<open>class_id\<close> that has been defined earlier, and  has its class-attributes set with particular 
  values (which are denotable in Isabelle/HOL mathematical term syntax).

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
\clearpage
\<^item> \<open>meta_args\<close> : 
   \<^rail>\<open>(obj_id ('::' class_id) ((attribute '=' term)) * ',')\<close>
\<^item> \<open>rich_meta_args\<close> :
   \<^rail>\<open> (obj_id ('::' class_id) ((attribute (('=' | '+=') term)) * ','))\<close>
\<close>


subsubsection\<open>Experts: Defining New Top-Level Commands\<close>

text\<open>
  Defining such new top-level commands requires some Isabelle knowledge as well as 
  extending the dispatcher of the \LaTeX-backend. For the details of defining top-level 
  commands, we refer the reader to the Isar manual~@{cite "wenzel:isabelle-isar:2019"}. 
  Here, we only give a brief example how the \inlineisar|section*|-command is defined; we 
  refer the reader to the source code of \isadof for details.

  First, new top-level keywords need to be declared in the \inlineisar|keywords|-section of 
  the theory header defining new keywords:

\begin{isar}
theory 
    ...
  imports
    ... 
  keywords
    "section*"
begin 
...
end
\end{isar}

  Second, given an implementation of the functionality of the new keyword (implemented in SML), 
  the new keyword needs to be registered, together with its parser, as outer syntax:

\begin{sml}
val _ =
  Outer_Syntax.command ("section*", <@>{here}) "section heading"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> (Toplevel.theory o (enriched_document_command (SOME(SOME 1)) 
           {markdown = false} )));
\end{sml}
\<close>

text\<open>
Finally, for the document generation, a new dispatcher has to be defined in \LaTeX---this is 
mandatory, otherwise the document generation will break. These dispatcher always follow the same 
schemata:

\begin{ltx}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% begin: section*-dispatcher
\NewEnviron{isamarkupsection*}[1][]{\isaDof[env={section},#1]{\BODY}}
% end: section*-dispatcher
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\end{ltx}

  After the definition of the dispatcher, one can, optionally, define a custom representation 
  using the \inlineltx|newisadof|-command, as introduced in the previous section: 

\begin{ltx}
\newisadof{section}[label=,type=][1]{%
  \isamarkupfalse%
    \isamarkupsection{#1}\label{\commandkey{label}}%
  \isamarkuptrue%
}
\end{ltx}
\<close>

subsection*["inspections-commands"::technical]\<open>Status and Inspection Commands\<close>
text\<open>
\<^item> \isadof\<open>change_status_command\<close> :
  \<^rail>\<open>  (@@{command "update_instance*"} '[' rich_meta_args ']')
       |  (@@{command "declare_reference*"} (obj_id ('::' class_id)))\<close>
\<^item> \isadof\<open>inspection_command\<close> :
   \<^rail>\<open>  @@{command "print_doc_classes"}
        |  @@{command "print_doc_items"} 
        |  @@{command "check_doc_global"}\<close>
\<close>



subsection*["sec:advanced"::technical]\<open>Advanced ODL Concepts\<close>
subsubsection\<open>Meta-types as Types\<close>

text\<open>
  To express the dependencies between text elements to the formal
  entities, \eg, \inlinesml+term+ ($\lambda$-term), \inlinesml+typ+, or
  \inlinesml+thm+, we represent the types of the implementation language
  \<^emph>\<open>inside\<close> the HOL type system.  We do, however, not reflect the data of
  these types. They are just declared abstract types, 
  ``inhabited'' by special constant symbols carrying strings, for
  example of the format \inlineisar+<@>{thm <string>}+. When HOL
  expressions were used to denote values of \inlineisar+doc_class+
  instance attributes, this requires additional checks after
  conventional type-checking that this string represents actually a
  defined entity in the context of the system state
  \inlineisar+\<theta>+.  For example, the \inlineisar+establish+
  attribute in the previous section is the power of the ODL: here, we model
  a relation between \<^emph>\<open>claims\<close> and \<^emph>\<open>results\<close> which may be a
  formal, machine-check theorem of type \inlinesml+thm+ denoted by, for
  example: \inlineisar+property = "[<@>{thm ''system_is_safe''}]"+ in a
  system context \inlineisar+\<theta>+ where this theorem is
  established. Similarly, attribute values like 
  \inlineisar+property = "<@>{term \<Open>A \<leftrightarrow> B\<Close>}"+
  require that the HOL-string \inlineisar+A \<leftrightarrow> B+ is 
  again type-checked and represents indeed a formula in $\theta$. Another instance of 
  this process, which we call \<open>second-level type-checking\<close>, are term-constants
  generated from the ontology such as 
  \inlineisar+<@>{definition <string>}+. 
\<close>


subsubsection*["sec:monitors"::technical]\<open>ODL Monitors\<close>
text\<open>
  We call a document class with an accept-clause a \<^emph>\<open>monitor\<close>.\bindex{monitor}  Syntactically, an 
  accept-clause\index{accept-clause} contains a regular expression over class identifiers. 
  For example:

  \begin{isar}
  doc_class article = style_id :: string   <= "''CENELEC_50128''"
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
  \<^emph>\<open>accept-set\<close>) have to appear in the order specified by the regular expression; instances not 
  covered by an accept-set may freely occur. Monitors may additionally contain a reject-clause 
  with a list of class-ids (the reject-list). This allows specifying ranges of
  admissible instances along the class hierarchy:
  \<^item> a superclass in the reject-list and a subclass in the
    accept-expression forbids instances superior to the subclass, and
  \<^item> a subclass $S$ in the reject-list and a superclass $T$ in the
    accept-list allows instances of superclasses of $T$ to occur freely,
    instances of $T$ to occur in the specified order and forbids
    instances of $S$.
\<close>
text\<open>
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
  Ontological classes as described so far are too liberal in many situations. For example, one 
  would like to express that any instance of a \inlineisar+result+ class finally has a non-empty 
  property list, if its \inlineisar+kind+ is \inlineisar+p$$roof+, or that the \inlineisar+establish+ 
  relation between \inlineisar+claim+ and \inlineisar+result+ is surjective.

  In a high-level syntax, this type of constraints could be expressed, \eg, by:

\begin{isar}
(* 1 *) \<forall> x \<in> result. x@kind = pr$$oof \<leftrightarrow> x@kind \<noteq> []
(* 2 *) \<forall> x \<in> conclusion. \<forall> y \<in> Domain(x@establish)
                  \<rightarrow> \<exists> y \<in> Range(x@establish). (y,z) \<in> x@establish
(* 3 *) \<forall> x \<in> introduction. finite(x@authored_by)
\end{isar}

  where \inlineisar+result+, \inlineisar+conclusion+, and \inlineisar+introduction+ are the set of
  all possible instances of these document classes.  All specified constraints are already checked
  in the IDE of \dof while editing; it is however possible to delay a final error message till the 
  closing of a monitor (see next section). The third constraint enforces that the user sets the 
  \inlineisar+authored_by+ set, otherwise an error will be reported.

  For the moment, there is no high-level syntax for the definition of class invariants. A 
  formulation, in SML, of the first class-invariant in \autoref{sec:class_inv} is straight-forward:

\begin{sml}
fun check_result_inv oid {is_monitor:bool} ctxt =
  let val kind = compute_attr_access ctxt "kind" oid <@>{here} <@>{here}
      val prop = compute_attr_access ctxt "property" oid <@>{here} <@>{here}
      val tS = HOLogic.dest_list prop
  in  case kind_term of
       <@>{term "proof"} => if not(null tS) then true
                          else error("class result invariant violation")
      | _ => false
  end
 val _ = Theory.setup (DOF_core.update_class_invariant
                                "tiny_cert.result" check_result_inv)
\end{sml}

  The \inlinesml{setup}-command (last line) registers the \inlineisar+check_result_inv+ function 
  into the \isadof kernel, which activates any creation or modification of an instance of 
  \inlineisar+result+. We cannot replace \inlineisar+compute_attr_access+ by the corresponding 
  antiquotation \inlineisar+<@>{docitem_value kind::oid}+, since \inlineisar+oid+ is bound to a 
  variable here and can therefore not be statically expanded.
\<close>


section*["document-templates"::technical]\<open>Defining Document Templates\<close>
subsection\<open>The Core Template\<close>

text\<open>
  Document-templates\bindex{document template} define the overall layout (page size, margins, fonts, 
  etc.) of the generated documents and are the the main technical means for implementing layout 
  requirements that are, \eg, required by publishers or standardization bodies.   
  The common structure of an \isadof document template looks as follows: 

\begin{ltx}[escapechar=ë, numbers=left,numberstyle=\tiny,xleftmargin=5mm]
\documentclass{article}        % The LaTeX-class of your template ë\label{lst:dc}ë  
%% The following part is (mostly) required by Isabelle/DOF, do not modify
\usepackage[T1]{fontenc}       % Font encoding
\usepackage[utf8]{inputenc}    % UTF8 support
\usepackage{isabelle}          % Required (by Isabelle)
\usepackage{xcolor}
\usepackage{isabellesym}       % Required (by Isabelle)
\usepackage{amsmath}           % Used by some ontologies  
\usepackage{amssymb}           % Strongly recommended (by Isabelle)  
\bibliographystyle{abbrv}
\IfFileExists{DOF-core.sty}{}{ % Required by Isabelle/DOF
  \PackageError{DOF-core}{Isabelle/DOF not installed. 
    This is a Isabelle_DOF project. The doëëcument preparation requires
    the Isabelle_DOF framework. }{%
    For further help, see 
    ë\url{\dofurl}ë
}
\input{ontologies}             % This will include the document specific 
                               % ontologies from isadof.cfg
\IfFileExists{preamble.tex}    % Include preamble.tex, if it exists.
             {\input{preamble.tex}}{}  
\usepackage{graphicx}          % Required for images. 
\usepackage[caption]{subfig}
\usepackage[size=footnotesize]{caption}
\usepackage{hyperref}          % Required by Isabelle/DOF

%% Begin of template specific configuration ë\label{lst:config-start}ë
\urlstyle{rm}
\isabellestyle{it}     ë\label{lst:config-end}ë

%% Main document, do not modify
\begin{document}
\maketitle
\input{session}
\IfFileExists{root.bib}{\bibliography{root}}{}
\end{document}
\end{ltx}

  If a new layout is already supported by a \LaTeX-class, then developing basic support for it 
  is straight forwards: after reading the authors guidelines of the new template, 
  Developing basic support for a new document template is straight forwards In most cases, it is 
  sufficient to replace the document class in \autoref{lst:dc} of the template and add the 
  \LaTeX-packages that are (strictly) required by the used \LaTeX-setup. In general, we recommend
  to only add \LaTeX-packages that are always necessary fro this particular template, as loading
  packages in the templates minimizes the freedom users have by adapting the \path{preample.tex}.
  Moreover, you might want to add/modify the template specific configuration 
  (\autoref{lst:config-start}-\ref{lst:config-end}). The new template should be stored in 
  \path{src/document-templates} and its file name should start with the prefix \path{root-}. After
  adding a new template, call the \inlinebash{install} script (see @{docref "infrastructure"}
\<close>

subsection\<open>Tips, Tricks, and Known Limitations\<close>
text\<open>
  For readers with basic knowledge of \LaTeX{}, adapting existing templates and ontologies) to 
  support new layouts should be rather straight forward, there are several things to consider that 
  we discuss in this section.
\<close>

subsubsection\<open>Getting Started\<close>
text\<open>
  In general, we recommend to create a test project (\eg, using \inlinebash|isabelle mkroot_DOF|)
  to develop new document templates or ontology representations. The default setup of the \isadof
  build system generated a \path{output/document} directory with a self-contained \LaTeX-setup. In 
  this directory, you can directly use \LaTeX on the main file, called \path{root.tex}:

\begin{bash}
ë\prompt{MyProject/output/document}ë pdflatex root.tex
\end{bash}

  This allows you to develop and check your \LaTeX-setup without the overhead of running 
  \inlinebash|isabelle build| after each change of your template (or ontology-style). Note that 
  the content of the \path{output} directory is overwritten by executing 
  \inlinebash|isabelle build|.
\<close>

subsubsection\<open>Truncated Warning and Error Messages\<close>
text\<open>
  By default, \LaTeX{} cuts of many warning or error messages after 79 characters. Due to the 
  use of full-qualified names in \isadof, this can often result in important information being 
  cut off. Thus, it can be very helpful to configure \LaTeX{} in such a way that it prints 
  long error or warning messages. This can easily be done on the command line for individual 
  \LaTeX{} invocations: 

\begin{bash}
ë\prompt{MyProject/output/document}ë max_print_line=200 error_line=200 half_error_line=100  pdflatex root.tex
\end{bash}
\<close>

subsubsection\<open>Deferred Declaration of Information\<close>
text\<open>
  During document generation, sometimes, information needs to be printed prior to its 
  declaration in a \isadof theory. This violation the declaration-before-use-principle
  requires that information is written into an auxiliary file during the first run of \LaTeX{}
  so that the information is available at further runs of \LaTeX{}. While, on the one hand, 
  this is a standard process (\eg, used for updating references), implementing it correctly
  requires a solid understanding of \LaTeX's expansion mechanism. In this context, the recently 
  introduced \inlineltx|\expanded{}|-primitive 
  (see \url{https://www.texdev.net/2018/12/06/a-new-primitive-expanded}) is particularly useful. 
  Examples of its use can be found, \eg, in the ontology-styles 
  \path{ontologies/scholarly_paper/DOF-scholarly_paper.sty} or 
  \path{ontologies/CENELEC_50128/DOF-CENELEC_50128.sty}.  For details about the expansion mechanism 
  in general, we refer the reader to the \LaTeX{} literature (\eg,~@{cite "knuth:texbook:1986"
  and "mittelbach.ea:latex:1999" and "eijkhout:latex-cs:2012"}).  
\<close>


subsubsection\<open>Authors and Affiliation Information\<close>
text\<open>
  In the context of academic papers, the defining the representations for the author and
  affiliation information is particularly challenges as, firstly, they inherently are breaking
  the declare-before-use-principle and, secondly, each publisher uses a different \LaTeX-setup 
  for their declaration. Moreover, the mapping from the ontological modeling to the document
  representation might also need to bridge the gap between different common modeling styles of 
  authors and their affiliations, namely: affiliations as attributes of authors vs. authors and 
  affiliations both as entities with a many-to-many relationship.

  The ontology representation
  \path{ontologies/scholarly_paper/DOF-scholarly_paper.sty} contains an example that, firstly, 
  shows how to write the author and affiliation information into the auxiliary file for re-use 
  in the next \LaTeX-run and, secondly, shows how to collect the author and affiliation 
  information into an \inlineltx|\author| and a \inlineltx|\institution| statement, each of 
  which containing the information for all authors. The collection of the author information 
  is provided by the following \LaTeX-code:

\begin{ltx}
\def\dof@author{}%
\newcommand{\DOFauthor}{\author{\dof@author}}
\AtBeginDocument{\DOFauthor}
\def\leftadd#1#2{\expandafter\leftaddaux\expandafter{#1}{#2}{#1}}
\def\leftaddaux#1#2#3{\gdef#3{#1#2}}
\newcounter{dof@cnt@author}
\newcommand{\addauthor}[1]{%
  \ifthenelse{\equal{\dof@author}{}}{%
    \gdef\dof@author{#1}%
  }{%
    \leftadd\dof@author{\protect\and #1}%
  }
}
\end{ltx}

The new command \inlineltx|\addauthor| and a similarly defined command \inlineltx|\addaffiliation|
can now be used in the definition of the representation of the concept 
\inlineisar|text.scholarly_paper.author|, which writes the collected information in the 
job's aux-file. The intermediate step of writing this information into the job's aux-file is necessary,
as the author and affiliation information is required right at the begin of the document 
(\ie, when \LaTeX's \inlineltx|\maketitle| is invoked) while  \isadof allows to define authors at 
any place within a document:

\begin{ltx}
\provideisadof{text.scholarly_paper.author}%
[label=,type=%
,scholarly_paper.author.email=%
,scholarly_paper.author.affiliation=%
,scholarly_paper.author.orcid=%
,scholarly_paper.author.http_site=%
][1]{%
  \stepcounter{dof@cnt@author}
  \def\dof@a{\commandkey{scholarly_paper.author.affiliation}}
  \ifthenelse{\equal{\commandkey{scholarly_paper.author.orcid}}{}}{%
    \immediate\write\@auxout%
       {\noexpand\addauthor{#1\noexpand\inst{\thedof@cnt@author}}}%
  }{%
    \immediate\write\@auxout%
        {\noexpand\addauthor{#1\noexpand%
            \inst{\thedof@cnt@author}%
                 \orcidID{\commandkey{scholarly_paper.author.orcid}}}}%
  }
  \protected@write\@auxout{}{%
               \string\addaffiliation{\dof@a\\\string\email{%
                    \commandkey{scholarly_paper.author.email}}}}%
}
\end{ltx}

Finally, the collected information is used in the  \inlineltx|\author| command using the 
\inlineltx|AtBeginDocument|-hook:

\begin{ltx}
\newcommand{\DOFauthor}{\author{\dof@author}}
\AtBeginDocument{%
  \DOFauthor
}

\end{ltx}


\<close>

subsubsection\<open>Restricting the Use of Ontologies to Specific Templates\<close>

text\<open>
  As ontology representations might rely on features only provided by certain templates 
  (\LaTeX-classes), authors of ontology representations might restrict their use to 
  specific classes. This can, \eg, be done using the \inlineltx|\@ifclassloaded{}| command:

\begin{ltx}
\@ifclassloaded{llncs}{}%
{% LLNCS class not loaded
    \PackageError{DOF-scholarly_paper}
    {Scholarly Paper only supports LNCS as document class.}{}\stop%
}
\end{ltx}

  For a real-world example testing for multiple classes, see 
  \path{ontologies/scholarly_paper/DOF-scholarly_paper.sty}):

  We encourage this clear and machine-checkable enforcement of restrictions while, at the same
  time, we also encourage to provide a package option to overwrite them. The latter allows 
  inherited ontologies to overwrite these restrictions and, therefore, to provide also support
  for additional document templates. For example, the ontology \inlineisar|technical_report| 
  extends the \inlineisar|scholarly_paper| ontology and its \LaTeX supports provides support
  for the \inlineltx|scrrept|-class which is not supported by the \LaTeX support for 
  \inlineisar|scholarly_paper|.
\<close>

subsubsection\<open>Outdated Version of \path{comment.sty}\<close>
text\<open>
  Isabelle's \LaTeX-setup relies on an ancient version of \path{comment.sty} that, moreover, 
  is used in plain\TeX-mode. This is known to cause issues with some modern \LaTeX-classes
  such as LPICS. Such a conflict might require the help of an Isabelle wizard.
\<close>






(*<*)
end
(*>*) 
  
