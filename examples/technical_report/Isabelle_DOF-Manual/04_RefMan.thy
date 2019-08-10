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
  Document-templates define the overall layout (page size, margins, fonts, etc.) of the generated 
  documents and are the the main technical means for implementing layout requirements that are, \eg,
  required by publishers or standardization bodies. Document-templates are stored in a directory 
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
  syntax and semantics of the specification constructs that are most likely relevant for
  the developer of ontologies (for more details, see~@{cite "isaisarrefman19" and "datarefman19" 
  and "functions19"}. Our presentation is a simplification of the original sources following the 
  needs of ontology developers in \isadof:
  \<^item> \<open>name\<close>:\index{name@\<open>name\<close>}
     with the syntactic category of \<open>name\<close>'s we refer to alpha-numerical identifiers 
     (called \<open>short_id\<close>'s in @{cite "isaisarrefman19"}) and identifiers
     in \inlineisar+" ... "+ which might contain certain ``quasi-letters'' such 
     as \inlineisar+_+, \inlineisar+-+, \inlineisar+.+. See~@{cite "isaisarrefman19"} for details.
  \clearpage
  \<^item> \<open>tyargs\<close>:\index{tyargs@\<open>tyargs\<close>} 
     \<^rail>\<open>  typefree | ('(' (typefree * ',') ')')\<close>
     \<open>typefree\<close> denotes fixed type variable(\<open>'a\<close>, \<open>'b\<close>, ...) (see~@{cite "isaisarrefman19"})
  \<^item> \<open>dt_name\<close>:\index{dt\_npurdahame@\<open>dt_name\<close>}
     \<^rail>\<open>  (tyargs?) name (mixfix?)\<close>   
     The syntactic entity \<open>name\<close> denotes an identifier, \<open>mixfix\<close> denotes the usual 
     parenthesized mixfix notation (see @{cite "isaisarrefman19"}).
     The \<open>name\<close>'s referred here are type names such as \<^verbatim>\<open>int\<close>, \<^verbatim>\<open>string\<close>, \<^verbatim>\<open>list\<close>, \<^verbatim>\<open>set\<close>, etc. 
  \<^item> \<open>type_spec\<close>:\index{type_spec@\<open>type_spec\<close>}
     \<^rail>\<open>  (tyargs?) name\<close>
     The \<open>name\<close>'s referred here are type names such as \<^verbatim>\<open>int\<close>, \<^verbatim>\<open>string\<close>, \<^verbatim>\<open>list\<close>, \<^verbatim>\<open>set\<close>, etc. 
  \<^item> \<open>type\<close>:\index{type@\<open>type\<close>}
     \<^rail>\<open>  (( '(' ( type * ',')  ')' )? name) | typefree \<close>     
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
  Advanced ontology might make use of concepts such as recursive function definitions with 
  pattern-matching~@{cite "functions19"}, extensible record 
  pecifications~@{cite "isaisarrefman19"}, and abstract type declarations.
\<close>


subsection*["odl-manual1"::technical]\<open>Defining Document Classes\<close>
text\<open>
A document class\bindex{document class} can be defined using the @{command "doc_class"} keyword: 
\<^item> \<open>class_id\<close>:\index{class\_id@\<open>class_id\<close>} a type-\<open>name\<close> that has been introduced 
  via a \<open>doc_class_specification\<close>.
\<^item> \<open>doc_class_specification\<close>:\index{doc\_class\_specification@\<open>doc_class_specification\<close>} 
     \<^rail>\<open> @@{command "doc_class"} class_id '=' (class_id '+')? (attribute_decl+) \<newline>
           (accepts_clause rejects_clause?)?\<close>
     Document classes whose specification contains an \<open>accepts_clause\<close> are called 
     \<^emph>\<open>monitor classes\<close> or \<^emph>\<open>monitors\<close> for short. 
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
     regular expressions describe sequences of \<open>class_id\<close>s (and indirect sequences of document
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
\<close>

subsubsection\<open>Example\<close>
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

  As this definition is part of the theory \inlineisar|CENELEC_50128|, the full-quallified
  name of the document class is \inlineisar|t$$ext.CENELEC_50128.EC| and, \eg, the full-qualified
  name of the attribute \inlineisar|long_name|, inherited from the document class 
  \inlineisar|requirement|, is \inlineisar|CENELEC_50128.requirement.long_name|. 

  Let us assume that we want to register the ECs in a dedicated table of contents (\inlineltx{tos}) 
  and use an earlier defined environment \inlineltx|\begin{EC}...\end{EC}| for the graphical 
  representation. We can implement this the corresponding document representation in 
  \path{ontologies/CENELEC_50128/DOF-CENELEC_50128.sty} as follows:

\begin{ltx}
\newisadof{text.CENELEC_50128.EC}%
[label=,type=%
,Isa_COL.text_element.level=%
,Isa_COL.text_element.referentiable=%
,Isa_COL.text_element.variants=%
,CENELEC_50128.requirement.is_concerned=%
,CENELEC_50128.requirement.long_name=%
,CENELEC_50128.EC.assumption_kind=%
][1]{%
\begin{isamarkuptext}%
   \ifthenelse{\equal{\commandkey{CENELEC_50128.requirement.long_name}}{}}{%
      % If long_name is not defined, we only create an entry in the table tos
      % using the auto-generated number of the EC 
      \begin{EC}%
          \addxcontentsline{tos}{chapter}[]{\autoref{\commandkey{label}}}%
    }{%
      % If long_name is defined, we use the long_name as title in the 
      % layout of the EC. Moreover, we use the long_name in the table tos
      % and also automatically generate an index entry for the EC.
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

  While, in principle, any \LaTeX-commands can be used within the \inlineltx|\newisadof|-command,
  one has to take special care for arguments containing special characters (\eg, the 
  underscore ``\_'') that do not have a special meaning in Isabelle but are commands in \LaTeX. 
  Moreover, as usual, special care has to be taken for commands that write into aux-files
  that are included in a following \LaTeX-run. For such complex examples, we refer the interested 
  reader, in general, to  the style files provided in the \isadof distribution. In particular 
  the definitions of the concepts \inlineisar|title*| and \inlineisar|author*| in the file 
  \path{ontologies/scholarly_paper/DOF-scholarly_paper.sty} show examples of protecting special 
  characters in definitions that need to make use of a entries in an aux-file. 
\<close>



subsection*["text-elements"::technical]\<open>Annotatable Top-level Text-Elements\<close>
text\<open>
  While the default user interface for class definitions via the  
  \inlineisar|text*\<Open> ... \<Close>|-command allow to access all features of the document 
  class, \isadof provides short-hands for certain, widely-used, concepts such as 
  \inlineisar|title*\<Open> ... \<Close>| or \inlineisar|section*\<Open> ... \<Close>|.

  \clearpage

  The syntax of top-level \isadof text commands reads as follows:
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


subsubsection\<open>Experts: Defining new top-level commands\<close>

text\<open>
  Defining such new top-level commands requires some Isabelle knowledge as well as 
  extending the dispatcher of the \LaTeX-backend. For the details of defining top-level 
  commands, we refer the reader to the Isar manual~@{cite "wenzel:isabelle-isar:2017"}. 
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

text\<open>To express the dependencies between text elements to the formal
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
  \inlineisar+<@>{definition <string>}+. For the latter, the argument string
  must be checked that it  represents a reference to a text-element
  having the type \inlineisar+definition+ according to the ontology in example ... .\<close>


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
The \inlinesml{setup}-command (last line) registers the
\inlineisar+check_result_inv+ function into the \isadof kernel, which
activates any creation or modification of an instance of
\inlineisar+result+.  We cannot replace \inlineisar+compute_attr_access+
by the corresponding antiquotation
\inlineisar+<@>{docitem_value kind::oid}+, since \inlineisar+oid+ is
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




subsection*["commonlib"::technical]\<open>Common Ontology Library (COL)\<close>
text\<open> The COL library is used to capture a couple of text-elements
that are expected to be common to all document types, a class
that is actually not easy to define. After a lot of thought, we excluded
things like @{command "title*"} and abstract-related classes back again
to specific ontologies, for example.
  
Finally, it is currently reduced to 
\<^enum> the common infra-structure on text-elements (section is a text-element of a certain "level"),
\<^enum> common infrastructure to semi-formal Isabelle elements (Definitions, Assertions, Proofs), and
\<^enum> the common infra-structure for figures.

Future extensions might include, for example, the infra-structure for tables.
\<close>

text\<open> The super-class \<^verbatim>\<open>text_element\<close> is the root of all text-elements used in \isadof.
It is defined as follows:
\begin{isar}
doc_class text_element = 
   level         :: "int  option"    <=  "None" 
   referentiable :: bool <= "False"
   variants      :: "String.literal set" <= "{STR ''outline'', STR ''document''}" 
\end{isar}
Of major importance is the @{term "level"} which influences, inspired by a LaTeX convention,
the following classification:
\<^enum>             part          = Some -1
\<^enum>             chapter       = Some 0
\<^enum>             section       = Some 1
\<^enum>             subsection    = Some 2
\<^enum>             subsubsection = Some 3
\<^enum>             ... 
for scholarly paper: invariant level > 

The attribute @{term "level"} in the subsequent enables doc-notation --- a kind of macro --- 
for support of @{command "chapter*"}, @{command "section*"} etc. This class definition forms 
for a number of invariants; for example, the derived ontology \<open>scholarly_paper\<close> contains an 
invariant that any sequence of, for example, \<open>technical\<close> - elements must be introduced
by a text-element with a higher level, \ie{}, must contain a section or subsection header. 
\<close>


section\<open>Example\<close>
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
\begin{figure}
\begin{isar}
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

\caption{An example ontology modeling simple certification documents, including 
  scientific papers such as~@{cite "brucker.ea:isabelle-ontologies:2018"}; also 
  recall \autoref{fig:dof-ide}.}\label{lst:doc}
\end{figure}
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
  We define the water level <@>{term "level"} of a system state
  <@>{term "\<sigma>"} of the steam boiler as follows: 
\<Close>
definition level :: "state \<rightarrow> real" where
          "level \<sigma> =  level0 + ..." 
update_instance*[d1::definition,
                 property += "[<@>{term ''level \<sigma> =  level0 + ...''}]"]

text*[only::result,evidence="proof"]\<Open>
  The water level is never lower than <@>{term "level0"}:
\<Close>
theorem level_always_above_level_0: "\<forall> \<sigma>. level \<sigma> \<geq> level0"
  unfolding level_def
  by auto
update_instance*[only::result,
                 property += "[<@>{thm ''level_always_above_level_0''}]"]
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



section*["document-templates"::technical]\<open>Defining Document Templates\<close>

text\<open>Current \isadof comes with a number of setups for the PDF generation, notably
Springer LNCS, lipics, ..., as well as setupqs of technical reports this the present one.

The question arises, what to do if \isadof has to be accoustomed to a new LaTeX style
file configuration in order to generate PDF.
\<close>
text\<open> 
In theory, this is simple - in practice, the efforts required
depends mostly on two factors:

\<^item> how compatible is the required LaTeX class with Isabelle's LateX 
 setup in general (e.g., does it work with an antique version 
 of \<open>comment.sty\<close> required by Isabelle)

\<^item>  how much magic does the required LaTeX class wrt the title page
 information (author, affiliation). 

\<^item>  which ontologies should be supported. While most ontologies are 
 generic, some only support a very specific subset of LaTeX 
 templates (classes).  For example, \<^theory_text>\<open>scholarly_paper\<close> does currently 
 \<^emph>\<open>only\<close> support \<open>llncs\<close>, \<open>rartcl\<close>, and \<open>lipics\<close>. 

The general process as such is straight-forward:

\<^enum> From the supported LaTeX classes, try to find the one that is 
  most similar to the one that you want to support. For the sake
  of the this example, let's assume this is llncs
\<^enum> Use the template for this class (llncs) as starting point, i.e.,
  \<^verbatim>\<open>cp document-generator/document-template/root-lncs.tex 
   document-generator/document-template/root-eptcs.tex\<close>

  The mandatory naming scheme for the templates is 

      \<^verbatim>\<open>root-<TEMPLATE_NAME>.tex\<close>

  That is to say that \<^verbatim>\<open><TEMPLATE_NAME>\<close> should be the name of the
  new LaTeX class (all lowercase preferred) that will be used
  in config files and also will be shown in the help text
  shown by executing 

      \<^verbatim>\<open>isabelle mkroot_DOF -h\<close>

\<^enum> Edit the new template as necessary (using the provided 
  example from the target class as reference):

     \<^verbatim>\<open>vim document-generator/document-template/root-foo.tex\<close>

  and do the needful.

\<^enum> Install the new template:

     \<^verbatim>\<open>./install\<close>

  (If you have a working installation of the required AFP entries
   and the Isabelle/DOF patch, you can use \<^verbatim>\<open>./install -s\<close>
   which will \<^emph>\<open>ONLY\<close> install the \<^verbatim>\<open>LaTeX styles/templates\<close>, see 
   \<^verbatim>\<open>./install -h)\<close>

\<^enum> Now the new template should be available, you can check this  with 
 
     \<^verbatim>\<open>isabelle mkroot_DOF -h\<close>

\<^enum> Create an "tiny/empty" Isabelle project using the ontology "core"
  and test your template. If everything works, celebrate. If it does 
  not work, understand what you need to change and continue 
  with step 3. 

  (of course, if the new class is not available in TeXLive, you need
  to add them locally to the documents folder of your Isabelle 
  project and, as usual, it needs to be registered in your ROOTS
  file)

\<^enum> If the ontologies that should be used together with this LaTeX
  class do not require specific adaptions (e.g., CENELEC 50128), 
  everything should work. If one of the required ontology LaTeX
  setups only supports a subset of LaTeX classes (e.g., \<^theory_text>\<open>scholarly_paper\<close> 
  due to the different setups for authors/affiliations blurb), 
  you need to develop support for you new class in the ontology 
  specific LaTeX styles, e.g., 
  \<open>document-generator/latex/DOF-scholarly_paper.sty\<close>
  (mandatory naming convention: \<open>DOF-<ONTOLOGY_NAME>.sty\<close>)

\<^enum> After updating the ontology style (or styles), you need 
  to install them (again, you might want to use ./install -s)
  and test your setup with a paper configuration using 
  your new LaTeX template and the required styles. In case
  of errors, go back to step 7.

\begin{ltx}
\documentclass{article}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage{isabelle}
\usepackage{xcolor}
\usepackage{isabellesym}
\usepackage{amsmath}
\usepackage{amssymb}
\IfFileExists{DOF-core.sty}{}{%
  \PackageError{DOF-core}{Isabelle/DOF not installed. 
    This is a Isabelle_DOF project. The document preparation requires
    the Isabelle_DOF framework. Please obtain the framework by cloning
    the Isabelle_DOF git repository, i.e.: 
         "git clone https://git.logicalhacking.com/Isabelle_DOF/Isabelle_DOF"
    You can install the framework as follows:
         "cd Isabelle_DOF/document-generator && ./install"}{%
    For further help, see 
    https://git.logicalhacking.com/Isabelle_DOF/Isabelle_DOF}
}
\input{ontologies}
\IfFileExists{preamble.tex}{\input{preamble.tex}}{}%
\usepackage{graphicx}
\usepackage{hyperref}
\urlstyle{rm}
\isabellestyle{it}
\usepackage[caption]{subfig}
\usepackage[size=footnotesize]{caption}

\begin{document}
\maketitle
\input{session}
% optional bibliography
\IfFileExists{root.bib}{%
  \bibliographystyle{abbrv}
  \bibliography{root}
}{}
\end{document}
\end{ltx}
\<close>






(*<*)
end
(*>*) 
  
