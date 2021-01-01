(*************************************************************************
 * Copyright (C) 
 *               2019-2020 University of Exeter 
 *               2018-2020 University of Paris-Saclay
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
  "04_RefMan"
  imports 
    "03_GuidedTour" 
    "Isabelle_DOF.Isa_COL"
begin

declare_reference*[infrastructure::technical]

(*>*)

chapter*[isadof_ontologies::technical]\<open>Ontologies and their Development\<close>

text\<open>
  In this chapter, we explain the concepts of \<^isadof> in a more systematic way, and give
  guidelines for modeling new ontologies, present underlying concepts for a mapping to a
  representation, and give hints for the development of new document templates. 

  \<^isadof> is embedded in the underlying generic document model of Isabelle as described in
  \<^introduction>\<open>dof\<close>. Recall that the document language can be extended dynamically, \<^ie>, new
  \<open>user-defined\<close> can be introduced at run-time.  This is similar to the definition of new functions 
  in an interpreter. \<^isadof> as a system plugin provides a number of new command definitions in 
  Isabelle's document model.

  \<^isadof> consists consists basically of five components:
  \<^item> the \<^emph>\<open>DOF-core\<close> providing the \<^emph>\<open>ontology definition language\<close> (called ODL) 
    which allow for the definitions of document-classes and necessary auxiliary datatypes,
  \<^item> the \<^emph>\<open>DOF-core\<close> also provides an own \<^emph>\<open>family of commands\<close> such as 
    \<^boxed_theory_text>\<open>text*\<close>, \<^boxed_theory_text>\<open>declare_reference*\<close>, \<^etc>.;
    They allow for the  annotation of text-elements with meta-information defined in ODL,
  \<^item> the \<^isadof> library of ontologies providing ontological concepts as well
    as supporting infrastructure, 
  \<^item> an infrastructure for ontology-specific \<^emph>\<open>layout definitions\<close>, exploiting this meta-information, 
    and 
  \<^item> an infrastructure for generic \<^emph>\<open>layout definitions\<close> for documents following, \<^eg>, the format 
    guidelines of publishers or standardization bodies. 
\<close>
text\<open>
  Similarly to Isabelle, which is based on a core logic \<^theory>\<open>Pure\<close> and then extended by libraries
  to major systems like \<^verbatim>\<open>HOL\<close> or \<^verbatim>\<open>FOL\<close>, \<^isadof> has a generic core infrastructure \<^dof> and then
  presents itself to users via major library extensions,  which add domain-specific 
  system-extensions. Consequently, ontologies in \<^isadof> are not just a sequence of descriptions in 
  \<^isadof>'s Ontology Definition Language (ODL). Rather, they are themselves presented as integrated 
  sources that provide textual decriptions, abbreviations, macro-support and even ML-code. 
  Conceptually, the library of \<^isadof> is currently organized as follows
  \<^footnote>\<open>Note that the \<^emph>\<open>technical\<close> organisation is slightly different and shown in 
  @{technical (unchecked) \<open>infrastructure\<close>}.\<close>: 
%
\begin{center}
\begin{minipage}{.9\textwidth}
\dirtree{%
.1 COL\DTcomment{The Common Ontology Library}.
.2 scholarly\_paper\DTcomment{Scientific Papers}.
.3 technical\_report\DTcomment{Extended Papers}.
.4 CENELEC\_50128\DTcomment{Papers according to CENELEC\_50128}.
.4 CC\_v3\_1\_R5\DTcomment{Papers according to Common Criteria}. 
.4 \ldots.
}
\end{minipage}
\end{center}

 These libraries not only provide ontological concepts, but also syntactic sugar in Isabelle's
 command language Isar that is of major importance for users (and may be felt as \<^isadof> key 
 features by many authors). In reality, 
 they are derived concepts from more generic ones; for example, the commands
 \<^boxed_theory_text>\<open>title*\<close>, \<^boxed_theory_text>\<open>section*\<close>,  \<^boxed_theory_text>\<open>subsection*\<close>, \<^etc>,
 are in reality a kind of macros for \<^boxed_theory_text>\<open>text*[<label>::title]...\<close>,
 \<^boxed_theory_text>\<open>text*[<label>::section]...\<close>, respectively.
 These example commands are defined in the COL.

 As mentioned earlier, our ontology framework is currently particularly geared towards 
 \<^emph>\<open>document\<close> editing, structuring and presentation (future applications might be advanced
 "knowledge-based" search procedures as well as tool interaction). For this reason, ontologies
 are coupled with \<^emph>\<open>layout definitions\<close> allowing an automatic mapping of an integrated
 source into \<^LaTeX> and finally \<^pdf>. The mapping of an ontology to a specific representation
 in \<^LaTeX> is steered via associated  \<^LaTeX> stylefiles which were included during Isabelle's
 document generation process. This mapping is potentially a one-to-many mapping;
 this implies a certain technical  organisation and some resulting restrictions 
 described in @{technical (unchecked) \<open>infrastructure\<close>} in more detail.
\<close>

section\<open>The Ontology Definition Language (ODL)\<close>
text\<open>
  ODL shares some similarities with meta-modeling languages such as UML class 
  models: It builds upon concepts like class, inheritance, class-instances, attributes, references 
  to instances, and class-invariants. Some concepts like  advanced type-checking, referencing to 
  formal entities of Isabelle, and monitors are due to its specific application in the 
  Isabelle context. Conceptually, ontologies specified in ODL consist of:
  \<^item> \<^emph>\<open>document classes\<close> (\<^boxed_theory_text>\<open>doc_class\<close>) that describe concepts;
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
  The \<^isadof> ontology specification language consists basically on a notation for document classes, 
  where the attributes were typed with HOL-types and can be instantiated by terms HOL-terms, \<^ie>, 
  the actual parsers and type-checkers of the Isabelle system were reused. This has the particular 
  advantage that \<^isadof> commands can be arbitrarily mixed with Isabelle/HOL commands providing the 
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
  document specification language support built-in types for Isabelle/HOL \<^boxed_theory_text>\<open>typ\<close>'s,  
  \<^boxed_theory_text>\<open>term\<close>'s, and \<^boxed_theory_text>\<open>thm\<close>'s reflecting internal Isabelle's  internal 
  types for these entities; when denoted in HOL-terms to instantiate an attribute, for example, 
  there is a  specific syntax (called \<^emph>\<open>inner syntax antiquotations\<close>) that is checked by 
  \<^isadof> for consistency.

  Document classes\<^bindex>\<open>document class\<close>\<^index>\<open>class!document@see document class\<close> support 
  \<^boxed_theory_text>\<open>where\<close>-clauses\<^index>\<open>where clause\<close> containing a regular expression over class 
  names. Classes with a \<^boxed_theory_text>\<open>where\<close> were called 
  \<^emph>\<open>monitor classes\<close>.\<^bindex>\<open>monitor class\<close>\<^index>\<open>class!monitor@see monitor class\<close> While document 
  classes and their inheritance relation structure meta-data of text-elements in an object-oriented 
  manner, monitor classes enforce structural organization of documents via the language specified 
  by the regular expression enforcing a sequence of text-elements.

  A major design decision of ODL is to denote attribute values by HOL-terms and HOL-types. 
  Consequently, ODL can refer to any predefined type defined in the HOL library, \<^eg>, 
  \<^boxed_theory_text>\<open>string\<close> or \<^boxed_theory_text>\<open>int\<close> as well as parameterized types, \<^eg>,
  \<^boxed_theory_text>\<open>_ option\<close>, \<^boxed_theory_text>\<open>_ list\<close>, \<^boxed_theory_text>\<open>_ set\<close>, or products
  \<^boxed_theory_text>\<open>_ \<times> _\<close>. As a consequence of the 
  document model, ODL definitions may be arbitrarily intertwined with standard HOL type definitions. 
  Finally, document class definitions result in themselves in a HOL-types in order to allow \<^emph>\<open>links\<close> 
  to and between ontological concepts.
\<close>

subsection*["odl-manual0"::technical]\<open>Some Isabelle/HOL Specification Constructs Revisited\<close>
text\<open>
  As ODL is an extension of Isabelle/HOL, document class definitions can therefore be arbitrarily 
  mixed with standard HOL specification constructs. To make this manual self-contained, we present 
  syntax and semantics of the specification constructs that are most likely relevant for the 
  developer of ontologies (for more details, see~@{cite "wenzel:isabelle-isar:2020"}.  Our 
  presentation is a simplification of the original sources following the needs of ontology developers 
  in \<^isadof>:
  \<^item> \<open>name\<close>:\<^index>\<open>name@\<open>name\<close>\<close>
     with the syntactic category of \<open>name\<close>'s we refer to alpha-numerical identifiers 
     (called \<open>short_id\<close>'s in @{cite "wenzel:isabelle-isar:2020"}) and identifiers
     in \<^boxed_theory_text>\<open> ... \<close> which might contain certain ``quasi-letters'' such 
     as \<^boxed_theory_text>\<open>_\<close>, \<^boxed_theory_text>\<open>-\<close>, \<^boxed_theory_text>\<open>.\<close> (see~@{cite "wenzel:isabelle-isar:2020"} for 
     details).
  \<^item> \<open>tyargs\<close>:\<^index>\<open>tyargs@\<open>tyargs\<close>\<close> 
     \<^rail>\<open>  typefree | ('(' (typefree * ',') ')')\<close>
     \<open>typefree\<close> denotes fixed type variable(\<open>'a\<close>, \<open>'b\<close>, ...) (see~@{cite "wenzel:isabelle-isar:2020"})
  \<^item> \<open>dt_name\<close>:\<^index>\<open>dt\_npurdahame@\<open>dt_name\<close>\<close>
     \<^rail>\<open>  (tyargs?) name (mixfix?)\<close>   
     The syntactic entity \<open>name\<close> denotes an identifier, \<open>mixfix\<close> denotes the usual 
     parenthesized mixfix notation (see @{cite "wenzel:isabelle-isar:2020"}).
     The \<open>name\<close>'s referred here are type names such as \<^verbatim>\<open>int\<close>, \<^verbatim>\<open>string\<close>, \<^verbatim>\<open>list\<close>, \<^verbatim>\<open>set\<close>, etc. 
  \<^item> \<open>type_spec\<close>:\index{type_spec@\<open>type_spec\<close>}
     \<^rail>\<open>  (tyargs?) name\<close>
     The \<open>name\<close>'s referred here are type names such as \<^verbatim>\<open>int\<close>, \<^verbatim>\<open>string\<close>, \<^verbatim>\<open>list\<close>, \<^verbatim>\<open>set\<close>, etc. 
  \<^item> \<open>type\<close>:\<^index>\<open>type@\<open>type\<close>\<close>
     \<^rail>\<open>  (( '(' ( type * ',')  ')' )? name) | typefree \<close>     
  \<^item> \<open>dt_ctor\<close>:\<^index>\<open>dt\_ctor@\<open>dt_ctor\<close>\<close>
     \<^rail>\<open> name (type*) (mixfix?)\<close>
  \<^item> \<open>datatype_specification\<close>:\<^index>\<open>datatype\_specification@\<open>datatype_specification\<close>\<close>
     \<^rail>\<open> @@{command "datatype"} dt_name '=' (dt_ctor * '|' )\<close>
  \<^item> \<open>type_synonym_specification\<close>:\<^index>\<open>type\_synonym\_specification@\<open>type_synonym_specification\<close>\<close>
     \<^rail>\<open> @@{command "type_synonym"} type_spec '=' type\<close>
  \<^item> \<open>constant_definition\<close> :\<^index>\<open>constant\_definition@\<open>constant_definition\<close>\<close>
     \<^rail>\<open> @@{command "definition"} name '::' type 'where' '"' name '=' \<newline> expr '"'\<close>
  \<^item> \<open>expr\<close>:\<^index>\<open>expr@\<open>expr\<close>\<close>
     the syntactic category \<open>expr\<close> here denotes the very rich ``inner-syntax'' language of 
     mathematical  notations for $\lambda$-terms in Isabelle/HOL. Example expressions are:
     \<^boxed_theory_text>\<open>1+2\<close> (arithmetics), \<^boxed_theory_text>\<open>[1,2,3]\<close> (lists), \<^boxed_theory_text>\<open>ab c\<close> (strings), 
     \<^boxed_theory_text>\<open>{1,2,3}\<close> (sets), \<^boxed_theory_text>\<open>(1,2,3)\<close> (tuples), 
     \<^boxed_theory_text>\<open>\<forall> x. P(x) \<and> Q x = C\<close> (formulas). For details, see~@{cite "nipkow:whats:2020"}.
\<close>

text\<open>
  Advanced ontologies can, \<^eg>,  use recursive function definitions with 
  pattern-matching~@{cite "kraus:defining:2020"}, extensible record 
  specifications~@{cite "wenzel:isabelle-isar:2020"}, and abstract type declarations.
\<close>

text\<open>Note that \<^isadof> works internally with fully qualified names in order to avoid confusions 
occurring otherwise, for example, in disjoint class hierarchies. This also extends to names for
 \<^boxed_theory_text>\<open>doc_class\<close>es, which must be representable as type-names as well since they
can be used in attribute types. Since theory names are lexically very liberal 
(\<^boxed_theory_text>\<open>0.thy\<close> is a legal theory name), this can lead to subtle problems when 
constructing a class: \<^boxed_theory_text>\<open>foo\<close> can be a legal name for a type definition, the 
corresponding type-name \<^boxed_theory_text>\<open>0.foo\<close> is not. For this reason, additional checks at the 
definition of a \<^boxed_theory_text>\<open>doc_class\<close> reject problematic lexical overlaps.\<close>


subsection*["odl-manual1"::technical]\<open>Defining Document Classes\<close>
text\<open>
A document class\<^bindex>\<open>document class\<close> can be defined using the @{command "doc_class"} keyword: 
\<^item> \<open>class_id\<close>:\<^index>\<open>class\_id@\<open>class_id\<close>\<close> a type-\<open>name\<close> that has been introduced 
  via a \<open>doc_class_specification\<close>.
\<^item> \<open>doc_class_specification\<close>:\<^index>\<open>doc\_class\_specification@\<open>doc_class_specification\<close>\<close>
     We call document classes with an \<open>accepts_clause\<close> 
     \<^emph>\<open>monitor classes\<close> or \<^emph>\<open>monitors\<close> for short.
     \<^rail>\<open> @@{command "doc_class"} class_id '=' (class_id '+')? (attribute_decl+) \<newline>
           (invariant_decl*) 
           (accepts_clause rejects_clause?)?\<close>
\<^item> \<open>attribute_decl\<close>:\<^index>\<open>attribute\_decl@\<open>attribute_decl\<close>\<close>
     \<^rail>\<open> name '::' '"' type '"' default_clause? \<close>
\<^item> \<open>invariant_decl\<close>:\<^index>\<open>invariant\_decl@\<open>invariant_decl\<close>\<close>
     An invariants can be specified as predicate over document classes represented as 
     records in HOL. Note that sufficient type information must be provided in order to
     disambiguate the argument of the \<open>\<lambda>\<close>-expression. 
     \<^rail>\<open> 'inv' (name '::')? '"' term '"' \<close>
\<^item> \<open>accepts_clause\<close>:\<^index>\<open>accepts\_clause@\<open>accepts_clause\<close>\<close>
     \<^rail>\<open> 'accepts' '"' regexpr '"'\<close>
\<^item> \<open>rejects_clause\<close>:\<^index>\<open>rejects\_clause@\<open>rejects_clause\<close>\<close>
     \<^rail>\<open> 'rejects' (class_id * ',') \<close>
\<^item> \<open>default_clause\<close>:\<^index>\<open>default\_clause@\<open>default_clause\<close>\<close> 
     \<^rail>\<open> '<=' '"' expr '"' \<close>
\<^item> \<open>regexpr\<close>:\<^index>\<open>regexpr@\<open>regexpr\<close>\<close>
     \<^rail>\<open> '\<lfloor>' class_id '\<rfloor>' | '(' regexpr ')' | (regexpr '||' regexpr) | (regexpr '~~' regexpr)
            | ('\<lbrace>' regexpr '\<rbrace>') | ( '\<lbrace>' regexpr '\<rbrace>\<^sup>*')  \<close>
     Regular expressions describe sequences of \<open>class_id\<close>s (and indirect sequences of document
     items corresponding to the \<open>class_id\<close>s). The constructors for alternative, sequence, 
     repetitions and non-empty sequence follow in the top-down order of the above diagram. 
\<close>

text\<open>
  \<^isadof> provides a default document representation (\<^ie>, content and layout of the generated 
  PDF) that only prints the main text, omitting all attributes. \<^isadof> provides the 
  \inlineltx|\newisadof[]{}|\<^index>\<open>newisadof@\inlineltx{\newisadof}\<close>\<^index>\<open>document class!PDF\<close>
  command for defining a dedicated layout for a document class in \<^LaTeX>. Such a document 
  class-specific \<^LaTeX>-definition can not only provide a specific layout (\<^eg>, a specific 
  highlighting, printing of certain attributes), it can also generate entries in in the table of 
  contents or an index. Overall, the \inlineltx|\newisadof[]{}| command follows the structure
  of the \<^boxed_theory_text>\<open>doc_class\<close>-command:

\begin{ltx}[escapechar=ë]
\newisadof{ë\<open>class_id\<close>ë}[label=,type=, ë\<open>attribute_decl\<close>ë][1]{%
  % ë\LaTeXë-definition of the document class representation
  \begin{isamarkuptext}%
  #1%
  \end{isamarkuptext}%
}
\end{ltx}

  The \<open>class_id\<close> is the full-qualified name of the document class and the list of \<open>attribute_decl\<close>
  needs to declare all attributes of the document class. Within the \<^LaTeX>-definition of the document
  class representation, the identifier \inlineltx|#1| refers to the content of the main text of the 
  document class (written in \<^boxed_theory_text>\<open>\<open> ... \<close>\<close>) and the attributes can be referenced
  by their name using the \inlineltx|\commandkey{...}|-command (see the documentation of the 
  \<^LaTeX>-package ``keycommand''~@{cite "chervet:keycommand:2010"} for details). Usually, the 
  representations definition needs to be wrapped in a 
  \inlineltx|\begin{isarmarkup}...\end{isamarkup}|-environment, to ensure the correct context 
  within Isabelle's \<^LaTeX>-setup. 

  Moreover, \<^isadof> also provides the following two variants of \inlineltx|\newisadof{}[]{}|:
  \<^item>  \inlineltx|\renewisadof{}[]{}|\<^index>\<open>renewisadof@\inlineltx{\renewisadof}\<close> for re-defining 
     (over-writing) an already defined command, and  
  \<^item>  \inlineltx|\provideisadof{}[]{}|\<^index>\<open>provideisadof@\inlineltx{\provideisadof}\<close> for providing 
     a definition if it is not yet defined. 
\<close>
text\<open>
  While arbitrary \<^LaTeX>-commands can be used within these commands,
  special care is required for arguments containing special characters (\<^eg>, the 
  underscore ``\_'') that do have a special meaning in \<^LaTeX>.  
  Moreover, as usual, special care has to be taken for commands that write into aux-files
  that are included in a following \<^LaTeX>-run. For such complex examples, we refer the interested 
  reader, in general, to  the style files provided in the \<^isadof> distribution. In particular 
  the definitions of the concepts \<^boxed_theory_text>\<open>title*\<close> and \<^boxed_theory_text>\<open>author*\<close> in the 
  file \<^file>\<open>../../../src/ontologies/scholarly_paper/DOF-scholarly_paper.sty\<close> show examples of protecting 
  special characters in definitions that need to make use of a entries in an aux-file. 
\<close>

section\<open>Fundamental Commands of the \<^isadof> Core\<close>
text\<open>Besides the core-commands to define an ontology as presented in the previous section, 
the \<^isadof> core provides a number of mechanisms to \<^emph>\<open>use\<close> the resulting data to annotate
text-elements and, in some cases, terms. 
\<close>

subsection\<open>Syntax\<close>
text\<open>In the following, we formally introduce the syntax of the core commands as 
supported on the Isabelle/Isar level. Note that some more advanced functionality of the Core 
is currently only available in the SML API's of the kernel. 

\<^item> \<open>meta_args\<close> : 
   \<^rail>\<open>obj_id ('::' class_id) ((',' attribute '=' term) *) \<close>
\<^item> \<open>upd_meta_args\<close> :
   \<^rail>\<open> (obj_id ('::' class_id) ((',' attribute ('=' | '+=') term) * ))\<close>
\<^item> \<open>annotated_text_element\<close> :
\<^rail>\<open>
    (  @@{command "text*"}'[' meta_args ']' '\<open>' text '\<close>' |
       (  @@{command "open_monitor*"}  
        | @@{command "close_monitor*"} 
        | @@{command "declare_reference*"} 
       ) '[' meta_args ']' 
     ) 
     | change_status_command
     | inspection_command
     | macro_command
  \<close>
\<^item> \<^isadof> \<open>change_status_command\<close> :
  \<^rail>\<open>  (@@{command "update_instance*"} '[' upd_meta_args ']')
       |  (@@{command "declare_reference*"} (obj_id ('::' class_id)))\<close>
\<^item> \<^isadof> \<open>inspection_command\<close> :
  \<^rail>\<open>    @@{command "print_doc_classes"}
        |  @@{command "print_doc_items"} 
        |  @@{command "check_doc_global"}\<close>
\<^item> \<^isadof> \<open>macro_command\<close> :
  \<^rail>\<open>   @@{command "define_shortcut*"} name ('\<rightleftharpoons>' | '==') '\<open>' string '\<close>' 
        |  @@{command "define_macro*"}  name ('\<rightleftharpoons>' | '==') 
           \<newline> '\<open>' string '\<close>' '_' '\<open>' string '\<close>' \<close>
\<close>
text\<open>Recall that with the exception of \<^theory_text>\<open>text* \<dots> \<close>, all \<^isadof> commands were mapped to visible
layout (such as \<^LaTeX>); these commands have to be wrapped into 
 \<^verbatim>\<open>(*<*) ... (*>*)\<close> brackets if this is undesired. \<close>

subsection\<open>Ontologic Text-Elements and their Management\<close>
text\<open> \<^theory_text>\<open>text*[oid::cid, ...] \<open>\<open>\<close> \<dots> text \<dots> \<open>\<close>\<close> \<close> is the core-command of \<^isadof>: it permits to create 
 an object of meta-data belonging to the class \<^theory_text>\<open>cid\<close>. This is viewed as the \<^emph>\<open>definition\<close> of
an instance of a document class. This instance object is attached to the text-element
and makes it thus "trackable" for  \<^isadof>, \<^ie>, it can be referenced via the  \<^theory_text>\<open>oid\<close>, its attributes
can be set by defaults in the class-definitions, or set at creation time, or modified at any
point after creation via  \<^theory_text>\<open>update_instance*[oid, ...]\<close>. The \<^theory_text>\<open>class_id\<close> is syntactically optional;
if ommitted, an object belongs to an anonymous superclass of all classes. 
The \<^theory_text>\<open>class_id\<close> is used to generate a \<^emph>\<open>class-type\<close> in HOL; note that this may impose lexical 
restrictions as well as to name-conflicts in the surrounding logical context. 
In many cases, it is possible to use the class-type to denote the \<^theory_text>\<open>class_id\<close>; this also
holds for type-synonyms on class-types.

References to text-elements can occur textually before creation; in these cases, they must be 
declared via \<^theory_text>\<open>declare_reference*[...]\<close> in order to compromise to Isabelle's fundamental 
"declaration-before-use" linear-visibility evaluation principle. The forward-declared class-type
must be identical with the defined class-type.

For a declared class \<^theory_text>\<open>cid\<close>, there exists a text antiquotation of the form \<^theory_text>\<open> @{cid \<open>oid\<close>} \<close>. 
The precise presentation is decided in the \<^emph>\<open>layout definitions\<close>, for example by suitable
\<^LaTeX>-template code. Declared but not yet defined instances must be referenced with a particular
pragma in order to enforce a relaxed checking \<^theory_text>\<open> @{cid (unchecked) \<open>oid\<close>} \<close>.

% there should also exist a *term* antiquotation ...
\<close>

(*<*)
declare_reference*["sec:advanced"::technical]
(*>*)

subsection\<open>Status and Query Commands\<close>
text\<open>\<^isadof> provides a number of inspection commands.
\<^item> \<^theory_text>\<open>print_doc_classes\<close> allows to view the status of the internal
  class-table resulting from ODL definitions,
\<^item> \<^ML>\<open>DOF_core.print_doc_class_tree\<close> allows for presenting (fragments) of
  class-inheritance trees (currently only available at ML level),
\<^item> \<^theory_text>\<open>print_doc_items\<close> allows  to view the status of the internal
  object-table of text-elements that were tracked, and 
\<^item> \<^theory_text>\<open>check_doc_global\<close> checks if all declared object references have been
  defined, and all monitors are in a final state and final invariant checks 
  on all objects are satisfied (cf. @{technical (unchecked) \<open>sec:advanced\<close>})
\<close>

subsection\<open>Macros\<close>
text\<open>There is a mechanism to define document-local short-cuts and macros which
were PIDE-supported but lead to an expansion in the integrated source; this feature
can be used to define 
\<^item> \<^theory_text>\<open>shortcuts\<close>, \<^ie>, short names that were expanded to, for example,
  \<^LaTeX>-code,
\<^item> \<^theory_text>\<open>macro\<close>'s (= parameterized short-cuts), which allow for 
  passing an argument to the expansion mechanism.
\<close>
text\<open>Note that the argument can be checked by an own SML-function with respect to syntactic
as well as semantic regards; however, the latter feature is currently only accessible at
the SML level and not directly in the Isar language. We would like to stress, that this 
feature is basically an abstract interface to existing Isabelle functionality in the document 
generation.
\<close>
subsubsection\<open>Examples\<close>
text\<open>
\<^item> common short-cut hiding \<^LaTeX> code in the integrated source:
    @{theory_text [display] \<open>
     define_shortcut* eg  \<rightleftharpoons> \<open>\eg\<close>  (* Latin: „exempli gratia“  meaning  „for example“. *)
                      clearpage \<rightleftharpoons> \<open>\clearpage{}\<close>
    \<close>}
\<^item> non-checking macro:
    @{theory_text [display] \<open>
      define_macro* index  \<rightleftharpoons> \<open>\index{\<close> _ \<open>}\<close>
    \<close>}
\<^item> checking macro:
    @{theory_text [display] \<open>
      setup\<open> DOF_lib.define_macro \<^binding>\<open>vs\<close>  "\\vspace{" "}" (check_latex_measure) \<close> 
    \<close>}
  where \<^ML>\<open>check_latex_measure\<close> is a hand-programmed function that checks 
  of the input syntax.
\<close>


section\<open>The Standard Ontology Libraries\<close>
text\<open> We will describe the backbone of the Standard Library with the
already mentioned hierarchy \<^verbatim>\<open>COL\<close> (the common ontology library),
 \<^verbatim>\<open>scholarly_paper\<close> (for MINT-oriented scientific papers), 
 \<^verbatim>\<open>technical_report\<close> (for MINT-oriented technical reports), and
the example for a domain-specific ontology 
\<^verbatim>\<open>CENELEC_50128\<close>.\<close>

subsection\<open>Common Ontology Library (COL)\<close>
(*<*)
ML\<open>writeln (DOF_core.print_doc_class_tree @{context} (fn (n,l) => String.isPrefix "Isa_COL" l) I)\<close>
(*>*)
text\<open> 
 \<^isadof> provides a Common Ontology Library (COL)\<^index>\<open>Common Ontology Library@see COL\<close>
 \<^bindex>\<open>COL\<close> \<^footnote>\<open>contained in \<^theory>\<open>Isabelle_DOF.Isa_COL\<close>\<close>
 that introduces several ontology root concepts such as common text-elements and 
 figures. The overall class-tree it provides looks as follows:
%
\begin{center}
\begin{minipage}{.9\textwidth}
\dirtree{%
.0 .
.1 Isa\_COL.text\_element.
.2 Isa\_COL.chapter.
.2 Isa\_COL.section.
.2 Isa\_COL.subsection.
.2 Isa\_COL.subsubsection.
.1 Isa\_COL.figure.
.2 Isa\_COL.side\_by\_side\_figure.
.1 Isa\_COL.figure\_group.
.1 \ldots.
}
\end{minipage}
\end{center}\<close>

text\<open>
In particular it defines the super-class \<^boxed_theory_text>\<open>text_element\<close>: the root of all 
text-elements,

@{boxed_theory_text [display]\<open>
doc_class text_element = 
   level         :: "int  option"    <=  "None" 
   referentiable :: bool <= "False"
   variants      :: "String.literal set" <= "{STR ''outline'', STR ''document''}" 
\<close>}

As mentioned in @{technical \<open>sss\<close>} (without explaining the origin of \<^typ>\<open>text_element\<close>)
, \<^boxed_theory_text>\<open>level\<close> defines the section-level (\<^eg>, using a \<^LaTeX>-inspired hierarchy:
from \<^boxed_theory_text>\<open>Some -1\<close> (corresponding to \inlineltx|\part|) to 
\<^boxed_theory_text>\<open>Some 0\<close> (corresponding to \inlineltx|\chapter|, respectively, \<^boxed_theory_text>\<open>chapter*\<close>) 
to \<^boxed_theory_text>\<open>Some 3\<close> (corresponding to \inlineltx|\subsubsection|, respectively, 
\<^boxed_theory_text>\<open>subsubsection*\<close>). Using an invariant, a derived ontology could, \<^eg>, require that
any sequence of technical-elements must be introduced by a text-element with a higher level
(this would require that technical text section are introduce by a section element).

The attribute \<^term>\<open>referentiable\<close> captures the information if a text-element can be target
for a reference, which is the case for sections or subsections, for example, but not arbitrary
elements such as, \<^ie>, paragraphs (this mirrors restrictions of the target \<^LaTeX> representation).
The attribute  \<^term>\<open>variants\<close> refers to an Isabelle-configuration attribute that permits
to steer the different versions a \<^LaTeX>-presentation of the integrated source.


For further information of the root classes such as \<^typ>\<open>figure\<close>'s, please consult the ontology 
 \<^theory>\<open>Isabelle_DOF.Isa_COL\<close> directly.

COL finally provides macros that extend the command-language of the DOF-core by the following
abbreviations:

\<^item> \<open>derived_text_element\<close> :
\<^rail>\<open>
    (  ( @@{command "chapter*"} 
       | @@{command "section*"}   | @@{command "subsection*"} | @@{command "subsubsection*"} 
       | @@{command "paragraph*"} | @@{command "subparagraph*"} 
       | @@{command "figure*"}    | @@{command "side_by_side_figure*"} 
       ) 
       \<newline>
       '[' meta_args ']' '\<open>' text '\<close>'
     ) 
  \<close>
\<close>
text\<open> Note that the command syntax follows the implicit convention to add a "*" to 
the command in order to distinguish them from the standard Isabelle text-commands
which are not "ontology-aware" but function similar otherwise.\<close>

subsection*["text-elements"::technical]\<open>The Ontology \<^theory>\<open>Isabelle_DOF.scholarly_paper\<close>\<close>
(*<*)
ML\<open>writeln (DOF_core.print_doc_class_tree @{context} (fn (n,l) => String.isPrefix "scholarly_paper" l) I)\<close>
(*>*)
text\<open>
  While the default user interface for class definitions via the  
  \<^boxed_theory_text>\<open>text*\<open> ... \<close>\<close>-command allow to access all features of the document 
  class, \<^isadof> provides short-hands for certain, widely-used, concepts such as 
  \<^boxed_theory_text>\<open>title*\<open> ... \<close>\<close> or \<^boxed_theory_text>\<open>section*\<open> ... \<close>\<close>, \<^eg>:

@{boxed_theory_text [display]\<open>
 title*[title::title]\<open>Isabelle/DOF\<close>
 subtitle*[subtitle::subtitle]\<open>User and Implementation Manual\<close>
 author*[adb::author, email="\<open>a.brucker@exeter.ac.uk\<close>",
         orcid="\<open>0000-0002-6355-1200\<close>", http_site="\<open>https://brucker.ch/\<close>",
         affiliation="\<open>University of Exeter, Exeter, UK\<close>"] \<open>Achim D. Brucker\<close>
 author*[bu::author, email = "\<open>wolff@lri.fr\<close>",
         affiliation = "\<open>Université Paris-Saclay, LRI, Paris, France\<close>"]\<open>Burkhart Wolff\<close>
\<close>}

In general, all standard text-elements from the Isabelle document model such
as \<^theory_text>\<open>chapter\<close>, \<^theory_text>\<open>section\<close>, \<^theory_text>\<open>text\<close>, have in the \<^isadof>
implementation their counterparts in the family of text-elements that are ontology-aware,
\<^ie>, they dispose on a meta-argument list that allows to define that a test-element
that has an identity as a text-object labelled as \<open>obj_id\<close>, belongs to a document class 
\<open>class_id\<close> that has been defined earlier, and  has its class-attributes set with particular 
values (which are denotable in Isabelle/HOL mathematical term syntax).
\<^item> \<open>annotated_text_element\<close> :
\<^rail>\<open>
    (  ( @@{command "title*"}
       | @@{command "subtitle*"}
       | @@{command "author*"}
       | @@{command "abstract*"})
       \<newline>
       '[' meta_args ']' '\<open>' text '\<close>'
     ) 
  \<close>
\<close>


text\<open>\<^isadof> uses the concept of implicit abstract classes (or: \<^emph>\<open>shadow classes\<close>).
These refer to the set of possible \<^boxed_theory_text>\<open>doc_class\<close> declarations that posses a number
of attributes with their types in common. Shadow classes represent an implicit requirement
(or pre-condition) on a given class to posses these attributes in order to work properly
for certain \<^isadof> commands. 

shadow classes will find concrete instances in COL, but \<^isadof> text elements do not \<^emph>\<open>depend\<close>
on our COL definitions: Ontology developers are free to build own class instances for these 
shadow classes, with own attributes and, last not least, own definitions of invariants independent
from ours.

In particular, these shadow classes are used at present in  \<^isadof>:
@{boxed_theory_text [display]\<open>
DOCUMENT_ALIKES = 
   level         :: "int  option"    <=  "None" 

ASSERTION_ALIKES = 
    properties :: "term list"
  
FORMAL_STATEMENT_ALIKE =
    properties :: "thm list"
\<close>}

These shadow-classes correspond to semantic macros 
 \<^ML>\<open>Onto_Macros.enriched_document_cmd_exp\<close>,
 \<^ML>\<open>Onto_Macros.assertion_cmd'\<close>, and
 \<^ML>\<open>Onto_Macros.enriched_formal_statement_command\<close>.\<close>


text\<open>
Similarly, we provide "minimal" instances of the \<^boxed_theory_text>\<open>ASSERTION_ALIKES\<close>
and \<^boxed_theory_text>\<open>FORMAL_STATEMENT_ALIKE\<close> shadow classes:
@{boxed_theory_text [display]\<open>
doc_class assertions = 
    properties :: "term list"
  
doc_class "thms" =
    properties :: "thm list"
\<close>}
\<close>

subsection\<open>The Ontology \<^theory>\<open>Isabelle_DOF.technical_report\<close>\<close>

subsection\<open>A Domain-Specific Ontology: \<^theory>\<open>Isabelle_DOF.CENELEC_50128\<close>\<close>

subsubsection\<open>Example: Text Elemens with Levels\<close>
text\<open>
The category ``exported constraint (EC)'' is, in the file 
\<^file>\<open>../../../src/ontologies/CENELEC_50128/CENELEC_50128.thy\<close> defined as follows:

@{boxed_theory_text [display]\<open>
doc_class requirement = text_element +
   long_name    :: "string option"
   is_concerned :: "role set"
doc_class AC = requirement +
   is_concerned :: "role set" <= "UNIV"
doc_class EC = AC  +
     assumption_kind :: ass_kind <= (*default *) formal
\<close>}

We now define the document representations, in the file 
\<^file>\<open>../../../src/ontologies/CENELEC_50128/DOF-CENELEC_50128.sty\<close>. Let us assume that we want to 
register the definition of EC's in a dedicated table of contents (\inlineltx{tos}) 
and use an earlier defined environment \inlineltx|\begin{EC}...\end{EC}| for their graphical 
representation. Note that the \inlineltx|\newisadof{}[]{}|-command requires the 
full-qualified names, \<^eg>, \<^boxed_theory_text>\<open>text.CENELEC_50128.EC\<close> for the document class and 
\<^boxed_theory_text>\<open>CENELEC_50128.requirement.long_name\<close> for the  attribute \<^boxed_theory_text>\<open>long_name\<close>, 
inherited from the document class \<^boxed_theory_text>\<open>requirement\<close>. The representation of EC's
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
formal model. For example, assume a definition: \<close>

definition last :: "'a list \<Rightarrow> 'a" where "last S = hd(rev S)"

(* Old stuff using abstract classes.
(*<*)
text*[claim::assertions]\<open>For non-empty lists, our definition yields indeed the last element of a list.\<close>
assert*[claim::assertions] "last[4::int] = 4"
assert*[claim::assertions] "last[1,2,3,4::int] = 4"
(*>*)
*)
text\<open>We want to check the consequences of this definition and can add the following statements:
@{boxed_theory_text [display]\<open>
text*[claim::assertions]\<open>For non-empty lists, our definition yields indeed 
                               the last element of a list.\<close>
assert*[claim1::assertions] "last[4::int] = 4"
assert*[claim2::assertions] "last[1,2,3,4::int] = 4"
\<close>}
\<close>

text\<open>As an \<^boxed_theory_text>\<open>ASSERTION_ALIKES\<close>, the \<^boxed_theory_text>\<open>assertions\<close> class possesses a 
\<^boxed_theory_text>\<open>properties\<close> attribute. The \<^boxed_theory_text>\<open>assert*\<close> command evaluates its argument;
in case it evaluates to true the property is added to the property list of the \<^boxed_theory_text>\<open>claim\<close> - 
text-element. Commands like \<^boxed_theory_text>\<open>Definitions*\<close> or \<^boxed_theory_text>\<open>Theorem*\<close> work analogously.\<close>


subsubsection\<open>For Isabelle Hackers: Defining New Top-Level Commands\<close>

text\<open>
  Defining such new top-level commands requires some Isabelle knowledge as well as 
  extending the dispatcher of the \<^LaTeX>-backend. For the details of defining top-level 
  commands, we refer the reader to the Isar manual~@{cite "wenzel:isabelle-isar:2020"}. 
  Here, we only give a brief example how the \<^boxed_theory_text>\<open>section*\<close>-command is defined; we 
  refer the reader to the source code of \<^isadof> for details.

  First, new top-level keywords need to be declared in the \<^boxed_theory_text>\<open>keywords\<close>-section of 
  the theory header defining new keywords:

@{boxed_theory_text [display]\<open>
theory 
    ...
  imports
    ... 
  keywords
    "section*"
begin 
...
end
\<close>}

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
Finally, for the document generation, a new dispatcher has to be defined in \<^LaTeX>---this is 
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



section*["sec:advanced"::technical]\<open>Advanced ODL Concepts\<close>
subsection\<open>Meta-types as Types\<close>

text\<open>
  To express the dependencies between text elements to the formal
  entities, \<^eg>, \<^ML_type>\<open>term\<close> (\<open>\<lambda>\<close>-term), \<^ML_type>\<open>typ\<close>, or
   \<^ML_type>\<open>thm\<close>, we represent the types of the implementation language
  \<^emph>\<open>inside\<close> the HOL type system.  We do, however, not reflect the data of
  these types. They are just declared abstract types, 
  ``inhabited'' by special constant symbols carrying strings, for
  example of the format \<^boxed_theory_text>\<open>@{thm <string>}\<close>. When HOL
  expressions were used to denote values of \<^boxed_theory_text>\<open>doc_class\<close>
  instance attributes, this requires additional checks after
  conventional type-checking that this string represents actually a
  defined entity in the context of the system state
  \<^boxed_theory_text>\<open>\<theta>\<close>.  For example, the \<^boxed_theory_text>\<open>establish\<close>
  attribute in the previous section is the power of the ODL: here, we model
  a relation between \<^emph>\<open>claims\<close> and \<^emph>\<open>results\<close> which may be a
  formal, machine-check theorem of type \<^ML_type>\<open>thm\<close> denoted by, for
  example: \<^boxed_theory_text>\<open>property = "[@{thm "system_is_safe"}]"\<close> in a
  system context \<^boxed_theory_text>\<open>\<theta>\<close> where this theorem is
  established. Similarly, attribute values like 
  \<^boxed_theory_text>\<open>property = "@{term \<open>A \<leftrightarrow> B\<close>}"\<close>
  require that the HOL-string \<^boxed_theory_text>\<open>A \<leftrightarrow> B\<close> is 
  again type-checked and represents indeed a formula in \<open>\<theta>\<close>. Another instance of 
  this process, which we call \<open>second-level type-checking\<close>, are term-constants
  generated from the ontology such as 
  \<^boxed_theory_text>\<open>@{definition <string>}\<close>. 
\<close>


subsection*["sec:monitors"::technical]\<open>ODL Monitors\<close>
text\<open>
  We call a document class with an accept-clause a \<^emph>\<open>monitor\<close>.\<^bindex>\<open>monitor\<close>  Syntactically, an 
  accept-clause\<^index>\<open>accept-clause\<close> contains a regular expression over class identifiers. 
  For example:

  @{boxed_theory_text [display]\<open>
  doc_class article = style_id :: string   <= "''CENELEC_50128''"
      accepts "(title ~~ \<lbrace>author\<rbrace>\<^sup>+ ~~ abstract ~~ \<lbrace>introduction\<rbrace>\<^sup>+ ~~
               \<lbrace>technical || example\<rbrace>\<^sup>+ ~~ \<lbrace>conclusion\<rbrace>\<^sup>+)"
  \<close>}

  Semantically, monitors introduce a behavioral element into ODL:

  @{boxed_theory_text [display]\<open>
  open_monitor*[this::article]  (* begin of scope of monitor "this" *)
    ...
  close_monitor*[this]          (* end of scope of monitor "this"   *)
  \<close>}

  Inside the scope of a monitor, all instances of classes mentioned in its accept-clause (the
  \<^emph>\<open>accept-set\<close>) have to appear in the order specified by the regular expression; instances not 
  covered by an accept-set may freely occur. Monitors may additionally contain a reject-clause 
  with a list of class-ids (the reject-list). This allows specifying ranges of
  admissible instances along the class hierarchy:
  \<^item> a superclass in the reject-list and a subclass in the
    accept-expression forbids instances superior to the subclass, and
  \<^item> a subclass $S$ in the reject-list and a superclass \<open>T\<close> in the
    accept-list allows instances of superclasses of \<open>T\<close> to occur freely,
    instances of \<open>T\<close> to occur in the specified order and forbids
    instances of \<open>S\<close>.
\<close>
text\<open>
  Monitored document sections can be nested and overlap; thus, it is
  possible to combine the effect of different monitors. For example, it
  would be possible to refine the \<^boxed_theory_text>\<open>example\<close> section by its own
  monitor and enforce a particular structure in the presentation of
  examples.
  
  Monitors manage an implicit attribute \<^boxed_theory_text>\<open>trace\<close> containing
  the list of ``observed'' text element instances belonging to the
  accept-set. Together with the concept of ODL class invariants, it is
  possible to specify properties of a sequence of instances occurring in
  the document section. For example, it is possible to express that in
  the sub-list of \<^boxed_theory_text>\<open>introduction\<close>-elements, the first has an
  \<^boxed_theory_text>\<open>introduction\<close> element with a \<^boxed_theory_text>\<open>level\<close> strictly
  smaller than the others. Thus, an introduction is forced to have a
  header delimiting the borders of its representation. Class invariants
  on monitors allow for specifying structural properties on document
  sections.\<close>


subsection*["sec:class_inv"::technical]\<open>ODL Class Invariants\<close>
text\<open>
  Ontological classes as described so far are too liberal in many situations. For example, one 
  would like to express that any instance of a \<^boxed_theory_text>\<open>result\<close> class finally has a 
  non-empty  property list, if its \<^boxed_theory_text>\<open>kind\<close> is \<^boxed_theory_text>\<open>proof\<close>, or that 
  the \<^boxed_theory_text>\<open>establish\<close> relation between \<^boxed_theory_text>\<open>claim\<close> and
  \<^boxed_theory_text>\<open>result\<close> is surjective.

  In a high-level syntax, this type of constraints could be expressed, \<^eg>, by:

@{boxed_theory_text [display]\<open>
(* 1 *) \<forall> x \<in> result. x@kind = pr$$oof \<leftrightarrow> x@kind \<noteq> []
(* 2 *) \<forall> x \<in> conclusion. \<forall> y \<in> Domain(x@establish)
                  \<rightarrow> \<exists> y \<in> Range(x@establish). (y,z) \<in> x@establish
(* 3 *) \<forall> x \<in> introduction. finite(x@authored_by)
\<close>}

  where \<^boxed_theory_text>\<open>result\<close>, \<^boxed_theory_text>\<open>conclusion\<close>, and \<^boxed_theory_text>\<open>introduction\<close> are the set of
  all possible instances of these document classes.  All specified constraints are already checked
  in the IDE of \<^dof> while editing; it is however possible to delay a final error message till the 
  closing of a monitor (see next section). The third constraint enforces that the user sets the 
  \<^boxed_theory_text>\<open>authored_by\<close> set, otherwise an error will be reported.

  For the moment, there is no high-level syntax for the definition of class invariants. A 
  formulation, in SML, of the first class-invariant in \<^technical>\<open>sec:class_inv\<close> is straight-forward:

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

  The \<^ML>\<open>Theory.setup\<close>-command (last line) registers the \<^boxed_theory_text>\<open>check_result_inv\<close> function 
  into the \<^isadof> kernel, which activates any creation or modification of an instance of 
  \<^boxed_theory_text>\<open>result\<close>. We cannot replace \<^boxed_theory_text>\<open>compute_attr_access\<close> by the 
  corresponding antiquotation \<^boxed_theory_text>\<open>@{docitem_value kind::oid}\<close>, since
  \<^boxed_theory_text>\<open>oid\<close> is bound to a  variable here and can therefore not be statically expanded.
\<close>



section*[infrastructure::technical]\<open>Technical Infrastructure\<close>

text\<open> 
  The list of fully supported (\<^ie>, supporting both interactive ontological modeling and 
  document generation) ontologies and the list of supported document templates can be 
  obtained by calling \inlinebash|isabelle mkroot_DOF -h| (see \<^technical>\<open>first_project\<close>).
  Note that the postfix \inlinebash|-UNSUPPORTED| denotes experimental ontologies or templates 
  for which further manual setup steps might be required or that are not fully tested. Also note 
  that the \<^LaTeX>-class files required by the templates need to be already installed on your 
  system. This is mostly a problem for publisher specific templates (\<^eg>, Springer's 
  \<^path>\<open>llncs.cls\<close>), which cannot be re-distributed due to copyright restrictions.
\<close>

subsection\<open>Developing Ontologies and their Represenation Mappings\<close>
text\<open>
  The document core \<^emph>\<open>may\<close>, but \<^emph>\<open>must\<close> not use Isabelle definitions or proofs for checking the 
  formal content---this manual is actually an example of a document not containing any proof.
  Consequently, the document editing and checking facility provided by \<^isadof> addresses the needs 
  of common users for an advanced text-editing environment, neither modeling nor proof knowledge is 
  inherently required.

  We expect authors of ontologies to have experience in the use of \<^isadof>, basic modeling (and, 
  potentially, some basic SML programming) experience, basic \<^LaTeX> knowledge, and, last but not 
  least, domain knowledge of the ontology to be modeled. Users with experience in UML-like 
  meta-modeling will feel familiar with most concepts; however, we expect  no need for insight in 
  the Isabelle proof language, for example, or other more advanced concepts.

  Technically, ontologies\<^index>\<open>ontology!directory structure\<close> are stored in a directory 
  \inlinebash|src/ontologies| and consist of a Isabelle theory file and a \<^LaTeX> -style file:
%
\begin{center}
\begin{minipage}{.9\textwidth}
\dirtree{%
.1 .
.2 src.
.3 ontologies\DTcomment{Ontologies}.
.4 ontologies.thy\DTcomment{Ontology Registration}.
.4 scholarly\_paper\DTcomment{scholarly\_paper}.
.5 scholarly\_paper.thy.
.5 DOF-scholarly\_paper.sty.
.4 technical\_report\DTcomment{technical\_paper}.
.5 technical\_report.thy.
.5 DOF-technical\_report.sty.
.4 CENELEC\_50128\DTcomment{CENELEC\_50128}.
.5 CENELEC\_50128.thy.
.5 DOF-CENELEC\_50128.sty.
.4 \ldots.
}
\end{minipage}
\end{center}
\<close>
text\<open>
  Developing a new ontology ``\inlinebash|foo|'' requires, from a technical perspective, the 
  following steps:
  \<^item> create a new sub-directory \inlinebash|foo| in the directory \inlinebash|src/ontologies|
  \<^item> definition of the ontological concepts, using \<^isadof>'s Ontology Definition Language (ODL), in 
    a new theory file \<^path>\<open>src/ontologies/foo/foo.thy\<close>.  
  \<^item> definition of the document representation for the ontological concepts in a \LaTeX-style 
    file \<^path>\<open>src/ontologies/foo/DOF-foo.sty\<close>
  \<^item> registration (as import) of the new ontology in the file. 
    \<^path>\<open>src/ontologies/ontologies.thy\<close>. 
  \<^item> activation of the new document setup by executing the install script. You can skip the lengthy 
    checks for the AFP entries and the installation of the Isabelle patch by using the 
    \inlinebash|--skip-patch-and-afp| option:
  
 \begin{bash}
ë\prompt{\isadofdirn}ë ./install --skip-patch-and-afp
 \end{bash}
\<close>

subsection\<open>Document Templates\<close>
text\<open>
  Document-templates\<^index>\<open>document template\<close> define the overall layout (page size, margins, fonts, 
  etc.) of the generated documents and are the the main technical means for implementing layout 
  requirements that are, \<^eg>, required by publishers or standardization bodies. Document-templates 
  are stored in a directory 
  \<^path>\<open>src/document-templates\<close>:\<^index>\<open>document template!directory structure\<close>
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
  \<^item> develop a new \<^LaTeX>-template \inlinebash|src/document-templates/root-bar.tex|
  \<^item> activation of the new document template  by executing the install script. You can skip the lengthy 
    checks for the AFP entries and the installation of the Isabelle patch by using the 
    \inlinebash|--skip-patch-and-afp| option:
  
  \begin{bash}
ë\prompt{\isadofdirn}ë ./install --skip-patch-and-afp
  \end{bash}
\<close>


text\<open>
  As the document generation of \<^isadof> is based 
  on \<^LaTeX>, the \<^isadof> document templates can (and should) make use of any \<^LaTeX>-classes provided
  by publishers or standardization bodies.
\<close>


section*["document-templates"::technical]\<open>Defining Document Templates\<close>
subsection\<open>The Core Template\<close>

text\<open>
  Document-templates\<^bindex>\<open>document template\<close> define the overall layout (page size, margins, fonts, 
  etc.) of the generated documents and are the the main technical means for implementing layout 
  requirements that are, \<^eg>, required by publishers or standardization bodies. 
  If a new layout is already supported by a \<^LaTeX>-class, then developing basic support for it 
  is straight forwards: after reading the authors guidelines of the new template, 
  Developing basic support for a new document template is straight forwards In most cases, it is 
  sufficient to replace the document class in \autoref{lst:dc} of the template and add the 
  \<^LaTeX>-packages that are (strictly) required by the used \<^LaTeX>-setup. In general, we recommend
  to only add \<^LaTeX>-packages that are always necessary fro this particular template, as loading
  packages in the templates minimizes the freedom users have by adapting the \<^path>\<open>preample.tex\<close>.
  Moreover, you might want to add/modify the template specific configuration 
  (\autoref{lst:config-start}-\ref{lst:config-end}). The new template should be stored in 
  \<^path>\<open>src/document-templates\<close> and its file name should start with the prefix \<^path>\<open>root-\<close>. After
  adding a new template, call the \inlinebash{install} script (see \<^technical>\<open>infrastructure\<close>  
  The common structure of an \<^isadof> document template looks as follows: 

\begin{ltx}[escapechar=ë, numbers=left,numberstyle=\tiny,xleftmargin=5mm]
\documentclass{article}        % The LaTeX-class of your template ë\label{lst:dc}ë  
%% The following part is (mostly) required by Isabelle/DOF, do not modify
\usepackage[T1]{fontenc}       % Font encoding
\usepackage[utf8]{inputenc}    % UTF8 support
\usepackage{xcolor}
\usepackage{isabelle,isabellesym,amssymb} % Required (by Isabelle)
\usepackage{amsmath}           % Used by some ontologies  
\bibliographystyle{abbrv}
\IfFileExists{DOF-core.sty}{}{ % Required by Isabelle/DOF
  \PackageError{DOF-core}{The doëëcument preparation 
   requires the Isabelle/DOF framework.}{For further help, see 
   ë\url{\dofurl}ë
}
\input{ontologies}             % This will include the document specific 
                               % ontologies from isadof.cfg
\IfFileExists{preamble.tex}{\input{preamble.tex}}{}  
\usepackage{graphicx}          % Required for images. 
\usepackage[caption]{subfig}
\usepackage[size=footnotesize]{caption}
\usepackage{hyperref}          % Required by Isabelle/DOF

%% Begin of template specific configuration ë\label{lst:config-start}ë
\urlstyle{rm}
\isabellestyle{it}     ë\label{lst:config-end}ë

%% Main document, do not modify
\begin{document}
\maketitle\input{session}
\IfFileExists{root.bib}{\bibliography{root}}{}
\end{document}
\end{ltx}
\<close>

subsection\<open>Tips, Tricks, and Known Limitations\<close>
text\<open>
  In this sectin, we sill discuss several tips and tricks for developing 
  new or adapting existing document templates or \<^LaTeX>-represenations of ontologies.
\<close>

subsubsection\<open>Getting Started\<close>
text\<open>
  In general, we recommend to create a test project (\<^eg>, using \inlinebash|isabelle mkroot_DOF|)
  to develop new document templates or ontology representations. The default setup of the \<^isadof>
  build system generated a \<^path>\<open>output/document\<close> directory with a self-contained \<^LaTeX>-setup. In 
  this directory, you can directly use \<^LaTeX> on the main file, called \<^path>\<open>root.tex\<close>:

\begin{bash}
ë\prompt{MyProject/output/document}ë pdflatex root.tex
\end{bash}

  This allows you to develop and check your \<^LaTeX>-setup without the overhead of running 
  \inlinebash|isabelle build| after each change of your template (or ontology-style). Note that 
  the content of the \<^path>\<open>output\<close> directory is overwritten by executing 
  \inlinebash|isabelle build|.
\<close>

subsubsection\<open>Truncated Warning and Error Messages\<close>
text\<open>
  By default, \<^LaTeX> cuts of many warning or error messages after 79 characters. Due to the 
  use of full-qualified names in \<^isadof>, this can often result in important information being 
  cut off. Thus, it can be very helpful to configure \<^LaTeX> in such a way that it prints 
  long error or warning messages. This can easily be done on the command line for individual 
  \<^LaTeX> invocations: 

\begin{bash}
ë\prompt{MyProject/output/document}ë max_print_line=200 error_line=200 half_error_line=100  pdflatex root.tex
\end{bash}
\<close>

subsubsection\<open>Deferred Declaration of Information\<close>
text\<open>
  During document generation, sometimes, information needs to be printed prior to its 
  declaration in a \<^isadof> theory. This violation the declaration-before-use-principle
  requires that information is written into an auxiliary file during the first run of \<^LaTeX>
  so that the information is available at further runs of \<^LaTeX>. While, on the one hand, 
  this is a standard process (\<^eg>, used for updating references), implementing it correctly
  requires a solid understanding of \<^LaTeX>'s expansion mechanism. In this context, the recently 
  introduced \inlineltx|\expanded{}|-primitive 
  (see \<^url>\<open>https://www.texdev.net/2018/12/06/a-new-primitive-expanded\<close>) is particularly useful. 
  Examples of its use can be found, \<^eg>, in the ontology-styles 
  \<^file>\<open>../../../src/ontologies/scholarly_paper/DOF-scholarly_paper.sty\<close> or 
  \<^file>\<open>../../../src/ontologies/CENELEC_50128/DOF-CENELEC_50128.sty\<close>.  For details about the expansion mechanism 
  in general, we refer the reader to the \<^LaTeX> literature (\<^eg>,~@{cite "knuth:texbook:1986"
  and "mittelbach.ea:latex:1999" and "eijkhout:latex-cs:2012"}).  
\<close>


subsubsection\<open>Authors and Affiliation Information\<close>
text\<open>
  In the context of academic papers, the defining the representations for the author and
  affiliation information is particularly challenges as, firstly, they inherently are breaking
  the declare-before-use-principle and, secondly, each publisher uses a different \<^LaTeX>-setup 
  for their declaration. Moreover, the mapping from the ontological modeling to the document
  representation might also need to bridge the gap between different common modeling styles of 
  authors and their affiliations, namely: affiliations as attributes of authors vs. authors and 
  affiliations both as entities with a many-to-many relationship.

  The ontology representation
  \<^file>\<open>../../../src/ontologies/scholarly_paper/DOF-scholarly_paper.sty\<close> contains an example that, firstly, 
  shows how to write the author and affiliation information into the auxiliary file for re-use 
  in the next \<^LaTeX>-run and, secondly, shows how to collect the author and affiliation 
  information into an \inlineltx|\author| and a \inlineltx|\institution| statement, each of 
  which containing the information for all authors. The collection of the author information 
  is provided by the following \<^LaTeX>-code:

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
\<^boxed_theory_text>\<open>text.scholarly_paper.author\<close>, which writes the collected information in the 
job's aux-file. The intermediate step of writing this information into the job's aux-file is necessary,
as the author and affiliation information is required right at the begin of the document 
(\<^ie>, when \<^LaTeX>'s \inlineltx|\maketitle| is invoked) while  \<^isadof> allows to define authors at 
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
  (\<^LaTeX>-classes), authors of ontology representations might restrict their use to 
  specific classes. This can, \<^eg>, be done using the \inlineltx|\@ifclassloaded{}| command:

\begin{ltx}
\@ifclassloaded{llncs}{}%
{% LLNCS class not loaded
    \PackageError{DOF-scholarly_paper}
    {Scholarly Paper only supports LNCS as document class.}{}\stop%
}
\end{ltx}

  For a real-world example testing for multiple classes, see 
  \<^file>\<open>../../../src/ontologies/scholarly_paper/DOF-scholarly_paper.sty\<close>:

  We encourage this clear and machine-checkable enforcement of restrictions while, at the same
  time, we also encourage to provide a package option to overwrite them. The latter allows 
  inherited ontologies to overwrite these restrictions and, therefore, to provide also support
  for additional document templates. For example, the ontology \<^boxed_theory_text>\<open>technical_report\<close>
  extends the \<^boxed_theory_text>\<open>scholarly_paper\<close> ontology and its \<^LaTeX> supports provides support
  for the \inlineltx|scrrept|-class which is not supported by the \<^LaTeX> support for 
  \<^boxed_theory_text>\<open>scholarly_paper\<close>.
\<close>

subsubsection\<open>Outdated Version of \<^path>\<open>comment.sty\<close>\<close>
text\<open>
  Isabelle's \<^LaTeX>-setup relies on an ancient version of \<^path>\<open>comment.sty\<close> that, moreover,
  is used in plain\<^TeX>-mode. This is known to cause issues with some modern \<^LaTeX>-classes
  such as LPICS. Such a conflict might require the help of an Isabelle wizard.
\<close>




(*<*)
end
(*>*) 
  
