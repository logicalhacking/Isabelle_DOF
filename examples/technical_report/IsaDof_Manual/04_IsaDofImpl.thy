(*<*)
theory "04_IsaDofImpl"
  imports "02_Background"
begin
(*>*)


chapter*[impl1::introduction,main_author="Some(@{docitem ''adb''}::author)"]
        \<open>Isabelle Ontology Framework \isadof\<close>
text\<open>
In this section, we introduce our framework, called \isadof. \isadof
is based on several design-decisions:
\begin{compactitem}
\item the entire \isadof is conceived as ``pure add-on'', \ie, we
  deliberately resign on the possibility to modify Isabelle itself
  (thus accepting a minor loss in performance and some additional
  complexity in the documentation generation process)
\item we decided to identify the ontology types with the Isabelle/HOL
  type system, \ie, we reuse the same infrastructure for parsers and
  type-checkers, but use the types on the meta-level of the document
  structure
\item we decided to make the markup-generation by own means in order
  to adapt it as good as possible to the needs of tracking the linking
  in documents.
\end{compactitem}
\<close>


subsection*["sec:plugins"::technical]{*Writing \isadof as User-Defined Plugin in Isabelle/Isar*}
text\<open>
Writing an own plugin in Isabelle starts with defining the local data
and registering it in the framework.  As mentioned before, contexts
are structures with independent cells/compartments having three
primitives \inlinesml+init+, \inlinesml+extend+ and
\inlinesml+merge+. Technically this is done by instantiating a functor
\inlinesml+Generic_Data+, and the following fairly typical
code-fragment is already drawn from \isadof:
\begin{sml}
  structure Data = Generic_Data
  (  type T = docobj_tab * docclass_tab 
     val empty  = (initial_docobj_tab, initial_docclass_tab) 
     val extend = I
     fun merge((d1,c1),(d2,c2))  = (merge_docobj_tab (d1, d2), 
                                    merge_docclass_tab(c1,c2))
  );
\end{sml}
with some tables \inlinesml+docobj_tab+ and \inlinesml+docclass_tab+
(not explained here) capturing the specific data of the application in
mind, \ie, a table of document classes and another one capturing the
document class instances.
\enlargethispage{2\baselineskip}
\<close>
text\<open>
All the text samples shown here have to be in the context of an SML
file or in an \inlineisar|ML{* ... *}| command inside a \verb|.thy|
file, which has the effect to type-check and compile these text
elements by the underlying SML compiler.
\<close>
text\<open>
Operations are organized in a model-view-controller scheme, where
Isabelle/Isar provides the controller part. A typical model operation
has the type:\<close>
text\<open>
\begin{sml}
  val opn :: <args_type> -> Context.generic -> Context.generic
\end{sml}
\ie, it represents a transformation on contexts. For example, the
operation of declaring a local reference in the context is presented
as follows:
\begin{sml}
  fun declare_object_local oid ctxt  =
  let fun decl {tab,maxano} = {tab=Symtab.update_new(oid,NONE) tab,
                               maxano=maxano}
  in  (Data.map(apfst decl)(ctxt)
    handle Symtab.DUP _ =>
                error("multiple declaration of document reference"))
  end
\end{sml} 
\<close>
text\<open>
where \inlineisar+Data.map+ is the update function resulting from the
above functor instantiation.  This code fragment uses operations from
a library structure \inlinesml+Symtab+ that were used to update the
appropriate table for document objects in the plugin-local
state. Possible exceptions to the update operation were mapped to a
system-global error reporting function.
\<close>
text\<open>
Finally, the view-aspects where handled by an API for
parsing-combinators. The library structure \inlinesml+Scan+ provides,
for example, the operators:
\begin{sml}
  op ||     : ('a -> 'b) * ('a -> 'b) -> 'a -> 'b
  op --     : ('a -> 'b * 'c) * ('c -> 'd * 'e) -> 'a -> ('b * 'd) * 'e
  op |--    : ('a -> 'b * 'c) * ('c -> 'd * 'e) -> 'a -> 'd * 'e
  op --|    : ('a -> 'b * 'c) * ('c -> 'd * 'e) -> 'a -> 'b * 'e
  op >>     : ('a -> 'b * 'c) * ('b -> 'd) -> 'a -> 'd * 'c
  op option : ('a -> 'b * 'a) -> 'a -> 'b option * 'a
  op repeat : ('a -> 'b * 'a) -> 'a -> 'b list * 'a
\end{sml}                                            
for alternative, sequence, sequence-ignore-left,
sequence-ignore-right, and piping, as well as combinators for option
and repeat. The parsing combinator technology arrived meanwhile even
in mainstream languages such as Java or Scala and is nowadays
sufficiently efficient implemented to replace conventional Lex-Yacc
technology for most applications. It has the advantage to be
smoothlessly integrated into standard programs and allows for dynamic
grammar extensions.  There is a more high-level structure
\inlinesml{Parse} providing specific combinators for the
command-language Isar:
\begin{sml}
  val attribute = Parse.position Parse.name 
        -- Scan.optional (Parse.$$$ "=" |-- Parse.!!! Parse.name) "";
  val reference = Parse.position Parse.name 
        -- Scan.option (Parse.$$$ "::" |-- Parse.!!!
                         (Parse.position Parse.name));
  val attributes =  (Parse.$$$ "[" |-- (reference 
                     -- (Scan.optional(Parse.$$$ ","
                         |-- (Parse.enum "," attribute))) []))
                                  --| Parse.$$$ "]"              
\end{sml}                                            
``Model'' and ``View'' parts were combined to ``parsers'' which were
registered in the interpreter toplevel of the Isabelle/Isar framework:
\begin{sml}
  val _ = Outer_Syntax.command @ {command_keyword "declare_reference"}
          "declare document reference"
          (attributes >> (fn (((oid,pos),cid),doc_attrs) =>  
             (Toplevel.theory (DOF_core.declare_object_global oid))));
\end{sml}
\<close>
text\<open>
Altogether, this gives the \emph{extension} of the Isar syntax
allowing to parse and interpret the new \emph{command} in a subsequent
\verb+.thy+ file:
\begin{isar}
declare_reference [lal::requirement, alpha="main", beta=42]
\end{isar}
where we ignore the semantics at the moment. The construction also
generates implicitely some markup information; for example, when
hovering over the \inlineisar|declare_reference| command in a
front-end supporting PIDE, a popup window with the text: ``declare
document reference'' will appear.
\<close>

subsection*["sec:prog_anti"::technical]{*Programming Text Antiquotations*}
text\<open>
As mentioned in the introduction, Isabelle/Isar is configured with a
number of standard commands to annotate formal definitions and proofs
with text---the latter is used in particular to generate PDF and HTML
documents with internal hypertext-references. Inside these text
commands, a number of predefined antiquotations can be inserted which
were checked and decorated with markup during editing. 
\<close>
text\<open>
Moreover, there is an API for user-defined antiquotations.  It follows
the lines of the MVC style system extensions presented in the previous
section.  An excerpt of the table defining some antiquotations can be
found in \verb+thy_output.ML+ of the Isabelle sources and give the
basic idea:
\begin{sml}
  val _ = Theory.setup
  (basic_entity @ {binding term} (stp -- Args.term) pretty_term_style #>
   basic_entity @ {binding prop} (stp -- Args.prop) pretty_term_style #>
    ... )
\end{sml}
where \inlinesml+stp+ (=\inlinesml+Term_Style.parse+),
\inlinesml+Args.term+ and \inlinesml+Args.prop+ are parsing
combinators from higher Isar-API's (that actually do the type checking
in the surrounding HOL context) and \inlinesml+pretty_term_style+ an
operation pretty-printing the parsed term for one of the possible
targets HTML or \LaTeX{} (converted to \verb+.pdf+ in a
post-compilation process). The construct \inlinesml+@ {binding term}+
decorates the keyword ``term'' with positioning markup (allowing 
navigating to this defining place in \verb+thy_output.ML+ by
hyperlinking) and \inlinesml+Theory.setup+ the operator that
registers the entire parser/checker into the Isar framework.
\<close>
text\<open>
Together, this establishes the syntax and semantics of, for example,
the antiquotation:
\begin{isar}
text{* @{term "fac 5"} *}
\end{isar}
inside the text command. A key contribution of this paper is that such
SML code is generated \emph{automatically} from an \isadof ontology
definition introduced in the subsequent section.
\<close>

end