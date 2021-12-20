chapter \<open>Notes on Isabelle/DOF for Isabelle2021-1\<close>

theory NOTES
  imports Main
begin

section \<open>Isabelle/DOF component setup\<close>

subsection \<open>Terminology\<close>

text \<open>
  \<^item> The concept of \<^emph>\<open>Isabelle system component\<close> is explained in \<^doc>\<open>system\<close>
  section 1.1.1; see also \<^tool>\<open>components\<close> explained in section 7.3.

    For example:

      \<^verbatim>\<open>isabelle components -l\<close>

  \<^item> In the private terminology of Burkhart, the word "component" has a
  different meaning: a tool implemented in Isabelle/ML that happens to
  declare context data (many ML tools do that, it is not very special,
  similar to defining a \<^verbatim>\<open>datatype\<close> or \<^verbatim>\<open>structure\<close> in ML).
\<close>


subsection \<open>Isabelle/DOF as component\<close>

text \<open>
  Formal Isabelle/DOF component setup happens here:

  \<^item> \<^path>\<open>$ISABELLE_HOME_USER/etc/components\<close>

    \<^item> A suitable directory entry in the file registers our component to
    existing Isabelle installation; it also activates the session
    directory tree starting at \<^file>\<open>$ISABELLE_DOF_HOME/ROOTS\<close>.

    \<^item> Alternative: use \<^path>\<open>$ISABELLE_HOME/Admin/build_release\<close> with
    option \<^verbatim>\<open>-c\<close> to produce a derived Isabelle distribution that bundles
    our component for end-users (maybe even with AFP entries).

  \<^item> \<^file>\<open>$ISABELLE_DOF_HOME/etc/settings\<close>

    \<^item> This provides a pervasive Bash process environment (variables,
    shell functions etc.). It may refer to \<^verbatim>\<open>$COMPONENT\<close> for the
    component root, e.g. to retain it in variable \<^dir>\<open>$ISABELLE_DOF_HOME\<close>.

    \<^item> Historically, it used to be the main configuration area, but today
    we see more and more alternatives, e.g. system options or services in
    Isabelle/Scala (see below).

  \<^item> \<^file>\<open>$ISABELLE_DOF_HOME/etc/options\<close>

    \<^item> options declared as \<^verbatim>\<open>public\<close> appear in the Isabelle/jEdit dialog
    \<^action>\<open>plugin-options\<close> (according to their \<^verbatim>\<open>section\<close>)

    \<^item> all options (public and non-public) are available for command-line
    usage, e.g. \<^verbatim>\<open>isabelle build -o dof_url="..."\<close>

    \<^item> access to options in Isabelle/ML:

      \<^item> implicit (for the running ML session)
        \<^ML>\<open>Options.default_string \<^system_option>\<open>dof_url\<close>\<close>

      \<^item> explicit (e.g. for each theories section in
      \<^file>\<open>$ISABELLE_HOME/src/Pure/Tools/build.ML\<close>):
        \<^ML>\<open>fn options => Options.string options \<^system_option>\<open>dof_url\<close>\<close>

    \<^item> access in Isabelle/Scala is always explicit; the initial options
      should be created only once and passed around as explicit argument:

      \<^scala>\<open>{
        val options = isabelle.Options.init();
        options.string("dof_url");
      }\<close>

      Note: there are no antiquotations in Isabelle/Scala, so the literal
      string \<^scala>\<open>"dof_url"\<close> is unchecked.
\<close>


section \<open>Document preparation in Isabelle/ML\<close>

subsection \<open>Session presentation hook\<close>

text \<open>
  \<^ML>\<open>Build.add_hook\<close> allows to install a global session presentation
  hook. It is used e.g. in Isabelle/Mirabelle to analyze all loaded
  theories via Sledgehammer and other tools. Isabelle/DOF could use it to
  "wrap-up" the whole session, to check if all document constraints hold
  (cf. "monitors").
\<close>


subsection \<open>Theory presentation hook\<close>

text \<open>
  \<^ML>\<open>Thy_Info.add_presentation\<close> installs a hook to be invoked at the
  end of successful loading of theories; the provided context
  \<^ML_type>\<open>Thy_Info.presentation_context\<close> provides access to
  \<^ML_type>\<open>Options.T\<close> and \<^ML_type>\<open>Document_Output.segment\<close> with
  command-spans and semantic states.

  An example is regular Latex output in
  \<^file>\<open>$ISABELLE_HOME/src/Pure/Thy/thy_info.ML\<close> where \<^ML>\<open>Export.export\<close>
  is used to produce export artifacts in the session build database, for
  retrieval via Isabelle/Scala.
\<close>


subsection \<open>Document commands\<close>

text \<open>
  Isar toplevel commands now support a uniform concept for
  \<^ML_type>\<open>Toplevel.presentation\<close>, but the exported interfaces are
  limited to commands that do not change the semantic state: see
  \<^ML>\<open>Toplevel.present\<close> and \<^ML>\<open>Toplevel.present_local_theory\<close>.

  There is an adhoc change to support \<^verbatim>\<open>Toplevel.present_theory\<close> in
  \<^file>\<open>$ISABELLE_DOF_HOME/src/patches/present_theory\<close>.

  An alternative, without patching Isabelle2021-1 in production, is to use
  the presentation hook together with a function like this:
\<close>

ML \<open>
  fun present_segment pr (segment: Document_Output.segment) =
    (case #span segment of
      Command_Span.Span (Command_Span.Command_Span (name, _), toks) =>
        let
          val {span, command = tr, prev_state = st, state = st'} = segment;
          val tr' =
            Toplevel.empty
            |> Toplevel.name (Toplevel.name_of tr)
            |> Toplevel.position (Toplevel.pos_of tr)
            |> Toplevel.present (pr name toks);
          val st'' = Toplevel.command_exception false tr' st'
            handle Runtime.EXCURSION_FAIL (exn, _) => Exn.reraise exn;
        in {span = span, command = tr, prev_state = st, state = st''} end
    | _ => segment);
\<close>


subsection \<open>Document content\<close>

text \<open>
  XML is now used uniformly (sometimes as inlined YXML). The meaning of
  markup elements and properties is defined in
  \<^scala_type>\<open>isabelle.Latex.Output\<close> (or user-defined subclasses).
\<close>


section \<open>Isabelle/Scala services\<close>

subsection \<open>Isabelle/DOF/Scala module\<close>

text \<open>
  \<^item> \<^file>\<open>$ISABELLE_DOF_HOME/etc/build.props\<close> is the main specification for
  the Isabelle/DOF/Scala module. It is built on the spot as required, e.g.
  for \<^verbatim>\<open>isabelle scala\<close> or \<^verbatim>\<open>isabelle jedit\<close>; an alternative is to invoke
  \<^verbatim>\<open>isabelle scala_build\<close> manually. See also \<^doc>\<open>system\<close>, chapter 5,
  especially section 5.2.

  \<^item> \<^verbatim>\<open>isabelle scala_project\<close> helps to develop Isabelle/Scala tools with
  proper IDE support, notably IntelliJ IDEA: the generated project uses
  Maven. See also \<^doc>\<open>system\<close>, section 5.2.3.

  \<^item> Command-line tools should be always implemented in Scala; old-fashioned
  shell scripts are no longer required (and more difficult to implement
  properly). Only a few low-level tools are outside the Scala environment,
  e.g. \<^verbatim>\<open>isabelle getenv\<close>. Add-on components should always use a name
  prefix for their tools, e.g. \<^verbatim>\<open>isabelle dof_mkroot\<close> as defined in
  \<^file>\<open>$ISABELLE_DOF_HOME/src/scala/dof_mkroot.scala\<close>.
\<close>


subsection \<open>Document preparation\<close>

text \<open>
  \<^item> \<^scala_type>\<open>isabelle.Document_Build.Engine\<close> is the main entry-point
  for user-defined document preparation; existing templates and examples
  are defined in the same module \<^file>\<open>~~/src/Pure/Thy/document_build.scala\<close>.
  There are two stages:

    \<^enum> \<^verbatim>\<open>prepare_directory\<close>: populate the document output directory (e.g.
    copy static document files, collect generated document sources from the
    session build database).

    \<^enum> \<^verbatim>\<open>build_document\<close>: produce the final PDF within the document output
    directory (e.g. via standard LaTeX tools).

  See also \<^system_option>\<open>document_build\<close> as explained in \<^doc>\<open>system\<close>,
  section 3.3.
\<close>


section \<open>Miscellaneous NEWS and Notes\<close>

text \<open>
  \<^item> Document preparation: there are many new options etc. that might help
    to fine-tune DOF output, e.g. \<^system_option>\<open>document_comment_latex\<close>.

  \<^item> ML: Theory_Data / Generic_Data: "val extend = I" has been removed;
    obsolete since Isabelle2021.

  \<^item> ML: \<^ML>\<open>Thm.instantiate\<close> and related operations now use explicit
    abstract types for the instantiate, see \<^file>\<open>~~/src/Pure/term_items.ML\<close>

  \<^item> ML: new antiquotation "instantiate" allows to instantiate formal
    entities (types, terms, theorems) with values given ML. For example:

    \<^ML>\<open>fn (A, B) =>
        \<^instantiate>\<open>'a = A and 'b = B in typ \<open>('a \<times> 'b) list\<close>\<close>\<close>

    \<^ML>\<open>fn A =>
        \<^instantiate>\<open>'a = A in
          lemma (schematic) \<open>x = y \<Longrightarrow> y = x\<close> for x y :: 'a by simp\<close>\<close>

  \<^item> ML: new antiquotations for type constructors and term constants. For
  example:

    \<^ML>\<open>\<^Type>\<open>nat\<close>\<close>
    \<^ML>\<open>fn (A, B) => \<^Type>\<open>fun A B\<close>\<close>
    \<^ML>\<open>\<^Type_fn>\<open>fun A B => \<open>(A, B)\<close>\<close>\<close>

    \<^ML>\<open>fn (A, B) => \<^Const>\<open>conj for A B\<close>\<close>
    \<^ML>\<open>\<^Const_fn>\<open>conj for A B => \<open>(A, B)\<close>\<close>\<close>

    \<^ML>\<open>fn t =>
      case t of
        \<^Const_>\<open>plus T for x y\<close> => ("+", T, x, y)
      | \<^Const_>\<open>minus T for x y\<close> => ("-", T, x, y)
      | \<^Const_>\<open>times T for x y\<close> => ("*", T, x, y)\<close>

    Note: do not use unchecked things like
    \<^ML>\<open>Const ("List.list.Nil", Type ("Nat.nat", []))\<close>

  \<^item> ML: antiquotations "try" and "can" operate directly on the given ML
    expression, in contrast to functions "try" and "can" that modify
    application of a function.

    Note: instead of semantically ill-defined "handle _ => ...", use
    something like this:

    \<^ML>\<open>
      fn (x, y) =>
        (case \<^try>\<open>x div y\<close> of
          SOME z => z
        | NONE => 0)
    \<close>

    \<^ML>\<open>
      fn (x, y) => \<^try>\<open>x div y\<close> |> the_default 0
    \<close>
\<close>

end

(* :maxLineLen=75: *)