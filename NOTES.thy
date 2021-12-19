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


section \<open>Isabelle/ML\<close>


section \<open>Isabelle/Scala\<close>


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