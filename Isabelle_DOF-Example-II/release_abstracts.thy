(*<*)
theory "release_abstracts"
  imports "Isabelle_DOF.scholarly_paper"
begin

use_template "scrartcl"
use_ontology "scholarly_paper"

open_monitor*[this::article]

declare[[ strict_monitor_checking  = false]]
declare[[ Definition_default_class = "definition"]]
declare[[ Lemma_default_class      = "lemma"]]
declare[[ Theorem_default_class    = "theorem"]]
declare[[ Corollary_default_class  = "corollary"]]

define_shortcut* dof     \<rightleftharpoons> \<open>\dof\<close>


define_shortcut* csp      \<rightleftharpoons> \<open>CSP\<close>
                 holcsp   \<rightleftharpoons> \<open>HOL-CSP\<close>

(*>*)

 
abstract*[abs, keywordlist="[\<open>Ontology\<close>, \<open>Ontological Modeling\<close>, \<open>Document Management\<close>, 
                             \<open>Formal Document Development\<close>,\<open>Isabelle/DOF\<close>]"]
\<open>   \<^isadof> provides an implementation of an document ontology framework on top of \<^isabelle>. 
    The framework allows both for \<^emph>\<open>defining\<close> ontologies and \<^emph>\<open>enforcing\<close> them during document 
    development and document evolution. \<^isadof> targets use-cases such as mathematical texts 
    referring to a theory development or technical reports requiring a particular structure.
    The documentation generation features are sufficiently powerful to typeset the most
    common cases without using LaTeX.

    \<^isadof> is integrated into Isabelle's IDE, which allows for smooth ontology development as 
    well as immediate ontological conformqnce-checks during the editing of a document. 
    Its checking facilities leverage the collaborative development of documents 
    required to be consistent with an underlying ontological structure.
    
    The present session provides a user-manual with in-depth presentation of the design
    concepts of \<^dof>'s Ontology Definition Language (ODL) and describe
    comprehensively its major commands. Many examples show typical best-practice
    applications of the system. 
  
    It is a unique feature of  \<^isadof>  that ontologies may be used to control
    the link between formal and informal content in documents in an automatically checked way. 
    These links can connect both text elements and formal modeling elements such as terms, 
    definitions, code  and logical formulas, altogether \<^emph>\<open>integrated\<close> into a state-of-the-art 
    interactive proof assistant.

\<close>

abstract*[exampleI, keywordlist="[\<open>Ontology\<close>, \<open>Ontological Modeling\<close>, \<open>Document Management\<close>, 
                             \<open>Formal Document Development\<close>,\<open>Isabelle/DOF\<close>]"]
\<open>  
  This entry contains an example of  an academic paper written using the \<^isadof> system oriented 
  towards an  introductory paper. The paper uses a number of typical situations referencing 
  figures and side-by-side figures. The paper demonstrates the power of \<^isadof>‘s typesetting 
  with no direct use of \<^LaTeX>.

  The example is relevant for its \<^emph>\<open>form\<close>; if you consider
  to cite it for its \<^emph>\<open>content\<close>, please refer to~@{cite "brucker.ea:isabelle-ontologies:2018"}.
  Please note that, consequenty, the content describes features of \<^isadof> that may be 
  partially outdated. 
\<close>

abstract*[exampleIi, keywordlist="[\<open>Ontology\<close>, \<open>Ontological Modeling\<close>, \<open>Document Management\<close>, 
                             \<open>Formal Document Development\<close>,\<open>Isabelle/DOF\<close>]"]
\<open>  
  This entry contains an example of a mathematics-oriented academic paper. 
  The paper uses a number of typical situations referencing freeform, freeform theorems, 
  complex  mathematical notation and a number of non-trivial cross-referencing  between 
  statements, definitions and proofs which are ontologically tracked.
  The paper demonstrates the power of \<^isadof>‘s typesetting with no direct use of \<^LaTeX>.
  
  The example is relevant for its \<^emph>\<open>form\<close>; if you consider to cite it for its \<^emph>\<open>content\<close>, 
  please refer to~@{cite "taha.ea:philosophers:2020"}}. Please note that, consequenty, 
  the content describes some features of HOL-CSP theories that may be partially outdated. 
\<close>


text\<open>
\<^url>\<open> sdfsdf \<close>
\<close>



end
(*>*) 
