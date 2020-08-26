(*************************************************************************
 * Copyright (C) 
 *               2019-20   The University of Exeter 
 *               2018-2020 The University of Paris-Saclay
 *               2018      The University of Sheffield
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

(*<*)
theory "00_Frontmatter"
  imports "Isabelle_DOF.technical_report"
begin

section\<open>Document Local Setup.\<close>
text\<open>Some internal setup, introducing document specific abbreviations and macros.\<close>

setup \<open>DOF_lib.define_shortcut ("dof",\<^here>) "\\dof"\<close>
setup \<open>DOF_lib.define_shortcut ("isadof",\<^here>) "\\isadof"\<close>
setup \<open>   DOF_lib.define_shortcut ("eg",\<^here>) "\\eg"
       #> DOF_lib.define_shortcut ("ie",\<^here>) "\\ie"\<close> 
      (* this is an alternative style for macro definitions eauivalent to setup ... setup  ...*)
setup \<open>   DOF_lib.define_shortcut ("TeXLive",\<^here>) "\\TeXLife"
       #> DOF_lib.define_shortcut ("LaTeX",\<^here>) "\\LaTeX{}"\<close>

text\<open>Note that these setups assume that the \<^LaTeX> macros are defined in the 
     document prelude. \<close>


open_monitor*[this::report] 

(*>*)

title*[title::title]\<open>Isabelle/DOF\<close> 
subtitle*[subtitle::subtitle]\<open>User and Implementation Manual\<close> 
text*[adb:: author,
      email="\<open>a.brucker@exeter.ac.uk\<close>",
      orcid="\<open>0000-0002-6355-1200\<close>",
      http_site="\<open>https://www.brucker.ch/\<close>",
      affiliation="\<open>University of Exeter, Exeter, UK\<close>"]\<open>Achim D. Brucker\<close>
text*[bu::author,
      email       = "\<open>wolff@lri.fr\<close>",
      affiliation = "\<open>Université Paris-Saclay, LRI, Paris, France\<close>"]\<open>Burkhart Wolff\<close>
 
text*[abs::abstract,
      keywordlist="[''Ontology'', ''Ontological Modeling'', ''Document Management'', 
                    ''Formal Document Development'', ''Document Authoring'', ''Isabelle/DOF'']"]
\<open> \<^isadof> provides an implementation of \<^dof> on top of Isabelle/HOL. 
  \<^dof> itself is a novel framework for \<^emph>\<open>defining\<close> ontologies
  and \<^emph>\<open>enforcing\<close> them during document development and document
  evolution. \<^isadof>  targets use-cases such as mathematical texts referring
  to a theory development or technical reports requiring a particular structure.
  A major application of \<^dof> is the integrated development of
  formal certification documents (\<^eg>, for Common Criteria or CENELEC
  50128) that require consistency across both formal and informal
  arguments. 

  \<^isadof> is integrated into Isabelle's IDE, which
  allows for smooth ontology development as well as immediate
  ontological feedback during the editing of a document.
  Its checking facilities leverage the collaborative 
  development of documents required to be consistent with an
  underlying ontological structure.
  
  In this user-manual, we give an in-depth presentation of the design
  concepts of \<^dof>'s Ontology Definition Language (ODL) and describe
  comprehensively its major commands. Many examples show typical best-practice
  applications of the system.

  It is an unique feature of  \<^isadof>  that ontologies may be used to control
  the link between formal and informal content in documents in a machine
  checked way. These links can connect both text elements as well as formal
  modelling elements such as terms, definitions, code  and logical formulas,
  alltogether *\<open>integrated\<close> in a state-of-the-art interactive theorem prover.
\<close>

(*<*) 
end
(*>*) 
  
