(*************************************************************************
 * Copyright (C) 
 *               2019      The University of Exeter 
 *               2018-2019 The University of Paris-Saclay
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
\<open> \isadof provides an implementation of \dof on top of Isabelle/HOL. 
  \dof itself is a novel framework for \<^emph>\<open>defining\<close> ontologies
  and \<^emph>\<open>enforcing\<close> them during document development and document
  evolution. A major goal of \dof is the integrated development of
  formal certification documents (\eg, for Common Criteria or CENELEC
  50128) that require consistency across both formal and informal
  arguments.

  \isadof is integrated into Isabelle's IDE, which
  allows for smooth ontology development as well as immediate
  ontological feedback during the editing of a document.
  
  In this paper, we give an in-depth presentation of the design
  concepts of \dof's Ontology Definition Language (ODL) and key
  aspects of the technology of its implementation.  \isadof is the
  first ontology language supporting machine-checked
  links between the formal and informal parts in an LCF-style
  interactive theorem proving environment.
\<close>

(*<*) 
end
(*>*) 
  
