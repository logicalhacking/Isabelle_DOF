(*<*)
(*************************************************************************
 * Copyright (C) 
 *               2019-2023 The University of Exeter 
 *               2018-2023 The University of Paris-Saclay
 *               2018      The University of Sheffield
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)
theory "Isabelle_DOF-Unit-Tests_document"
  imports
    "Isabelle_DOF.technical_report"
    (* "Isabelle_DOF-Ontologies.CENELEC_50128"  where do we use this - bu *)
  
begin

use_template "scrreprt-modern"
use_ontology "technical_report" (* and "Isabelle_DOF-Ontologies.CENELEC_50128" *)
(*>*)

title*[title::title]         \<open>The Isabelle/DOF Implementation\<close>
subtitle*[subtitle::subtitle]\<open>The Unit-Test Suite\<close>

(*<*)
end
(*>*)
