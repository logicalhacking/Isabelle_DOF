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
theory "Isabelle_DOF-Manual"
  imports "05_Implementation"
begin
use_template "scrreprt-modern"
use_ontology "technical_report" and "CENELEC_50128"
close_monitor*[this]
check_doc_global
text\<open>Resulting trace in \<^verbatim>\<open>doc_item\<close> ''this'': \<close>
ML\<open>@{trace_attribute this}\<close>

 
end
(*>*) 


