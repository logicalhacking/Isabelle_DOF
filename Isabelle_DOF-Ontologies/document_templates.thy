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

theory 
  "document_templates"
imports
  "Isabelle_DOF.Isa_DOF"
begin

define_template "./document-templates/root-eptcs-UNSUPPORTED.tex" 
                "Unsupported template for the EPTCS class. Not for general use."
define_template "./document-templates/root-lipics-v2021-UNSUPPORTED.tex" 
                "Unsupported template for LIPICS (v2021). Not for general use."
define_template "./document-templates/root-svjour3-UNSUPPORTED.tex" 
                "Unsupported template for SVJOUR. Not for general use."
define_template "./document-templates/root-sn-article-UNSUPPORTED.tex" 
                "Unsupported template for Springer Nature's template. Not for general use."
end
