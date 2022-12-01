/*
 * Copyright (c) 
 *               2021-2022 The University of Exeter. 
 *               2021-2022 The University of Paris-Saclay. 
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 * COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
 * BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 * ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 * POSSIBILITY OF SUCH DAMAGE.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 */


/*** constants and parameters for Isabelle/DOF ***/

package isabelle.dof

import isabelle._


object DOF {
  val isabelle_version = "2022"
  val isabelle_url = "https://isabelle.in.tum.de/website-Isabelle2022"

  // Isabelle/DOF version: "Unreleased" for development, semantic version for releases
  val version = "Unreleased"

  val session = "Isabelle_DOF"

  def implode_ontologies(list: List[String]): String = Word.implode(list)
  def explode_ontologies(text: String): List[String] = Word.explode(text)
  val ontologies: List[String] =
    explode_ontologies("Isabelle_DOF.technical_report Isabelle_DOF.scholarly_paper")
  val template = "Isabelle_DOF.scrreprt-modern"

  val latest_version = "1.3.0"
  val latest_isabelle = "Isabelle2021-1"
  val latest_doi = "10.5281/zenodo.6810799"
  val generic_doi = "10.5281/zenodo.3370482"

  // Isabelle/DOF source repository
  val url = "https://git.logicalhacking.com/Isabelle_DOF/Isabelle_DOF"

  // Isabelle/DOF release artifacts
  val artifact_dir = "releases/Isabelle_DOF/Isabelle_DOF"
  val artifact_host = "artifacts.logicalhacking.com"
  val artifact_url: String = "https://" + artifact_host + "/" + artifact_dir

  def options(opts: Options): Options = opts + "document_comment_latex"
}
