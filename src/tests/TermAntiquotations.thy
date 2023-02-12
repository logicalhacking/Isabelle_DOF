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

chapter\<open>Term Antiquotations\<close>

text\<open>Terms are represented by "Inner Syntax" parsed by an Earley parser in Isabelle.
For historical reasons, \<^emph>\<open>term antiquotations\<close> are called therefore somewhat misleadingly
"Inner Syntax Antiquotations". \<close>

theory 
  TermAntiquotations
imports 
  "Isabelle_DOF.Conceptual"
begin

text\<open>Since the syntax chosen for values of doc-class attributes is HOL-syntax --- requiring
a fast read on the ``What's in Main''-documentation, but not additional knowledge on, say, SML --- 
an own syntax for references to types, terms, theorems, etc. are necessary. These are the
``Inner Syntax Antiquotations'' since they make only sense \emph{inside} the Inner-Syntax
of Isabelle/Isar, so inside the \verb+" ... "+ parenthesis.

They are the key-mechanism to denote 
\<^item> Ontological Links, i.e. attributes refering to document classes defined by the ontology
\<^item> Ontological F-Links, i.e. attributes referring to formal entities inside Isabelle (such as thm's)

This file contains a number of examples resulting from the 
% @ {theory "Isabelle_DOF-tests.Conceptual"} does not work here --- why ?
\<^theory_text>\<open>Conceptual\<close> - ontology; the emphasis of this presentation is to present the expressivity of 
ODL on a paradigmatical example.
\<close>


text\<open>Voila the content of the Isabelle_DOF environment so far:\<close>
ML\<open>
val x = DOF_core.get_instances \<^context>
val isa_transformer_tab = DOF_core.get_isa_transformers \<^context>
val {docclass_tab,...} = DOF_core.get_data @{context}; 
Name_Space.dest_table isa_transformer_tab; 
\<close>

text\<open>Some sample lemma:\<close>
lemma murks : "Example=Example" by simp

text\<open>Example for a meta-attribute of ODL-type @{typ "file"} with an appropriate ISA for the
     file @{file "TermAntiquotations.thy"}\<close>
(* not working: 
text*[xcv::F, u="@{file ''InnerSyntaxAntiquotations.thy''}"]\<open>Lorem ipsum ...\<close>
*)

text*[xcv1::A, x=5]\<open>Lorem ipsum ...\<close>
text*[xcv3::A, x=7]\<open>Lorem ipsum ...\<close>

text\<open>Example for a meta-attribute of ODL-type @{typ "typ"} with an appropriate ISA for the
     theorem @{thm "refl"}}\<close>
text*[xcv2::C, g="@{thm ''HOL.refl''}"]\<open>Lorem ipsum ...\<close>

text\<open>A warning about the usage of the \<open>docitem\<close> TA:
The \<open>docitem\<close> TA offers a way to check the reference of class instances
without checking the instances type.
So one will be able to reference \<open>docitem\<close>s (class instances) and have them checked,
without the burden of the type checking required otherwise.
But it may give rise to unwanted behaviors, due to its polymorphic type.
It must not be used for certification.
\<close>

text\<open>Major sample: test-item of doc-class \<open>F\<close> with a relational link between class instances, 
     and links to formal Isabelle items like \<open>typ\<close>, \<open>term\<close> and \<open>thm\<close>. \<close>
text*[xcv4::F, r="[@{thm ''HOL.refl''}, 
                   @{thm \<open>TermAntiquotations.murks\<close>}]", (* long names required *)
               b="{(@{docitem ''xcv1''},@{docitem \<open>xcv2\<close>})}",  (* notations \<open>...\<close> vs. ''...'' *)
               s="[@{typ \<open>int list\<close>}]",                        
               properties = "[@{term \<open>H \<longrightarrow> H\<close>}]"              (* notation \<open>...\<close> required for UTF8*)
]\<open>Lorem ipsum ...\<close>

text*[xcv5::G, g="@{thm \<open>HOL.sym\<close>}"]\<open>Lorem ipsum ...\<close>

text\<open>... and here we add a relation between @{docitem \<open>xcv3\<close>} and @{docitem \<open>xcv2\<close>} 
into the relation \verb+b+ of @{docitem \<open>xcv5\<close>}. Note that in the link-relation,
a @{typ "C"}-type is required, but a  @{typ "G"}-type is offered which is legal in
\verb+Isa_DOF+ because of the sub-class relation between those classes: \<close>
update_instance*[xcv4::F, b+="{(@{docitem ''xcv3''},@{docitem ''xcv5''})}"]

text\<open>And here is the results of some ML-term antiquotations:\<close>
ML\<open> @{docitem_attribute b::xcv4} \<close>
ML\<open> @{docitem xcv4}              \<close>
ML\<open> @{docitem_name xcv4}         \<close>
ML\<open> @{trace_attribute aaa}       \<close>

text\<open>Now we might need to reference a class instance in a term command and we would like
Isabelle to check that this instance is indeed an instance of this class.
Here, we want to reference the instance @{docitem_name "xcv4"} previously defined.
We can use the term* command which extends the classic term command
and does the appropriate checking.\<close>
term*\<open>@{F \<open>xcv4\<close>}\<close>

text\<open>We can also reference an attribute of the instance.
Here we reference the attribute r of the class F which has the type @{typ \<open>thm list\<close>}.\<close>
term*\<open>r @{F \<open>xcv4\<close>}\<close>

text\<open>We declare a new text element. Note that the class name contains an underscore "_".\<close>
text*[te::text_element]\<open>Lorem ipsum...\<close>

text\<open>Unfortunately due to different lexical conventions for constant symbols and mixfix symbols
     this term antiquotation has to be denoted like this: @{term_ \<open>@{text-element \<open>te\<close>}\<close>}.
     We need to substitute an hyphen "-" for the underscore "_".\<close>
term*\<open>@{text-element \<open>te\<close>}\<close>

text\<open>Terms containing term antiquotations can be checked and evaluated
using \<^theory_text>\<open>term_\<close> and \<^theory_text>\<open>value_\<close> text antiquotations respectively:
We can print the term @{term_ \<open>r @{F \<open>xcv4\<close>}\<close>} with \<open>@{term_ \<open>r @{F \<open>xcv4\<close>}\<close>}\<close>
or get the value of the \<^const>\<open>F.r\<close> attribute of @{docitem \<open>xcv4\<close>} with \<open>@{value_ \<open>r @{F \<open>xcv4\<close>}\<close>}\<close>
\<^theory_text>\<open>value_\<close> may have an optional argument between square brackets to specify the evaluator but this
argument must be specified after a default optional argument already defined
by the text antiquotation implementation.
So one must use the following syntax if he does not want to specify the first optional argument:
\<open>@{value_ [] [nbe] \<open>r @{F \<open>xcv4\<close>}\<close>}\<close>. Note the empty brackets.

\<close>

text\<open>There also are \<^theory_text>\<open>term_\<close> and \<^theory_text>\<open>value_\<close> ML antiquotations:
\<^ML>\<open>@{term_ \<open>r @{F \<open>xcv4\<close>}\<close>}\<close> will return the ML representation of the term \<^term_>\<open>r @{F \<open>xcv4\<close>}\<close>,
and \<^ML>\<open>@{value_ \<open>r @{F \<open>xcv4\<close>}\<close>}\<close> will return the ML representation
of the value of the \<^const>\<open>F.r\<close> attribute of @{docitem \<open>xcv4\<close>}.
\<^theory_text>\<open>value_\<close> may have an optional argument between square brackets to specify the evaluator:
\<close>

ML\<open>
val t = @{term_ \<open>r @{F \<open>xcv4\<close>}\<close>}
val tt = @{value_ [nbe] \<open>r @{F \<open>xcv4\<close>}\<close>}
\<close>

end

