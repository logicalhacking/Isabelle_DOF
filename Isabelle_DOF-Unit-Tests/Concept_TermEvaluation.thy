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

chapter\<open>Term-Antiquotation Expansions and Evaluation\<close>

theory 
  Concept_TermEvaluation
imports 
  "Isabelle_DOF-Unit-Tests.Concept_TermAntiquotations"
  "Isabelle_DOF-Unit-Tests.Concept_High_Level_Invariants"
  TestKit
begin 

section\<open>Test Purpose.\<close>
text\<open> Creation of ontological instances along the \<^theory>\<open>Isabelle_DOF-Ontologies.Conceptual\<close> 
Ontology. Emphasis is put on type-safe (ontologically consistent) referencing of text, code and
proof elements. Some tests cover also the critical cases concerning name spaces of oid's. \<close>


section\<open>\<^theory_text>\<open>ML*\<close>-Annotated SML-commands\<close>
(*<*)
ML*[thefunction::B,x=\<open>\<open>dfg\<close>\<close>]\<open>fun fac x = if x = 0 then 1 else x * fac(x-1);
                               val t = \<^value_>\<open>x @{B \<open>thefunction\<close>}\<close>\<close>
ML\<open>fac 5; t\<close> \<comment> \<open>this is a test that ML* is actually evaluated and the 
                 resulting toplevel state is preserved.\<close>
text*[the::C]\<open> @{B "thefunction"} \<close>
text\<open>... and here we reference @{B \<open>thefunction\<close>}.\<close>
(*>*)



section\<open>Term-Annotation and its Evaluation\<close>

text\<open>Term Annotation Antiquotations (TA) can be evaluated with the help of the value* command.\<close>

text\<open>The value* command uses the same code as the value command
and adds the possibility to evaluate Term Annotation Antiquotations (TA).
For that an elaboration of the term referenced by a TA must be done before
passing it to the evaluator.
The current implementation is based on referential equality, syntactically, and
with the help of HOL, on referential equivalence, semantically:
Some built-ins remain as unspecified constants:
\<^item> the docitem TA offers a way to check the reference of class instances
  without checking the instances type.
  It must be avoided for certification

We also have the possibility to make some requests on classes instances, i.e. on docitems
by specifying the doc class.
The TA denotes the HOL list of the values of the instances.
The value of an instance is the record of every attributes of the instance.
This way, we can use the usual functions on lists to make our request.

The emphasis of this presentation is to present the evaluation possibilities and limitations
of the current implementation.
\<close>

section\<open>Term Annotation evaluation\<close>
(*<*)
text\<open>We can validate a term with TA:\<close>
term*[axx::A]\<open>@{thm \<open>HOL.refl\<close>}\<close>

text\<open>check : @{A "axx"}\<close>

text\<open>Now we can evaluate a term with TA:
the current implementation return the term which references the object referenced by the TA.
Here the evualuation of the TA will return the HOL.String which references the theorem:
\<close>
value*\<open>@{thm \<open>HOL.refl\<close>}\<close> \<comment> \<open>syntax check\<close>

value*[axxx::A]\<open>@{thm \<open>HOL.refl\<close>}\<close> \<comment> \<open>defining a reference of class A\<close> 

text\<open>check : @{A "axxx"}\<close> \<comment> \<open>using it\<close> 
(*>*)
text\<open>An instance class is an object which allows us to define the concepts we want in an ontology.
It is a concept which will be used to implement an ontology. It has roughly the same meaning as
an individual in an OWL ontology.
The validation process will check that the instance class @{docitem \<open>xcv1\<close>} is indeed
an instance of the class @{doc_class A}:
\<close>
term*\<open>@{A \<open>xcv1\<close>}\<close>

text\<open>The instance class @{docitem \<open>xcv1\<close>} is not an instance of the class @{doc_class B}:\<close>
value-assert-error\<open>@{B \<open>xcv1\<close>}\<close>\<open>xcv1 is not an instance of Conceptual.B\<close>

text\<open>We can evaluate the instance class. The current implementation returns
the value of the instance, i.e. a collection of every attribute of the instance: \<close>
value*\<open>@{A \<open>xcv1\<close>}\<close>

text\<open>We can also get the value of an attribute of the instance:\<close>
value*\<open>A.x @{A \<open>xcv1\<close>}\<close>

text\<open>If the attribute of the instance is not initialized, we get an undefined value,
whose type is the type of the attribute:\<close>
term*\<open>B.level @{C \<open>xcv2\<close>}\<close>
value*\<open>B.level @{C \<open>xcv2\<close>}\<close>

text\<open>The value of a TA is the term itself:\<close>
term*\<open>C.g @{C \<open>xcv2\<close>}\<close>
value*\<open>C.g @{C \<open>xcv2\<close>}\<close>

text\<open>Some terms can be validated, i.e. the term will be checked,
and the existence of every object referenced by a TA will be checked,
and can be evaluated by using referential equivalence.
The existence of the instance @{docitem \<open>xcv4\<close>} can be validated,
and the fact that it is an instance of the class @{doc_class F} will be checked:\<close>
term*\<open>@{F \<open>xcv4\<close>}\<close>

text\<open>We can also evaluate the instance @{docitem \<open>xcv4\<close>}.
The attribute \<open>b\<close> of the instance @{docitem \<open>xcv4\<close>} is of type @{typ "(A \<times> C) set"}
but the instance @{docitem \<open>xcv4\<close>} initializes the attribute by using the \<open>docitem\<close> TA.
Then the instance can be evaluate but only the references of the classes of the set
used in the \<open>b\<close> attribute will be checked, and the type of these classes will not:\<close>
value* \<open>@{F \<open>xcv4\<close>}\<close>


text\<open>If we want the classes to be checked,
we can use the TA which will also check the type of the instances.
The instance @{A \<open>xcv3\<close>} is of type @{typ "A"} and the instance @{C \<open>xcv2\<close>} is of type @{typ "C"}:\<close>
update_instance*[xcv4::F, b+="{(@{A ''xcv3''},@{C ''xcv2''})}"]

text\<open>Using a TA in terms is possible, and the term is evaluated:\<close>
value*\<open>[@{thm \<open>HOL.refl\<close>}, @{thm \<open>HOL.refl\<close>}]\<close>
value*\<open>@{thm ''HOL.refl''} = @{thm (''HOL.refl'')}\<close>

ML\<open>@{thm "refl"}\<close>

section\<open>Request on instances\<close>

text\<open>We define a new class Z:\<close>
doc_class Z =
  z::"int"

text\<open>And some instances:\<close>
text*[test1Z::Z, z=1]\<open>lorem ipsum...\<close>
text*[test2Z::Z, z=4]\<open>lorem ipsum...\<close>
text*[test3Z::Z, z=3]\<open>lorem ipsum...\<close>

text\<open>We want to get all the instances of the @{doc_class Z}:\<close>
value*\<open>@{Z-instances}\<close>

text\<open>Now we want to get the instances of the @{doc_class Z} whose attribute z > 2:\<close>
value*\<open>filter (\<lambda>\<sigma>. Z.z \<sigma> > 2) @{Z-instances}\<close>

text\<open>We can check that we have the list of instances we wanted:\<close>
value*\<open>filter (\<lambda>\<sigma>. Z.z \<sigma> > 2) @{Z-instances} = [@{Z \<open>test3Z\<close>}, @{Z \<open>test2Z\<close>}]
       \<or> filter (\<lambda>\<sigma>. Z.z \<sigma> > 2) @{Z-instances} = [@{Z \<open>test2Z\<close>}, @{Z \<open>test3Z\<close>}]\<close>

text\<open>Now, we want to get all the instances of the @{doc_class A}\<close>
value*\<open>@{A-instances}\<close>

(*<*)
text\<open>Warning: If you make a request on attributes that are undefined in some instances,
you will get a result which includes these unresolved cases.
In the following example, we request the instances of the @{doc_class A}.
But we have defined an instance @{docitem \<open>sdf\<close>} in theory @{theory "Isabelle_DOF-Ontologies.Conceptual"}
whose our theory inherits from, and this docitem instance does not initialize its attribute \<^emph>\<open>x\<close>.
So in the request result we get an unresolved case because the evaluator can not get
the value of the \<^emph>\<open>x\<close> attribute of the instance @{docitem \<open>sdf\<close>}:\<close>
value*\<open>filter (\<lambda>\<sigma>. A.x \<sigma> > 5) @{A-instances}\<close>
(*>*)
section\<open>Limitations\<close>

text\<open>There are still some limitations.
The terms passed as arguments to a TA are not simplified \<open>before\<close> expansion
and their evaluation therefore fails:
\<close>

value\<open>@{thm (''HOL.re'' @ ''fl'')}\<close>
value-assert-error\<open>@{thm (''HOL.re'' @ ''fl'')}\<close>
                  \<open>wrong term format: must be string constant\<close>
value-assert-error\<open>@{thm ''HOL.refl''} = @{thm (''HOL.re'' @ ''fl'')}\<close>
                  \<open>wrong term format: must be string constant\<close>

text\<open>The type checking is unaware that a class is subclass of another one.
The @{doc_class "G"} is a subclass of the class @{doc_class "C"}, but one can not use it
to update the instance @{docitem \<open>xcv4\<close>}:
\<close>

update_instance-assert-error[xcv4::F, b+="{(@{A ''xcv3''},@{G ''xcv5''})}"]
                  \<open>type of attribute: Conceptual.F.b does not fit to term\<close>


section\<open>\<^theory_text>\<open>assert*\<close>-Annotated assertion-commands\<close>

text\<open>The \<^emph>\<open>assert*\<close>-command allows for logical statements to be checked in the global context.
Recall that it uses the same mechanism as the \<^emph>\<open>value*\<close>-command but requires that the evaluation 
reduces the argument term to true.
Consequently, it has the same limitations as \<^emph>\<open>value*\<close>.
\<close>

text\<open>Using the ontology defined in \<^theory>\<open>Isabelle_DOF-Unit-Tests.Concept_High_Level_Invariants\<close>
we can check logical statements:\<close>

term*\<open>authored_by @{introduction \<open>introduction2\<close>} = authored_by @{introduction \<open>introduction3\<close>}\<close>
assert*\<open>authored_by @{introduction \<open>introduction2\<close>} = authored_by @{introduction \<open>introduction3\<close>}\<close>
assert*\<open>\<not>(authored_by @{introduction \<open>introduction2\<close>}
          = authored_by @{introduction \<open>introduction4\<close>})\<close>

text\<open>Assertions must be boolean expressions, so the following assertion triggers an error:\<close>
(* Error:
assert*\<open>@{introduction \<open>introduction2\<close>}\<close>*)

text\<open>Assertions must be true, hence the error:\<close>
(* Error:
assert*\<open>{@{author \<open>curry\<close>}} = {@{author \<open>church\<close>}}\<close>*)

term*\<open>property @{result \<open>resultProof\<close>} = property @{result \<open>resultProof2\<close>}\<close>
assert*[assertionA::A]\<open>\<not> property @{result \<open>resultProof\<close>} = property @{result \<open>resultProof2\<close>}\<close>

(*<*)
text*[assertionAA::A]\<open>@{A "assertionA"}\<close> 
text\<open>... and here we reference @{A \<open>assertionA\<close>}.\<close>
(*>*)
assert*\<open>evidence @{result \<open>resultProof\<close>} = evidence @{result \<open>resultProof2\<close>}\<close>

text\<open>The optional evaluator of \<open>value*\<close> and \<open>assert*\<close> must be specified after the meta arguments:\<close>
value* [optional_test_A::A, x=6] [nbe] \<open>filter (\<lambda>\<sigma>. A.x \<sigma> > 5) @{A-instances}\<close>

assert* [resultProof3::result, evidence = "proof", property="[@{thm \<open>HOL.sym\<close>}]"] [nbe]
        \<open>evidence @{result \<open>resultProof3\<close>} = evidence @{result \<open>resultProof2\<close>}\<close>

end
