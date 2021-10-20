chapter\<open>Evaluation\<close>

text\<open>Term Annotation Antiquotations (TA) can be evaluated with the help of the value* command.\<close>

theory 
  Evaluation
imports 
  "Isabelle_DOF-tests.TermAntiquotations"
begin

text\<open>The value* command uses the same code as the value command
and adds the possibility to evaluate Term Annotation Antiquotations (TA).
For that an elaboration of the term referenced by a TA must be done before
passing it to the evaluator.
The current implementation is really basic:
\<^item> For the built-ins, the term referenced by the TA is returned
  as it is;
\<^item> For an instance class, the value of the instance is returned.
The emphasis of this presentation is to present the evaluation possibilities and limitations
of the current implementation.
\<close>

text\<open>

case : attribute not initialized

\<close>

text\<open>We can validate a term with TA:\<close>
term*\<open>@{thm \<open>HOL.refl\<close>}\<close>

text\<open>Now we can evaluate a term with TA:
the current implementation return the term which references the object referenced by the TA.
Here the evualuation of the TA will return the HOL.String which references the theorem:
\<close>
value*\<open>@{thm \<open>HOL.refl\<close>}\<close>

text\<open>An instance class is an object which allows us to define the concepts we want in an ontology.
It is a concept which will be used to implement an ontology. It has roughly the same meaning as
an individual in an OWL ontology.
The validation process will check that the instance class @{docitem \<open>xcv1\<close>} is indeed
an instance of the class @{doc_class A}:
\<close>
term*\<open>@{A \<open>xcv1\<close>}\<close>

text\<open>The instance class @{docitem \<open>xcv1\<close>} is not an instance of the class B:
\<close>
(* Error:
term*\<open>@{B \<open>xcv1\<close>}\<close>*)

text\<open>We can evaluate the instance class. The current implementation returns
the value of the instance, i.e. a collection of every attribute of the instance: 
\<close>
value*\<open>@{A \<open>xcv1\<close>}\<close>

text\<open>We can also get the value of an attribute of the instance:\<close>
value*\<open>A.x @{A \<open>xcv1\<close>}\<close>

ML\<open> 
val {docobj_tab={tab = x, ...},docclass_tab, ISA_transformer_tab,...} = DOF_core.get_data @{context}; 
     Symtab.dest ISA_transformer_tab; 
\<close>

text\<open>If the attribute of the instance is not initialized, we get an undefined value,
whose type is the type of the attribute:\<close>
term*\<open>level @{C \<open>xcv2\<close>}\<close>
value*\<open>level @{C \<open>xcv2\<close>}\<close>

text\<open>The value of a TA is the term itself:\<close>
term*\<open>C.g @{C \<open>xcv2\<close>}\<close>
value*\<open>C.g @{C \<open>xcv2\<close>}\<close>

text\<open>Some terms can be validated, i.e. the term will be checked,
 and the existence of every object referenced by a TA will be checked,
but can not be evaluated, i.e. the elaboration of the TA to be evaluated will fail.
The existence of the instance @{docitem \<open>xcv4\<close>} can be validated,
and the fact that it is an instance of the class @{doc_class F} } will be checked:\<close>
term*\<open>@{F \<open>xcv4\<close>}\<close>

text\<open>But the evaluation will fail with the current implementation.
The attribute \<open>b\<close> of the instance @{docitem \<open>xcv4\<close>} is of type @{typ "(A \<times> C) set"}
and then the elements of the set must have equivalence properties,
i.e. definitions for the equality.
But the current definition does not define equality for TA.
So the attribute \<open>g\<close> of the class @{doc_class C}, which is a @{typ "thm"},
does not have a definition for the equality and the evaluation of the set fails:
\<close>
(* Error:
value* \<open>@{F \<open>xcv4\<close>}\<close>*)

text\<open>Because we do not keep necessarily the same type for the TA and the term referenced
by the TA, evaluation may fail due to type mismatch.
Here, we have a list of @{typ "thm"}, but after the elaboration,
the theorem become an HOL string with type @{typ "char list"} and then
does not match the list type\<close>
(* Error:
value*\<open>[@{thm \<open>HOL.refl\<close>}, @{thm \<open>HOL.refl\<close>}]\<close>*)

end