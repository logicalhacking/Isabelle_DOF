theory OntoMathPro_Ontology
  imports "Isabelle_DOF.Isa_DOF"
begin

datatype dc = creator string | title string

datatype owl =
    backwardCompatibleWith string
  | deprecated string
  | incompatibleWith string
  | priorVersion string
  | versionInfo string
  
datatype rdfs =
    comment string
  | isDefinedBy string
  | label string
  | seeAlso string

datatype annotation = DC dc | OWL owl |  RDFS rdfs


onto_class Top =
  Annotations :: "annotation list"

onto_class Field_of_mathematics =
  Annotations :: "annotation list"
  invariant restrict_annotation_F ::"set (Annotations \<sigma>) \<subseteq>
                                              range (RDFS o label) \<union> range (RDFS o comment)"

onto_class Mathematical_knowledge_object =
  Annotations :: "annotation list"
  invariant restrict_annotation_M ::"set (Annotations \<sigma>) \<subseteq>
                                              range (RDFS o label) \<union> range (RDFS o comment)"

onto_class assoc_F_M =
  contains:: "(Field_of_mathematics \<times> Mathematical_knowledge_object) set"
  invariant contains_defined :: "\<forall> x. x \<in> Domain (contains \<sigma>)
                                              \<longrightarrow> (\<exists> y \<in> Range (contains \<sigma>). (x, y) \<in> contains \<sigma>)"

onto_class assoc_M_F =
  belongs_to :: "(Mathematical_knowledge_object \<times> Field_of_mathematics) set"
  invariant belong_to_defined :: "\<forall> x. x \<in> Domain (belongs_to \<sigma>)
                                           \<longrightarrow> (\<exists> y \<in> Range (belongs_to \<sigma>). (x, y) \<in> belongs_to \<sigma>)"

onto_class assoc_M_M =
  is_defined_by :: "(Mathematical_knowledge_object \<times> Mathematical_knowledge_object) set"
  invariant is_defined_by_defined :: "\<forall> x. x \<in> Domain (is_defined_by \<sigma>)
                                    \<longrightarrow> (\<exists> y \<in> Range (is_defined_by \<sigma>). (x, y) \<in> is_defined_by \<sigma>)"

onto_class assoc_M_M' =
  "defines" :: "(Mathematical_knowledge_object \<times> Mathematical_knowledge_object) set"
  invariant defines_defined :: "\<forall> x. x \<in> Domain (defines \<sigma>)
                                    \<longrightarrow> (\<exists> y \<in> Range (defines \<sigma>). (x, y) \<in> defines \<sigma>)"

onto_class assoc_M_M_see_also =
  see_also :: "(Mathematical_knowledge_object rel) set" 
  invariant see_also_trans :: "\<forall> r \<in> (see_also \<sigma>). trans r"
  invariant see_also_sym :: "\<forall> r \<in> (see_also \<sigma>). sym r"

onto_class Problem = Mathematical_knowledge_object +
  Annotations :: "annotation list"
  
onto_class Method = Mathematical_knowledge_object +
  Annotations :: "annotation list"

onto_class assoc_Problem_Method =
  is_solved_by :: "(Problem \<times> Method) set"
  invariant is_solved_by_defined :: "\<forall> x. x \<in> Domain (is_solved_by \<sigma>)
                                    \<longrightarrow> (\<exists> y \<in> Range (is_solved_by \<sigma>). (x, y) \<in> is_solved_by \<sigma>)"

onto_class assoc_Method_Problem =
  solves :: "(Method \<times> Problem) set"
  invariant solves_defined :: "\<forall> x. x \<in> Domain (solves \<sigma>)
                                    \<longrightarrow> (\<exists> y \<in> Range (solves \<sigma>). (x, y) \<in> solves \<sigma>)"
