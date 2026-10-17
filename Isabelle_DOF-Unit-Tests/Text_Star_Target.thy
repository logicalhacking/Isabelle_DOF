chapter\<open>Annotated text elements with a target: text* (in X)\<close>

theory Text_Star_Target
  imports
    "Isabelle_DOF_Unit_Tests_document"
    "Isabelle_DOF-Ontologies.Conceptual"
begin

locale L =
  fixes c :: nat
  assumes c_pos: "c > 0"

text\<open>Core reference behaviour: the text is checked in the context of \<^locale>\<open>L\<close>.\<close>
text (in L) \<open>Fact @{thm c_pos} about @{term c}.\<close>

text\<open>The same with an annotation. The meta-arguments are evaluated in the theory before the
command; the instance is global and visible after the command; the text is checked in L.\<close>
text* (in L) [t1::A, x = "3"] \<open>Fact @{thm c_pos} about @{term c}.\<close>

assert*\<open>A.x @{A \<open>t1\<close>} = 3\<close>

text\<open>Without target: unchanged behaviour.\<close>
text* [t2::A, x = "4"] \<open>No target.\<close>
assert*\<open>A.x @{A \<open>t2\<close>} = 4\<close>

text\<open>Headings and ontological macros take the target as well.\<close>
section* (in L) [s1] \<open>A heading checked in L: @{term c}\<close>

text\<open>Synchronous mode for debugging: the same commands, evaluated without forks.\<close>
declare [[invariants_parallel = false]]
text* (in L) [t3::A, x = "5"] \<open>@{thm c_pos}\<close>
assert*\<open>A.x @{A \<open>t3\<close>} = 5\<close>
declare [[invariants_parallel = true]]

end
