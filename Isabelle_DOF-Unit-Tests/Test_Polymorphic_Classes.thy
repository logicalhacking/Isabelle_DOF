theory Test_Polymorphic_Classes
  imports Isabelle_DOF.Isa_DOF
          TestKit
begin

doc_class title =
  short_title :: "string option" <= "None"

doc_class Author =
  email :: "string" <= "''''"

datatype classification = SIL0 | SIL1 | SIL2 | SIL3 | SIL4

doc_class abstract =
  keywordlist :: "string list" <= "[]"
  safety_level :: "classification" <= "SIL3"

doc_class text_section =
  authored_by :: "Author set" <= "{}"
  level :: "int option" <= "None"

doc_class ('a::one, 'b, 'c) test0 = text_section +
  testa :: "'a list"
  testb :: "'b list"
  testc :: "'c list"

typ\<open>('a, 'b, 'c) test0\<close>
typ\<open>('a, 'b, 'c, 'd) test0_scheme\<close>

find_consts name:"test0"
find_theorems name:"test0"


doc_class 'a test1 = text_section +
  test1 :: "'a list"
   invariant author_finite_test :: "finite (authored_by \<sigma>)"
   invariant force_level_test :: "(level \<sigma>) \<noteq> None \<and> the (level \<sigma>) > 1"

find_consts name:"test1*inv"
find_theorems name:"test1*inv"

text*[church::Author, email="\<open>b\<close>"]\<open>\<close>
text\<open>@{Author "church"}\<close>
value*\<open>@{Author \<open>church\<close>}\<close>

text\<open>\<^value_>\<open>@{Author \<open>church\<close>}\<close>\<close>

doc_class ('a, 'b) test2 =  "'a test1" +
  test2 :: "'b list"
type_synonym ('a, 'b) test2_syn = "('a, 'b) test2"

find_theorems name:"test2"

declare [[invariants_checking_with_tactics]]
text*[testtest::"('a, int) test2", level = "Some 2", authored_by = "{@{Author \<open>church\<close>}}", test2 = "[1]"]\<open>\<close>
value*\<open>test2 @{test2 \<open>testtest\<close>}\<close>

text*[testtest2''::"(nat, int) test2", test1 = "[2::nat, 3]", test2 = "[4::int, 5]", level = "Some (2::int)"]\<open>\<close>
value*\<open>test1 @{test2 \<open>testtest2''\<close>}\<close>
declare [[invariants_checking_with_tactics = false]]

ML\<open>
val t = Syntax.parse_term \<^context> "@{test2 \<open>testtest\<close>}"

\<close>
ML\<open>
val t = \<^term>\<open>test2.make 8142730 Test_Parametric_Classes_2_test2_authored_by_Attribute_Not_Initialized Test_Parametric_Classes_2_test2_level_Attribute_Not_Initialized Test_Parametric_Classes_2_test2_test1_Attribute_Not_Initialized
                         Test_Parametric_Classes_2_test2_test2_Attribute_Not_Initialized
                        \<lparr>authored_by := bot, level := None\<rparr> \<close>
\<close>

text\<open>test2 = "[1::'a::one]" should be test2 = "[1::int]" because the type of testtest4 is ('a::one, int) test2:\<close>
text-assert-error[testtest4::"('a::one, int) test2", level = "Some 2", authored_by = "{@{Author \<open>church\<close>}}", test2 = "[1::'a::one]"]\<open>\<close>
  \<open>Type unification failed\<close>
text\<open>Indeed this definition fails:\<close>
definition-assert-error testtest2::"('a::one, int) test2" where "testtest2 \<equiv>
                  test2.make 11953346 
                  {@{Author \<open>church\<close>}}
                  (Some 2)
                  []
                  []
                  \<lparr>authored_by := bot
                      , level := None, level := Some 2
                      , authored_by := insert \<lparr>Author.tag_attribute = 11953164, email = []\<rparr> bot
                      , test2.test2 := [1::('a::one)]\<rparr> "
\<open>Type unification failed\<close>

text\<open>For now, no more support of type synonyms as parent:\<close>
doc_class ('a, 'b, 'c) A =
a :: "'a list"
b :: "'b list"
c :: "'c list"
type_synonym ('a, 'b, 'c) A_syn = "('a, 'b, 'c) A"

doc_class-assert-error ('a, 'b, 'c, 'd) B = "('b, 'c, 'd) A_syn" +
d ::"'a::one list" <= "[1]"
\<open>Undefined onto class: "A_syn"\<close>


declare[[invariants_checking_with_tactics]]

definition* testauthor0  where "testauthor0 \<equiv> \<lparr>Author.tag_attribute = 5, email = \<open>test_author_email\<close>\<rparr>"
definition* testauthor :: "Author" where "testauthor \<equiv> \<lparr>Author.tag_attribute = 5, email = \<open>test_author_email\<close>\<rparr>"
definition* testauthor2 :: "Author" where "testauthor2 \<equiv> \<lparr>Author.tag_attribute = 5, email = \<open>test_author_email\<close>\<rparr> \<lparr>email := \<open>test_author_email_2\<close> \<rparr>"
definition* testauthor3 :: "Author" where "testauthor3 \<equiv> testauthor \<lparr>email := \<open>test_author_email_2\<close> \<rparr>"

ML\<open>
val ctxt =  \<^context>
val input0 = Syntax.read_input "@{Author \<open>church\<close>}"
val source = Syntax.read_input "\<^term_>\<open>@{Author \<open>church\<close>}\<close>"
val input = source
val tt = Document_Output.output_document ctxt {markdown = false} input
\<close>

doc_class ('a, 'b) elaborate1 =
a :: "'a list"
b :: "'b list"

doc_class ('a, 'b) elaborate2 = 
c :: "('a, 'b) elaborate1 list"

doc_class ('a, 'b) elaborate3 = 
d :: "('a, 'b) elaborate2 list"

text*[test_elaborate1::"('a::one, 'b) elaborate1", a = "[1]"]\<open>\<close>

term*\<open>@{elaborate1 \<open>test_elaborate1\<close>}\<close>
value* [nbe]\<open>@{elaborate1 \<open>test_elaborate1\<close>}\<close> 


text*[test_elaborate2::"('a::one, 'b) elaborate2", c = "[@{elaborate1 \<open>test_elaborate1\<close>}]"]\<open>\<close>

text*[test_elaborate3::"('a::one, 'b) elaborate3", d = "[@{elaborate2 \<open>test_elaborate2\<close>}]"]\<open>\<close>

term*\<open>(concat o concat) ((map o map) a (map c (elaborate3.d @{elaborate3 \<open>test_elaborate3\<close>})))\<close>
value*\<open>(concat o concat) ((map o map) a (map c (elaborate3.d @{elaborate3 \<open>test_elaborate3\<close>})))\<close>


text\<open>
The term antiquotation is considered a ground term.
Then its type here is \<^typ>\<open>'a::one list\<close> with \<open>'a\<close> a fixed-type variable.
So the following definition only works because the parameter of the class is also \<open>'a\<close>.\<close>
declare[[ML_print_depth = 10000]]
doc_class 'a elaborate4 = 
d :: "'a::one list" <= "(concat o concat) ((map o map) a (map c (elaborate3.d @{elaborate3 \<open>test_elaborate3\<close>})))"
declare[[ML_print_depth = 20]]

declare[[ML_print_depth = 10000]]
text*[test_elaborate4::"'a::one elaborate4"]\<open>\<close>
declare[[ML_print_depth = 20]]


text\<open>Bug:
As the term antiquotation is considered as a ground term,
its type \<^typ>\<open>'a::one list\<close> conflicts with the type of the attribute \<^typ>\<open>int list\<close>.
To support the instantiation of the term antiquotation as an \<^typ>\<open>int list\<close>,
the term antiquotation should have the same behavior as a constant definition,
which is not the case for now.\<close>
declare[[ML_print_depth = 10000]]
doc_class-assert-error elaborate4' = 
d :: "int list" <= "(concat o concat) ((map o map) a (map c (elaborate3.d @{elaborate3 \<open>test_elaborate3\<close>})))"
\<open>Type unification failed\<close>
declare[[ML_print_depth = 20]]

text\<open>The behavior we want to support: \<close>

definition one_list :: "'a::one list" where "one_list \<equiv> [1]"

text\<open>the constant \<^const>\<open>one_list\<close> can be instantiate as an \<^typ>\<open>int list\<close>:\<close>
doc_class elaborate4'' = 
d :: "int list" <= "one_list"

declare[[ML_print_depth = 10000]]
text*[test_elaborate4''::"elaborate4''"]\<open>\<close>
declare[[ML_print_depth = 20]]


term*\<open>concat (map a (elaborate2.c @{elaborate2 \<open>test_elaborate2\<close>}))\<close>
value*\<open>concat (map a (elaborate2.c @{elaborate2 \<open>test_elaborate2\<close>}))\<close>

text\<open>
The term antiquotation is considered a ground term.
Then its type here is \<^typ>\<open>'a::one list\<close> with \<open>'a\<close> a fixed-type variable.
So the following definition only works because the parameter of the class is also \<open>'a\<close>.\<close>
declare[[ML_print_depth = 10000]]
doc_class 'a elaborate5 =
d :: "'a::one list" <= "concat (map a (elaborate2.c @{elaborate2 \<open>test_elaborate2\<close>}))"
declare[[ML_print_depth = 20]]

text\<open>Bug: But when defining an instance, as we use a \<open>'b\<close> variable to specify the type
of the instance (\<^typ>\<open>'b::one elaborate5\<close>, then the unification fails\<close>
declare[[ML_print_depth = 10000]]
text-assert-error[test_elaborate5::"'b::one elaborate5"]\<open>\<close>
\<open>Inconsistent sort constraints for type variable "'b"\<close>
declare[[ML_print_depth = 20]]

text\<open>Bug:
The term antiquotation is considered a ground term.
Then its type here is \<^typ>\<open>'a::one list\<close> with \<open>'a\<close> a fixed-type variable.
So it is not compatible with the type of the attribute \<^typ>\<open>'a::numeral list\<close>\<close>
doc_class-assert-error 'a elaborate5' =
d :: "'a::numeral list" <= "concat (map a (elaborate2.c @{elaborate2 \<open>test_elaborate2\<close>}))"
\<open>Sort constraint\<close>

text\<open>The behavior we want to support: \<close>

text\<open>the constant \<^const>\<open>one_list\<close> can be instantiate as an \<^typ>\<open>'a::numeral list\<close>:\<close>
doc_class 'a elaborate5'' = 
d :: "'a::numeral list" <= "one_list"


text*[test_elaborate1a::"('a::one, int) elaborate1", a = "[1]", b = "[2]"]\<open>\<close>

term*\<open>@{elaborate1 \<open>test_elaborate1a\<close>}\<close>
value* [nbe]\<open>@{elaborate1 \<open>test_elaborate1a\<close>}\<close> 

text*[test_elaborate2a::"('a::one, int) elaborate2", c = "[@{elaborate1 \<open>test_elaborate1a\<close>}]"]\<open>\<close>

text*[test_elaborate3a::"('a::one, int) elaborate3", d = "[@{elaborate2 \<open>test_elaborate2a\<close>}]"]\<open>\<close>

text\<open>
The term antiquotation is considered a ground term.
Then its type here is \<^typ>\<open>'a::one list\<close> with \<open>'a\<close> a fixed-type variable.
So the following definition only works because the parameter of the class is also \<open>'a\<close>.\<close>
definition* test_elaborate3_embedding ::"'a::one list"
  where "test_elaborate3_embedding \<equiv> (concat o concat) ((map o map) elaborate1.a (map elaborate2.c (elaborate3.d @{elaborate3 \<open>test_elaborate3a\<close>})))"

text\<open>Bug:
The term antiquotation is considered a ground term.
Then its type here is \<^typ>\<open>'a::one list\<close> with \<open>'a\<close> a fixed-type variable.
So it is not compatible with the specified type of the definition \<^typ>\<open>int list\<close>:\<close>
definition-assert-error test_elaborate3_embedding'::"int list"
  where "test_elaborate3_embedding' \<equiv> (concat o concat) ((map o map) elaborate1.a (map elaborate2.c (elaborate3.d @{elaborate3 \<open>test_elaborate3a\<close>})))"
\<open>Type unification failed\<close>

term*\<open>@{elaborate1 \<open>test_elaborate1a\<close>}\<close>
value* [nbe]\<open>@{elaborate1 \<open>test_elaborate1a\<close>}\<close>


record ('a, 'b) elaborate1' =
a :: "'a list"
b :: "'b list"

record ('a, 'b) elaborate2' = 
c :: "('a, 'b) elaborate1' list"

record ('a, 'b) elaborate3' = 
d :: "('a, 'b) elaborate2' list"

doc_class 'a one =
a::"'a list"

text*[test_one::"'a::one one", a = "[1]"]\<open>\<close>

value* [nbe] \<open>@{one \<open>test_one\<close>}\<close>

term*\<open>a @{one \<open>test_one\<close>}\<close>

text\<open>Bug:
The term antiquotation is considered a ground term.
Then its type here is \<^typ>\<open>'a::one list\<close> with \<open>'a\<close> a fixed-type variable.
So it is not compatible with the specified type of the definition \<^typ>\<open>('b::one, 'a::numeral) elaborate1'\<close>
because the term antiquotation can not be instantiate as a \<^typ>\<open>'b::one list\<close>
and the \<open>'a\<close> is checked against the \<open>'a::numeral\<close> instance type parameter:\<close>
definition-assert-error test_elaborate1'::"('b::one, 'a::numeral) elaborate1'"
  where "test_elaborate1' \<equiv> \<lparr> elaborate1'.a = a @{one \<open>test_one\<close>}, b = [2] \<rparr>"
\<open>Sort constraint\<close>

text\<open>This is the same behavior as the following:\<close>
definition-assert-error test_elaborate10::"('b::one, 'a::numeral) elaborate1'"
  where "test_elaborate10 \<equiv> \<lparr>  elaborate1'.a = [1::'a::one], b = [2] \<rparr>"
\<open>Sort constraint\<close>

definition-assert-error test_elaborate11::"('b::one, 'c::numeral) elaborate1'"
  where "test_elaborate11 \<equiv> \<lparr>  elaborate1'.a = [1::'a::one], b = [2] \<rparr>"
\<open>Type unification failed\<close>

text\<open>So this works:\<close>
definition* test_elaborate1''::"('a::one, 'b::numeral) elaborate1'"
  where "test_elaborate1'' \<equiv> \<lparr> elaborate1'.a = a @{one \<open>test_one\<close>}, b = [2] \<rparr>"

term \<open>elaborate1'.a test_elaborate1''\<close>
value [nbe] \<open>elaborate1'.a test_elaborate1''\<close>

text\<open>But if we embed the term antiquotation in a definition,
the type unification works:\<close>
definition* onedef where "onedef \<equiv> @{one \<open>test_one\<close>}"

definition test_elaborate1'''::"('b::one, 'a::numeral) elaborate1'"
  where "test_elaborate1''' \<equiv> \<lparr>  elaborate1'.a = a onedef, b = [2] \<rparr>"

value [nbe] \<open>elaborate1'.a test_elaborate1'''\<close>


definition test_elaborate2'::"(int, 'b::numeral) elaborate2'"
  where "test_elaborate2' \<equiv> \<lparr> c = [test_elaborate1''] \<rparr>"

definition test_elaborate3'::"(int, 'b::numeral) elaborate3'"
  where "test_elaborate3' \<equiv> \<lparr> d = [test_elaborate2'] \<rparr>"


doc_class 'a test3' =
test3 :: "int"
test3' :: "'a list"

text*[testtest30::"'a::one test3'", test3'="[1]"]\<open>\<close>
text-assert-error[testtest30::"'a test3'", test3'="[1]"]\<open>\<close>
\<open>Type unification failed: Variable\<close>

find_consts name:"test3'.test3"
definition testone :: "'a::one test3'" where "testone \<equiv> \<lparr>tag_attribute = 5, test3 = 3, test3' = [1] \<rparr>"
definition* testtwo :: "'a::one test3'" where "testtwo \<equiv> \<lparr>tag_attribute = 5, test3 = 1, test3' = [1] \<rparr>\<lparr> test3 := 1\<rparr>"

text*[testtest3'::"'a test3'", test3 = "1"]\<open>\<close>

declare [[show_sorts = false]]
definition* testtest30 :: "'a test3'" where "testtest30 \<equiv> \<lparr>tag_attribute = 12, test3 = 2, test3' = [] \<rparr>"
update_instance*[testtest3'::"'a test3'", test3 := "2"]

ML\<open>
val t = @{value_ [nbe] \<open>test3 @{test3' \<open>testtest3'\<close>}\<close>}
val tt = HOLogic.dest_number t
\<close>

text\<open>@{value_ [] [nbe] \<open>test3 @{test3' \<open>testtest3'\<close>}\<close>}\<close>

update_instance*[testtest3'::"'a test3'", test3 += "2"]

ML\<open>
val t = @{value_ [nbe] \<open>test3 @{test3' \<open>testtest3'\<close>}\<close>}
val tt = HOLogic.dest_number t
\<close>

value\<open>test3 \<lparr> tag_attribute = 1, test3 = 2, test3' = [2::int, 3] \<rparr>\<close>
value\<open>test3 \<lparr> tag_attribute = 1, test3 = 2, test3' = [2::int, 3] \<rparr>\<close>
find_consts name:"test3'.test3"

ML\<open>
val test_value = @{value_ \<open>@{test3' \<open>testtest3'\<close>}\<close>}

\<close>
declare [[show_sorts = false]]
update_instance*[testtest3'::"'a test3'", test3 += "3"]
declare [[show_sorts = false]]
value*\<open>test3 @{test3' \<open>testtest3'\<close>}\<close>
value\<open>test3 \<lparr> tag_attribute = 12, test3 = 5, test3' = AAAAAA\<rparr>\<close>

find_consts name:"test3'.test3"

text*[testtest3''::"int test3'", test3 = "1"]\<open>\<close>

update_instance*[testtest3''::"int test3'", test3' += "[3]"]

value*\<open>test3' @{test3' \<open>testtest3''\<close>}\<close>

update_instance*[testtest3''::"int test3'", test3' := "[3]"]

value*\<open>test3' @{test3' \<open>testtest3''\<close>}\<close>

update_instance*[testtest3''::"int test3'", test3' += "[2,5]"]

value*\<open>test3' @{test3' \<open>testtest3''\<close>}\<close>

definition testeq where "testeq \<equiv> \<lambda>x. x"
find_consts name:"test3'.ma"

text-assert-error[testtest3''::"int test3'", test3 = "1", test3' = "[3::'a::numeral]"]\<open>\<close>
  \<open>Type unification failed\<close>

text-assert-error[testtest3''::"int test3'", test3 = "1", test3' = "[3]"]\<open>\<close>
  \<open>Duplicate instance declaration\<close>


declare[[ML_print_depth = 10000]]
definition-assert-error testest3''' :: "int test3'"
  where "testest3''' \<equiv> \<lparr> tag_attribute = 12, test3 = 1, test3' = [2]\<rparr>\<lparr> test3' := [3::'a::numeral]\<rparr>"
\<open>Type unification failed\<close>
declare[[ML_print_depth = 20]]

value* \<open>test3 @{test3' \<open>testtest3''\<close>}\<close>
value* \<open>\<lparr> tag_attribute = 12, test3 = 1, test3' = [2]\<rparr>\<lparr> test3' := [3::int]\<rparr>\<close>
value* \<open>test3 (\<lparr> tag_attribute = 12, test3 = 1, test3' = [2]\<rparr>\<lparr> test3' := [3::int]\<rparr>)\<close>
term*\<open>@{test3' \<open>testtest3''\<close>}\<close>

ML\<open>val t = \<^term_>\<open>test3 @{test3' \<open>testtest3''\<close>}\<close>\<close>

value\<open>test3 \<lparr> tag_attribute = 12, test3 = 2, test3' =  [2::int ,3]\<rparr>\<close>

find_consts name:"test3'.test3"
find_consts name:"Isabelle_DOF_doc_class_test3'"
update_instance*[testtest3''::"int test3'", test3 := "2"]
ML\<open>
val t = @{value_ [nbe] \<open>test3 @{test3' \<open>testtest3''\<close>}\<close>}
val tt = HOLogic.dest_number t |> snd
\<close>

doc_class 'a testa =
a:: "'a set"
b:: "int set"

text*[testtesta::"'a testa", b = "{2}"]\<open>\<close>
update_instance*[testtesta::"'a testa", b += "{3}"]

ML\<open>
val t = @{value_ [nbe] \<open>b @{testa \<open>testtesta\<close>}\<close>}
val tt = HOLogic.dest_set t |> map (HOLogic.dest_number #> snd)
\<close>

update_instance-assert-error[testtesta::"'a::numeral testa", a := "{2::'a::numeral}"]
\<open>incompatible classes:'a Test_Polymorphic_Classes.testa:'a::numeral Test_Polymorphic_Classes.testa\<close>

text*[testtesta'::"'a::numeral testa", a = "{2}"]\<open>\<close>

update_instance*[testtesta'::"'a::numeral testa", a += "{3}"]

ML\<open>
val t = @{value_ [nbe] \<open>a @{testa \<open>testtesta'\<close>}\<close>}
\<close>

update_instance-assert-error[testtesta'::"'a::numeral testa", a += "{3::int}"]
  \<open>Type unification failed\<close>

definition-assert-error testtesta'' :: "'a::numeral testa"
  where "testtesta'' \<equiv> \<lparr>tag_attribute = 5, a = {1}, b = {1} \<rparr>\<lparr> a := {1::int}\<rparr>"
\<open>Type unification failed\<close>

update_instance*[testtesta'::"'a::numeral testa", b := "{3::int}"]
ML\<open>
val t = @{value_ [nbe] \<open>b @{testa \<open>testtesta'\<close>}\<close>}
\<close>

value* [nbe] \<open>b @{testa \<open>testtesta'\<close>}\<close>

definition testtesta'' :: "'a::numeral testa"
  where "testtesta'' \<equiv> \<lparr>tag_attribute = 5, a = {1}, b = {1} \<rparr>\<lparr> b := {2::int}\<rparr>"

value [nbe]\<open>b testtesta''\<close>

doc_class 'a test3 =
test3 :: "'a list"
type_synonym 'a test3_syn = "'a test3"

text*[testtest3::"int test3", test3 = "[1]"]\<open>\<close>
update_instance*[testtest3::"int test3", test3 := "[2]"]
ML\<open>
val t = \<^term_>\<open>test3 @{test3 \<open>testtest3\<close>}\<close>
val tt = \<^value_>\<open>test3 @{test3 \<open>testtest3\<close>}\<close> |> HOLogic.dest_list |> map HOLogic.dest_number
\<close>

update_instance*[testtest3::"int test3", test3 += "[3]"]
value*\<open>test3 @{test3 \<open>testtest3\<close>}\<close>


doc_class ('a, 'b) test4 =  "'a test3" +
  test4 :: "'b list"

definition-assert-error testtest0'::"('a::one, int) test4" where "testtest0' \<equiv>
                  test4.make 11953346 
                  [] [1::('a::one)]"
\<open>Type unification failed\<close>

definition-assert-error testtest0''::"('a, int) test4" where "testtest0'' \<equiv>
                  test4.make 11953346 
                   [1] Test_Parametric_Classes_2_test4_test4_Attribute_Not_Initialized"
\<open>Type unification failed\<close>

text\<open>Must fail because the equivalent definition
\<open>testtest0'\<close> below fails
due to the constraint in the where [1::('a::one)] is not an \<^typ>\<open>int list\<close>
but an \<^typ>\<open>'a::one list\<close> list \<close>
text-assert-error[testtest0::"('a::one, int) test4", test4 = "[1::'a::one]"]\<open>\<close>
\<open>Type unification failed\<close>
update_instance-assert-error[testtest0::"('a::one, int) test4"]
  \<open>Undefined instance: "testtest0"\<close>

value-assert-error\<open>@{test4 \<open>testtest0\<close>}\<close>\<open>Undefined instance: "testtest0"\<close>

definition testtest0''::"('a, int) test4" where "testtest0'' \<equiv>
                  \<lparr> tag_attribute = 11953346, test3 = [], test4 =  [1]\<rparr>\<lparr>test4 := [2]\<rparr>"

definition testtest0'''::"('a, int) test4" where "testtest0''' \<equiv>
                  \<lparr> tag_attribute = 11953346, test3 = [], test4 =  [1]\<rparr>\<lparr>test4 := [2]\<rparr>"


value [nbe] \<open>test3 testtest0''\<close>

type_synonym notion = string

doc_class Introduction = text_section +
  authored_by :: "Author set"  <= "UNIV" 
  uses :: "notion set"
  invariant author_finite :: "finite (authored_by \<sigma>)"
  and force_level :: "(level \<sigma>) \<noteq> None \<and> the (level \<sigma>) > 1"

doc_class claim = Introduction +
  based_on :: "notion list"

doc_class technical = text_section +
  formal_results :: "thm list" 

doc_class "definition" = technical +
  is_formal :: "bool"
  property  :: "term list" <= "[]" 

datatype kind = expert_opinion | argument | "proof"

doc_class result = technical +
  evidence :: kind
  property :: "thm list" <= "[]"
  invariant has_property :: "evidence \<sigma> = proof \<longleftrightarrow> property \<sigma> \<noteq> []"

doc_class example = technical +
  referring_to :: "(notion + definition) set" <= "{}"

doc_class conclusion = text_section +
  establish :: "(claim \<times> result) set"
  invariant establish_defined :: "\<forall> x. x \<in> Domain (establish \<sigma>)
                                           \<longrightarrow> (\<exists> y \<in> Range (establish \<sigma>). (x, y) \<in> establish \<sigma>)"

text\<open>Next we define some instances (docitems): \<close>

declare[[invariants_checking_with_tactics = true]]

text*[church1::Author, email="\<open>church@lambda.org\<close>"]\<open>\<close>

text*[resultProof::result, evidence = "proof", property="[@{thm \<open>HOL.refl\<close>}]"]\<open>\<close>
text*[resultArgument::result, evidence = "argument"]\<open>\<close>

text\<open>The invariants \<^theory_text>\<open>author_finite\<close> and \<^theory_text>\<open>establish_defined\<close> can not be checked directly
  and need a little help.
  We can set the \<open>invariants_checking_with_tactics\<close> theory attribute to help the checking.
  It will enable a basic tactic, using unfold and auto:\<close>

declare[[invariants_checking_with_tactics = true]]

text*[curry::Author, email="\<open>curry@lambda.org\<close>"]\<open>\<close>
text*[introduction2::Introduction, authored_by = "{@{Author \<open>church\<close>}}", level = "Some 2"]\<open>\<close>
(* When not commented, should violated the invariant:
update_instance*[introduction2::Introduction
                  , authored_by := "{@{Author \<open>church\<close>}}"
                  , level := "Some 1"]
*)

text*[introduction_test_parsed_elaborate::Introduction, authored_by = "authored_by @{Introduction \<open>introduction2\<close>}", level = "Some 2"]\<open>\<close>
term*\<open>authored_by @{Introduction \<open>introduction_test_parsed_elaborate\<close>}\<close>
value*\<open>authored_by @{Introduction \<open>introduction_test_parsed_elaborate\<close>}\<close>
text*[introduction3::Introduction, authored_by = "{@{Author \<open>church\<close>}}", level = "Some 2"]\<open>\<close>
text*[introduction4::Introduction, authored_by = "{@{Author \<open>curry\<close>}}", level = "Some 4"]\<open>\<close>

text*[resultProof2::result, evidence = "proof", property="[@{thm \<open>HOL.sym\<close>}]"]\<open>\<close>

text\<open>Then we can evaluate expressions with instances:\<close>

term*\<open>authored_by @{Introduction \<open>introduction2\<close>} = authored_by @{Introduction \<open>introduction3\<close>}\<close>
value*\<open>authored_by @{Introduction \<open>introduction2\<close>} = authored_by @{Introduction \<open>introduction3\<close>}\<close>
value*\<open>authored_by @{Introduction \<open>introduction2\<close>} = authored_by @{Introduction \<open>introduction4\<close>}\<close>

value*\<open>@{Introduction \<open>introduction2\<close>}\<close>

value*\<open>{@{Author \<open>curry\<close>}} = {@{Author \<open>church\<close>}}\<close>

term*\<open>property @{result \<open>resultProof\<close>} = property @{result \<open>resultProof2\<close>}\<close>
value*\<open>property @{result \<open>resultProof\<close>} = property @{result \<open>resultProof2\<close>}\<close>

value*\<open>evidence @{result \<open>resultProof\<close>} = evidence @{result \<open>resultProof2\<close>}\<close>

declare[[invariants_checking_with_tactics = false]]

declare[[invariants_strict_checking = false]]

doc_class test_A =
   level :: "int option"
   x :: int

doc_class test_B =
   level :: "int option"
   x :: "string"                            (* attributes live in their own name-space *)
   y :: "string list"          <= "[]"      (* and can have arbitrary type constructors *)
                                            (* LaTeX may have problems with this, though *)

text\<open>We may even use type-synonyms for class synonyms ...\<close>
type_synonym test_XX = test_B

doc_class test_C0 = test_B +                           
   z :: "test_A option"             <= None      (* A LINK, i.e. an attribute that has a type
                                               referring to a document class. Mathematical
                                               relations over document items can be modeled. *)
   g :: "thm"                               (* a reference to the proxy-type 'thm' allowing

                                               to denote references to theorems inside attributes *)


doc_class test_C = test_B +
   z :: "test_A option"             <= None      (* A LINK, i.e. an attribute that has a type
                                               referring to a document class. Mathematical
                                               relations over document items can be modeled. *)
   g :: "thm"                               (* a reference to the proxy-type 'thm' allowing

                                               to denote references to theorems inside attributes *)

datatype enum = X1 | X2 | X3                (* we add an enumeration type ... *)
 

doc_class test_D = test_B +
   x  :: "string"              <= "\<open>def \<longrightarrow>\<close>" (* overriding default *)
   a1 :: enum                  <= "X2"      (* class - definitions may be mixed 
                                               with arbitrary HOL-commands, thus 
                                               also local definitions of enumerations *)
   a2 :: int                   <= 0

doc_class test_E = test_D +
   x :: "string"              <= "''qed''"  (* overriding default *)

doc_class test_G = test_C +
   g :: "thm"  <= "@{thm \<open>HOL.refl\<close>}"  (* warning overriding attribute expected*)

doc_class 'a test_F  =     
   properties  :: "term list"
   r           :: "thm list"
   u           :: "file"
   s           :: "typ list"
   b           :: "(test_A \<times> 'a test_C_scheme) set"  <= "{}"       (* This is a relation link, roughly corresponding
                                                 to an association class. It can be used to track
                                                 claims to result - relations, for example.*) 
   b'          :: "(test_A \<times> 'a test_C_scheme) list"  <= "[]"
   invariant br :: "r \<sigma> \<noteq> [] \<and> card(b \<sigma>) \<ge> 3"
        and  br':: "r \<sigma> \<noteq> [] \<and> length(b' \<sigma>) \<ge> 3"
        and  cr :: "properties \<sigma> \<noteq> []"

lemma*[l::test_E] local_sample_lemma : 
       "@{thm \<open>refl\<close>} = @{thm ''refl''}" by simp
                                                       \<comment> \<open>un-evaluated references are similar to
                                                           uninterpreted constants. Not much is known
                                                           about them, but that doesn't mean that we
                                                           can't prove some basics over them...\<close>

text*[xcv1::test_A, x=5]\<open>Lorem ipsum ...\<close>
text*[xcv2::test_C, g="@{thm ''HOL.refl''}"]\<open>Lorem ipsum ...\<close>
text*[xcv3::test_A, x=7]\<open>Lorem ipsum ...\<close>

text\<open>Bug: For now, the implementation is no more compatible with the docitem term-antiquotation:\<close>
text-assert-error[xcv10::"unit test_F", r="[@{thm ''HOL.refl''}, 
                   @{thm \<open>local_sample_lemma\<close>}]", (* long names required *)
               b="{(@{docitem ''xcv1''},@{docitem \<open>xcv2\<close>})}",  (* notations \<open>...\<close> vs. ''...'' *)
               s="[@{typ \<open>int list\<close>}]",                        
               properties = "[@{term \<open>H \<longrightarrow> H\<close>}]"              (* notation \<open>...\<close> required for UTF8*)
]\<open>Lorem ipsum ...\<close>\<open>Type unification failed\<close>

text*[xcv11::"unit test_F", r="[@{thm ''HOL.refl''}, 
                   @{thm \<open>local_sample_lemma\<close>}]", (* long names required *)
               b="{(@{test_A ''xcv1''},@{test_C \<open>xcv2\<close>})}",  (* notations \<open>...\<close> vs. ''...'' *)
               s="[@{typ \<open>int list\<close>}]",                        
               properties = "[@{term \<open>H \<longrightarrow> H\<close>}]"              (* notation \<open>...\<close> required for UTF8*)
]\<open>Lorem ipsum ...\<close>

value*\<open>b @{test_F \<open>xcv11\<close>}\<close>

typ\<open>unit test_F\<close>

text*[xcv4::"unit test_F", r="[@{thm ''HOL.refl''}, 
                   @{thm \<open>local_sample_lemma\<close>}]", (* long names required *)
               b="{(@{test_A ''xcv1''},@{test_C \<open>xcv2\<close>})}",  (* notations \<open>...\<close> vs. ''...'' *)
               s="[@{typ \<open>int list\<close>}]",                        
               properties = "[@{term \<open>H \<longrightarrow> H\<close>}]"              (* notation \<open>...\<close> required for UTF8*)
]\<open>Lorem ipsum ...\<close>

value*\<open>b @{test_F \<open>xcv4\<close>}\<close>

text*[xcv5::test_G, g="@{thm \<open>HOL.sym\<close>}"]\<open>Lorem ipsum ...\<close>

update_instance*[xcv4::"unit test_F", b+="{(@{test_A ''xcv3''},@{test_C ''xcv2''})}"]

update_instance-assert-error[xcv4::"unit test_F", b+="{(@{test_A ''xcv3''},@{test_G ''xcv5''})}"]
  \<open>Type unification failed: Clash of types\<close>
                


typ\<open>unit test_G_ext\<close>
typ\<open>\<lparr>test_G.tag_attribute :: int\<rparr>\<close>
text*[xcv6::"\<lparr>test_G.tag_attribute :: int\<rparr> test_F", b="{(@{test_A ''xcv3''},@{test_G ''xcv5''})}"]\<open>\<close>


text\<open>\<open>lemma*\<close>, etc. do not support well polymorphic classes.
For now only embedded term-antiquotation in a definition could work:\<close>
definition* testtest_level where "testtest_level \<equiv> the (text_section.level @{test2 \<open>testtest2''\<close>})"
lemma*[e5::E] testtest : "xx + testtest_level = yy + testtest_level \<Longrightarrow> xx = yy" by simp

text\<open>Indeed this fails:\<close>
(*lemma*[e6::E] testtest : "xx + the (level @{test2 \<open>testtest2''\<close>}) = yy + the (level @{test2 \<open>testtest2''\<close>}) \<Longrightarrow> xx = yy" by simp*)

end