theory mathex_onto
 
imports "../Isa_DOF"
begin

doc_class Author =
   affiliation :: "string"
   email :: "string"

datatype Subject =
  algebra | geometry | statistical

datatype Level =
  oneStar | twoStars | threeStars

text{* In our scenario, content has three different types of addressees: 
\<^item> the @{emph \<open>examiner\<close>}, i.e. the author of the exam, 
\<^item> the @{emph \<open>student\<close>}, i.e. the addressee of the exam, 
\<^item> the @{emph \<open>validator\<close>}, i.e. a person that checks the exam for
  feasibility and non-ambiguity.

Note that the latter quality assurance mechanism is used in many universities,
where for organizational reasons the execution of an exam takes place in facilities
where the author of the exam is not expected to be physically present.
 *}  
  
  
datatype Grade =
  A1 | A2 | A3

doc_class Header = 
  examTitle :: string
  examSubject :: Subject
  date :: string
  timeAllowed :: int --  minutes

datatype ContentClass =   
    examiner    -- \<open>the 'author' of the exam\<close>
    | validator -- \<open>the 'proof-reader' of the exam\<close>
    | student   -- \<open>the victim ;-) ... \<close>

doc_class Exam_item = 
  concerns :: "ContentClass set"  

datatype SubQuestion = Item string
 
doc_class Answer_Formal =  Exam_item +
  step_label :: string
  "term"     :: "string" 
  
doc_class Answer_YesNo =  Exam_item +
  step_label :: string
  yes_no     :: bool  -- \<open>for checkboxes\<close>

datatype Question_Type =   
  formal | informal | mixed 
  
doc_class Question = Exam_item +
  level    :: Level
  type     :: Question_Type
  subitems :: "(SubQuestion * (Answer_Formal + Answer_YesNo)list) list"
  concerns :: "ContentClass set" <= "{examiner,validator,student}" 
  mark     :: int
   

doc_class Exercise = Exam_item +
  content  :: "(Question) list"
  concerns :: "ContentClass set" <= "{examiner,validator,student}" 


text{* In many institutions, it makes sense to have a rigorous process of validation
for exam subjects : is the initial question correct ? Is a proof in the sense of the
question possible ? We model the possibility that the @{term examiner} validates a 
question by a sample proof validated by Isabelle. In our scenario this sample proofs
are completely @{emph \<open>intern\<close>}, i.e. not exposed to the students but just additional
material for the internal review process of the exam.*}
  
doc_class Validation = 
   tests  :: "term list"  <="[]"
   proofs :: "thm list"   <="[]"
  
doc_class Solution = Exam_item +
  content  :: "Question list"
  valids   :: "Validation list"
  concerns :: "ContentClass set" <= "{examiner,validator}" 
  
doc_class MathExam=
  content :: "(Header + Author + Exercise) list"
  global_grade :: Grade 
  where "((Author)+  ~
          Header ~ 
         (Exercise ~ Solution)+ )"

end