theory math_exam
 imports "../../DOF/Isa_COL"
begin
  
(*<<*)  
text\<open>In our scenario, content has four different types of addressees: 
\<^item> the @{emph \<open>setter\<close>}, i.e. the author of the exam, 
\<^item> the @{emph \<open>student\<close>}, i.e. the addressee of the exam, 
\<^item> the @{emph \<open>checker\<close>}, i.e. a person that checks the exam for
\<^item> the @{emph \<open>external\_examiner\<close>}, i.e. a person that checks the exam for
  feasibility and non-ambiguity.

Note that the latter quality assurance mechanism is used in many universities,
where for organizational reasons the execution of an exam takes place in facilities
where the author of the exam is not expected to be physically present.
\<close>  
  
  
datatype ContentClass =   
      setter            (* \<open>the 'author' of the exam\<close> *)
    | checker           (* \<open>the 'proof-reader' of the exam\<close> *)
    | externalExaminer  (* \<open>an external 'proof-reader' of the exam\<close> *)
    | student           (* \<open>the victim ;-) ... \<close> *)

  
doc_class Author =
   affiliation :: "string"
   email :: "string"

    
   
datatype Subject =
  algebra | geometry | statistical | analysis

datatype Level =
  oneStar | twoStars | threeStars

  
datatype Grade =
  A1 | A2 | A3


doc_class Exam_item = 
  level    :: "int option"
  concerns :: "ContentClass set"  

doc_class Header = Exam_item +
  examSubject :: "(Subject) list"
  date :: string
  timeAllowed :: int (*  minutes *)


type_synonym SubQuestion = string
 
doc_class Answer_Formal_Step =  Exam_item +
  justification :: string
  "term"        :: "string" 
  
doc_class Answer_YesNo =  Exam_item +
  step_label :: string
  yes_no     :: bool  (* \<open>for checkboxes\<close> *)

datatype Question_Type =   
  formal | informal | mixed 
  
doc_class Task = Exam_item +
  local_grade :: Level
  type        :: Question_Type
  subitems    :: "(SubQuestion * (Answer_Formal_Step list + Answer_YesNo)list) list"
  concerns    :: "ContentClass set" <= "{setter,student,checker,externalExaminer}" 
  mark        :: int
   

doc_class Exercise = Exam_item +
  content  :: "(Task) list"
  concerns :: "ContentClass set" <= "{setter,student,checker,externalExaminer}"


text\<open>In many institutions, it makes sense to have a rigorous process of validation
for exam subjects : is the initial question correct ? Is a proof in the sense of the
question possible ? We model the possibility that the @{term setter} validates a 
question by a sample proof validated by Isabelle. In our scenario this sample proofs
are completely @{emph \<open>intern\<close>}, i.e. not exposed to the students but just additional
material for the internal review process of the exam.\<close>
  
doc_class Validation = 
   tests  :: "term list"  <="[]"
   proofs :: "thm list"   <="[]"
  
doc_class Solution = Exam_item +
  content  :: "Exercise list"
  valids   :: "Validation list"
  concerns :: "ContentClass set" <= "{setter,checker,externalExaminer}"
  
doc_class MathExam =
  content :: "(Header + Author + Exercise) list"
  global_grade :: Grade 
  accepts "\<lbrace>Author\<rbrace>\<^sup>+  ~~  Header ~~  \<lbrace>Exercise ~~ Solution\<rbrace>\<^sup>+ "
  
(*>>*)
end
