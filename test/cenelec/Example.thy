theory Example
  imports  "../../ontologies/CENELEC_50128"
begin

section{* Some show-off's of general antiquotations. *}

(* some show-off of standard anti-quotations: *) 
print_attributes
print_antiquotations

text\<open>  @{thm refl}  of name @{thm [source] refl} 
        @{thm[mode=Rule] conjI}
        @{file "../../Isa_DOF.thy"} 
        @{value "3+4::int"} 
        @{const hd} 
        @{theory List}}
        @{term "3"} 
        @{type bool}  
        @{term [show_types] "f x = a + x"} \<close>

section{* Example *}

text*[tralala] {* Brexit means Brexit *}
  
text*[ass1::assumption] {* Brexit means Brexit *}

text*[hyp1::hypothesis] {* P inequal NP *}
  
  
text*[ass122::srac] {* The overall sampling frequence of the odometer
subsystem is therefore 14 khz, which includes sampling, computing and
result communication times... *}
  
text*[t10::test_result] {* This is a meta-test. This could be an ML-command
that governs the external test-execution via, eg., a makefile or specific calls
to a test-environment or test-engine *}

text \<open> @{ec \<open>ass122\<close>}}\<close>

text \<open> As established by @{docref (unchecked) \<open>t10\<close>}, 
                         @{docref (define) \<open>t10\<close>} \<close>
text \<open> the               @{docref \<open>t10\<close>}                      
       as well as the    @{docref \<open>ass122\<close>}\<close>  
text \<open> represent a justification of the safety related applicability 
       condition @{srac \<open>ass122\<close>} aka exported constraint @{ec \<open>ass122\<close>}.       
     \<close>
  
text{*  And some ontologically inconsistent reference: @{hypothesis \<open>ass1\<close>} as well as  *} 
-- wrong

text{* ... some more ontologically inconsistent reference: @{assumption \<open>hyp1\<close>} as well as  *} 
-- wrong

  
  
text{* And a further ontologically totally inconsistent reference:
    @{test_result \<open>ass122\<close>} as well as ... *} 
-- wrong  
  
text{* the ontologically inconsistent reference: @{ec \<open>t10\<close>}  *} 
-- wrong  
  
  

section{* Some Tests for Ontology Framework and its CENELEC Instance *}  

declare_reference* [lalala::requirement, alpha="main", beta=42]

declare_reference* [lalala::quod] (* shouldn't work: multiple declaration *)

declare_reference* [blablabla::cid, alpha="beta sdf", beta=gamma, delta=dfg_fgh\<^sub>1]
  
paragraph*[sdf]{* just a paragraph *}  
paragraph* [sdfk] \<open> just a paragraph - lexical variant \<close>  

subsection*[sdf]{* shouldn't work, multiple ref. *}  
-- wrong

section*[sedf::requirement, alpja= refl]{* Shouldn't work - misspelled attribute. *}  
text\<open>\label{sedf}\<close>  (* Hack to make the LaTeX-ing running. Should disappear. *)
-- wrong

section*[seedf::test_case, dfg=34,fgdfg=zf]{* and another example with attribute setting,
but wrong doc_class constraint. *}  
-- wrong

section{* Text Antiquotation Infrastructure ... *}  
                  
text{* @{docref \<open>lalala\<close>} -- produces warning. *}  
text{* @{docref (unchecked) \<open>lalala\<close>} -- produces no warning. *}  

text{* @{docref \<open>ass122\<close>} -- global reference to a text-item in another file. *}

text{* @{ec \<open>ass122\<close>} -- global reference to a exported constraint in another file.
                         Note that the link is actually a srac, which, according to 
                         the ontology, happens to be an "ec".  *}

text{* @{test_specification \<open>ass122\<close>} -- wrong: "reference ontologically inconsistent". *}
-- wrong


text{* Here is a reference to @{docref \<open>sedf\<close>} *}    
(* shouldn't work: label exists, but definition was finally rejected to to errors. *)
 
check_doc_global (* shoudn't work : Unresolved forward references: lalala,blablabla *)
-- wrong

section \<open>Miscellaneous\<close> 
  
section(in order){* sdfsdf*}  (* undocumented trouvaille when analysing the code *) 

  
end
  
    