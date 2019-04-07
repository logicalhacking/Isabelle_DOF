
theory mini_odo
  imports  "Isabelle_DOF.CENELEC_50128" 
           "Isabelle_DOF.scholarly_paper"
begin

section\<open> Some examples of Isabelle's standard antiquotations. \<close>
(* some show-off of standard anti-quotations: *) 
text \<open>THIS IS A TEXT\<close>

text\<open>  @{thm refl}  of name @{thm [source] refl} 
        @{thm[mode=Rule] conjI}
        @{file "mini_odo.thy"} 
        @{value "3+4::int"} 
        @{const hd} 
        @{theory List}
        @{term "3"} 
        @{type bool}  
        @{term [show_types] "f x = a + x"} \<close>




section\<open> Core Examples for stating text-elements as doc-items.\<close>

text\<open>An "anonymous" text-item, automatically coerced into the top-class "text".\<close>
text*[tralala] \<open> Brexit means Brexit \<close> 

text\<open>Examples for declaration of typed doc-items "assumption" and "hypothesis",
     concepts defined in the underlying ontology @{theory "CENELEC_50128"}. \<close>
text*[ass1::assumption] \<open> The subsystem Y is safe. \<close>
text*[hyp1::hypothesis] \<open> P not equal NP \<close>
  
text\<open>A real example fragment from a larger project, declaring a text-element as a
     "safety-related application condition", a concept defined in the  @{theory "CENELEC_50128"}
     ontology:\<close>  

text*[new_ass::hypothesis]\<open>Under the assumption @{assumption \<open>ass1\<close>} we establish the following: ... \<close>

text*[ass122::SRAC] \<open> The overall sampling frequence of the odometer
subsystem is therefore 14 khz, which includes sampling, computing and
result communication times... \<close>
  
text*[t10::test_result] \<open> This is a meta-test. This could be an ML-command
that governs the external test-execution via, eg., a makefile or specific calls
to a test-environment or test-engine \<close>


section\<open> References to doc-items.\<close>
text\<open>Finally some examples of references to doc-items, i.e. text-elements with declared 
     meta-information and status. \<close> 
text \<open> As established by @{docref (unchecked) \<open>t10\<close>}, 
                         @{docref (define) \<open>t10\<close>} \<close>
text \<open> the               @{docref \<open>t10\<close>}                      
       as well as the    @{docref \<open>ass122\<close>}\<close>  
text \<open> represent a justification of the safety related applicability 
       condition @{SRAC \<open>ass122\<close>} aka exported constraint @{EC \<open>ass122\<close>}.\<close> 




section\<open> Some Tests for Ontology Framework and its CENELEC Instance \<close>  
                                                  
declare_reference* [lalala::requirement, alpha="main", beta=42]
declare_reference* [blablabla::cid, alpha="beta sdf", beta=gamma, delta=dfg_fgh\<^sub>1]


section*[h::example]\<open> Some global inspection commands for the status of docitem and 
                      doc-class tables ... \<close>  


section*[i::example]\<open> Text Antiquotation Infrastructure ... \<close>  
                 
(*<*)
text\<open> @{docitem \<open>lalala\<close>}   -- produces warning. \<close>  
text\<open> @{docitem (unchecked) \<open>lalala\<close>} -- produces no warning. \<close>  
(*>*)

text\<open> @{docitem \<open>ass122\<close>} -- global reference to a text-item in another file. \<close>

text\<open> @{EC \<open>ass122\<close>} -- global reference to a exported constraint in another file.
                         Note that the link is actually a srac, which, according to 
                         the ontology, happens to be an "ec".  \<close>
   

  
end
  
    
