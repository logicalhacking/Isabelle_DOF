theory Example
  imports  "../../ontologies/CENELEC_50126"
  keywords "Term" :: diag 
begin

section\<open> Some show-off's of general antiquotations : for demos. \<close>

  
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
   

section\<open> Example \<close>

text*[ass1::assumption] \<open> Brexit means Brexit \<close>

text*[hyp1::hypothesis] \<open> P means not P \<close>
  
  
text*[ass122::srac] \<open> The overall sampling frequence of the odometer
subsystem is therefore 14 khz, which includes sampling, computing and
result communication times... \<close>
  
text*[t10::test_result] \<open> This is a meta-test. This could be an ML-command
that governs the external test-execution via, eg., a makefile or specific calls
to a test-environment or test-engine \<close>


text \<open> As established by @{docref (unchecked) \<open>t10\<close>}, 
                         @{docref (define) \<open>t10\<close>}
       the               @{docref  \<open>t10\<close>}
       the               @{docref \<open>ass122\<close>}
     \<close>  
text \<open> safety related applicability condition @{srac \<open>ass122\<close>}.
       exported constraint @{ec \<open>ass122\<close>}.       
     \<close>
  
text\<open>
   And some ontologically inconsistent reference:
    @{hypothesis \<open>ass1\<close>} as well as 
    
\<close> 
-- "very wrong"

text\<open>
   And some ontologically inconsistent reference:
    @{assumption \<open>hyp1\<close>} as well as 
    
\<close>
-- "very wrong"

  
  
text\<open>
   And some ontologically inconsistent reference:
    @{test_result \<open>ass122\<close>} as well as 
    
\<close> 
-- wrong  
  
text\<open>
   And some other ontologically inconsistent reference:
    @{ec \<open>t10\<close>} as well as  
\<close> 
-- wrong  
  
  

section\<open> Some Tests for Ontology Framework and its CENELEC Instance \<close>  

declare_reference* [lalala::requirement, alpha="main", beta=42]

declare_reference* [lalala::quod] (* multiple declaration*)
-- wrong  

declare_reference* [blablabla::cid, alpha="beta sdf", beta=gamma, delta=dfg_fgh\<^sub>1]
  
paragraph*[sdf]\<open> just a paragraph \<close>  
paragraph* [sdfk] \<open> just a paragraph - lexical variant \<close>  

subsection*[sdf]\<open> shouldn't work, multiple ref. \<close>  
-- wrong

section*[sedf::requirement, long_name = "None::string option"]
        \<open> works again. One can hover over the class constraint and jump to its definition. \<close>  
  
section*[seedf::test_case, dfg=34,fgdfg=zf]\<open> and another example with undefined attributes. \<close>  
-- wrong

section\<open> Text Antiquotation Infrastructure ... \<close>  
                  
text\<open> @{docref \<open>lalala\<close>} -- produces warning. \<close>  
text\<open> @{docref (unchecked) \<open>lalala\<close>} -- produces no warning. \<close>  

text\<open> @{docref \<open>ass122\<close>} -- global reference to a text-item in another file. \<close>

text\<open> @{ec \<open>ass122\<close>} -- global reference to a exported constraint in another file.
                         Note that the link is actually a srac, which, according to 
                         the ontology, happens to be an "ec".  \<close>

text\<open> @{test_specification \<open>ass122\<close>} -- wrong: "reference ontologically inconsistent". \<close>



text\<open> Here is a reference to @{docref \<open>sedf\<close>} \<close>   
(* works currently only in connection with the above label-hack. 
   Try to hover over the sedf - link and activate it !!! *)
 











  
section\<open> A Small Example for Isar-support of a Command Definition --- for demos. \<close>

ML\<open> 

local 
      val opt_modes =  Scan.optional (@{keyword "("} 
                        |-- Parse.!!! (Scan.repeat1 Parse.name 
                        --| @{keyword ")"})) [];
in
      val _ =
        Outer_Syntax.command @{command_keyword Term} "read and print term"
          (opt_modes -- Parse.term >> Isar_Cmd.print_term);
end
\<close>

lemma "True" by simp
  
Term "a + b = b + a"

term "a + b = b + a"  




section(in order)\<open> sdfsdf \<close>  (* undocumented trouvaille when analysing the code *) 

  
end 
  
    