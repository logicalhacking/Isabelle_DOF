theory Example
  imports  "../../ontologies/CENELEC_50126"
  keywords "Term" :: diag 
begin

section{* Some show-off's of general antiquotations. *}

  
(* some show-off of standard anti-quotations: *) 
print_attributes
  print_antiquotations
text{*  @{thm refl}  of name @{thm [source] refl} 
        @{thm[mode=Rule] conjI}
        @{file "../../Isa_DOF.thy"} 
        @{value "3+4::int"} 
        @{const hd} 
        @{theory List}}
        @{term "3"} 
        @{type bool}  
        @{term [show_types] "f x = a + x"} *}
   


section{* Some Tests for Ontology Framework and its CENELEC Instance *}  

declare_reference [lalala::requirement, alpha="main", beta=42]

declare_reference [lalala::quod] (* shouldn't work *)

declare_reference [blablabla::cid, alpha="beta sdf", beta=gamma, delta=dfg_fgh\<^sub>1]
  
paragraph*[sdf]{* just a paragraph *}  
paragraph* [sdfk] \<open> just a paragraph - lexical variant \<close>  

subsection*[sdf]{* shouldn't work, multiple ref. *}  

section*[sedf::requirement, alpja= refl]{* works again. One can hover over the class constraint and 
                              jump to its definition. *}  
text\<open>\label{sedf}\<close>  (* Hack to make the LaTeX-ing running. Should disappear. *)
  
section*[seedf::test_case, dfg=34,fgdfg=zf]{* and another example with attribute setting,
but wrong doc_class constraint. *}  

section{* Text Antiquotation Infrastructure ... *}  
                  
text{* @{docref \<open>lalala\<close>} -- produces warning. *}  
text{* @{docref (unchecked) \<open>lalala\<close>} -- produces no warning. *}  

text{* @{docref \<open>ass122\<close>} -- global reference to a text-item in another file. *}

text{* @{ec \<open>ass122\<close>} -- global reference to a exported constraint in another file.
                         Note that the link is actually a srac, which, according to 
                         the ontology, happens to be an "ec".  *}

text{* @{test_specification \<open>ass122\<close>} -- wrong: "reference ontologically inconsistent". *}



text{* Here is a reference to @{docref \<open>sedf\<close>} *}    
(* works currently only in connection with the above label-hack. 
   Try to hover over the sedf - link and activate it !!! *)
 











  
section{* A Small Example for a Command Definition --- just to see how this works in principle. *}

ML{* 
val opt_modes =
  Scan.optional (@{keyword "("} |-- Parse.!!! (Scan.repeat1 Parse.name --| @{keyword ")"})) [];

val _ =
  Outer_Syntax.command @{command_keyword Term} "read and print term"
    (opt_modes -- Parse.term >> Isar_Cmd.print_term);

*}

lemma "True" by simp
  
Term "a + b = b + a"

term "a + b = b + a"  
  
section(in order){* sdfsdf*}  (* undocumented trouvaille when analysing the code *) 

  
end
  
    