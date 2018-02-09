theory Example
  imports  Isa_DOF CENELEC_50126
  keywords "Term" :: diag 
begin
  
section{* Some tests ... *}  

declare_reference [lalala::requirement, alpha="main", beta=42]

declare_reference [lalala::quod] (* shouldn't work *)

declare_reference [blablabla::cid, alpha=beta, beta=gamma]
  
paragraph*[sdf]{* just a paragraph *}  

subsection*[sdf]{* shouldn't work, multiple ref. *}  

section*[sedf::requirement]{* works again *}  
text\<open>\label{sedf}\<close>  (* Hack to make the LaTeX-ing running. Should disappear. *)
  
section*[seedf::test_case, dfg=34,fgdfg=zf]{* and another example with attribute setting,
but wrong doc_class constraint. *}  

section{* Text Antiquotation Infrastructure ... *}  
                  
text{* @{docref \<open>lalala\<close>} -- produces warning. *}  

text{* Here is a reference to @{docref \<open>sedf\<close>} *}    
(* works currently only in connection with the above label-hack. 
   Try to hover over the sedf - link and activate it !!! *)
 
  
(* some show-off of standard anti-quotations: *)  
text{* @{thm refl} @{file "MOF.sml"} @{value "3+4"} @{const hd} @{theory List}}
       @{term "3"} @{type bool}  @{term [show_types] "f x = a + x"} *}
  
 









  
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
  
    