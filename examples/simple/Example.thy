theory Example
  imports  Isa_DOF
  keywords "Term" :: diag 
begin
  
section{* Some tests ... *}  

declare_reference [lalala::requirement, alpha="main", beta=42]

declare_reference [lalala::quod] (* shouldn't work *)

declare_reference [blablabla::cid, alpha=beta, beta=gamma]
  
paragraph*[sdf]{* just a paragraph *}  

subsection*[sdf]{* shouldn't work *}  

section*[sedf::requirement]{* works again *}  
  
section*[seedf::integration_test, dfg=34,fgdfg=zf]{* and another example with attribute setting *}  

section{* Text Antiquotation Infrastructure ... *}  
                  
text{* @{docref lalala} *}  

  
  
text{* @{thm refl} @{file "MOF.sml"} @{value 3} @{const hd} @{theory List}}
       @{term "3"} @{type bool}  @{term [show_types] "f x = a + x"} *}
  
text{* Here is a reference to @{docref sedf} *}    

  
  
section{* A Small Example for a Command Definition *}

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
  
    