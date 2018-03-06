theory DOF_example
  imports  "../../CENELEC_50126"
begin

section{* Some show-off's of general antiquotations. *}

  
(* some show-off of standard anti-quotations: *)  
text{* @{thm refl} 
       @{file "../../Isa_DOF.thy"} 
       @{value "3+4::int"} 
       @{const hd} 
       @{theory List}
       @{term "3"} 
       @{type bool}  
       @{term [show_types] "f x = a + x"} *}
   


section{* Some Tests for Ontology Framework and its CENELEC Instance *}  

declare_reference [lalala::requirement, alpha="main", beta=42]

(* 
declare_reference [lalala::quod] (* shouldn't work *)
*)

declare_reference [blablabla::cid, alpha=beta, beta=gamma]
  
paragraph*[sdf]{* just a paragraph *}  
(*
subsection*[sdf]{* shouldn't work, multiple ref. *}  
*)
section*[sedf::requirement]{* works again. One can hover over the class constraint and 
                              jump to its definition. *}  
text\<open>\label{sedf}\<close>  (* Hack to make the LaTeX-ing running. Should disappear. *)
  
section*[seedf::test_case, dfg=34,fgdfg=zf]{* and another example with attribute setting,
but wrong doc_class constraint. *}  

section{* Text Antiquotation Infrastructure ... *}  
                  
text{* @{docref \<open>lalala\<close>} -- produces warning. *}  

text{* @{docref \<open>ass122\<close>} -- global reference to a text-item in another file. *}

text{* @{ec \<open>ass122\<close>} -- global reference to a exported constraint in another file.
                         Note that the link is actually a srac, which, according to 
                         the ontology, happens to be an "ec".  *}

(*
text{* @{test_specification \<open>ass122\<close>} -- wrong: "reference ontologically inconsistent". *}
*)


text{* Here is a reference to @{docref \<open>sedf\<close>} *}    
(* works currently only in connection with the above label-hack. 
   Try to hover over the sedf - link and activate it !!! *)
 

end
  
    
