(*<*)
theory "front"
  imports   "Isabelle_DOF.scholarly_paper"
            (* "Isabelle_DOF-Ontologies.document_templates" *)
            "HOL-CSP_OpSem.Conclusion"
begin


use_ontology "Isabelle_DOF.scholarly_paper" 
(* use_template "lipics-v2021-UNSUPPORTED" *)

open_monitor*[this::article]

declare[[strict_monitor_checking = false]]




(*>*)

title*[tit::title]\<open>An Operational Semantics in Isabelle/HOL-CSP\<close>

(*<*)
text*[stit::subtitle]\<open>Proving Parametric Properties in Isabelle/HOL-CSP2\<close> 
     (* doesn't work in lipics-style *)

author*[ben,
        email       = "''benoit.ballenghien@universite-paris-saclay.fr''",
        affiliation = "\<open>LMF, Université Paris-Saclay, Paris, France\<close>",
        orcid       = "''0009-0000-4941-187X''"]\<open>Benoît Ballenghien\<close>
author*[bu,
        email       = "''wolff@lmf.cnrs.fr''",
        affiliation = "\<open>LMF, Université Paris-Saclay, Paris, France\<close>",
        orcid       = "''0000-0002-9648-7663''"]\<open>Burkhart Wolff\<close>

(*>*)


text*[abs::abstract,
      keywordlist="[''Process-Algebra'',''Semantics'',''Concurrency'',''Computational Models'',
                    ''Theorem Proving'', ''Isabelle/HOL'']"]
\<open>  The theory of Communicating Sequential Processes going back to Hoare and Roscoe is still today 
   a reference model for concurrency. In the fairly rich literature, several versions of operational
   semantics have been discussed, which should be consistent with the denotational one.
   
   This work is based on Isabelle/HOL-CSP 2.0, a shallow embedding of the 
   failure-divergence model of denotational semantics proposed by Hoare, Roscoe and Brookes 
   in the eighties. In several ways, HOL-CSP is actually an extension of the original setting
   in the sense that it admits higher-order processes and infinite alphabets.  
   
   In this paper, we present a construction and formal equivalence proofs between
   operational CSP semantics and the underlying denotational failure-divergence semantics. 
   The construction is based on a \<^emph>\<open>definition\<close> of the operational transition operator
   \<open>P \<leadsto>\<^bsub>e\<^esub> P’\<close> basically via the \<open>After\<close> operator and the classical failure-divergence refinement.  

   Several choices are discussed to formally derive the operational semantics leading to subtle
   differences. The derived operational semantics for symbolic Labelled Transition Systems (LTSs) 
   can be potentially used for certifications of model-checker logs as well as combined proof 
   techniques.
%   This means that 
%   one can mix proofs based on bisimulation arguments with those from fixed point 
%   induction. More technically, our work paves the way to use model-checker-logs to construct an 
%   Isabelle proof. 
%
%   The formal proof work is quite substantial; the operational semantics is as large as HOL-CSP 
%   in terms of lines of code.
\<close>



(*<*)
end
(*>*) 
