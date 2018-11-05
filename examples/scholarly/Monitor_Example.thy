theory Monitor_Example
  imports "../../ontologies/scholarly_paper"
begin 


ML\<open>
val term = @{term "(title       ~~ 
                   \<lbrakk>subtitle\<rbrakk>    ~~
                   \<lbrace>author\<rbrace>\<^sup>+     ~~ 
                   abstract     ~~
                   introduction ~~ 
                   \<lbrace>technical || example\<rbrace>\<^sup>+ ~~ 
                   conclusion   ~~  
                   bibliography)"}
\<close>

ML\<open>
val alpha = (RegExpInterface.alphabet [term]);
val DA as (init,(next,fin)) = RegExpInterface.rexp_term2da  (RegExpInterface.alphabet [term]) term ;
RegExpChecker.accepts DA [0,2,3,4,5,6,7,8];
\<close>

ML\<open>
(* simulation with low-level interface RegExpChecker generated from AFP Functional Automata module*)
val S0 = init
val E1 = RegExpChecker.enabled DA S0 [0,1,2,3,4,5,6,7,8];
val S1 = next 0 init;
val E2 = RegExpChecker.enabled DA S1 [0,1,2,3,4,5,6,7,8];
val S2 = next 2 S1; (* uffz. it works. *)
val E3 = RegExpChecker.enabled DA S2 [0,1,2,3,4,5,6,7,8];
val S3 = next 3 S2; (* uffz. it works. *)
\<close>

ML\<open>
(* simulation with high-level interface RegExpInterface *)

RegExpInterface.enabled DA alpha;
val DA' = RegExpInterface.next DA alpha "scholarly_paper.title";
RegExpInterface.enabled DA' alpha;
val DA'' = RegExpInterface.next DA' alpha "scholarly_paper.author";
RegExpInterface.enabled DA'' alpha;
\<close>



end
