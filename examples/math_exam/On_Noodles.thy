theory "On_Noodles"
  imports "../../ontologies/small_math"
          "../../ontologies/technical_report"
begin

open_monitor*[this::article]

title*[t1::title]\<open>On Noodles\<close> 

text*[simon::author]\<open>Simon Foster\<close>
text*[a::abstract, keywordlist = "[topology]"]
\<open>We present the first fundamental results on the goundbreaking theory of noodles...\<close>
section*[intro::introduction]\<open>Introduction\<close>

text\<open> Authorities say, that Noodles are unleavened dough which is stretched,
 extruded, or rolled flat and cut into one or a variety of shapes which usually 
include long, thin strips, or waves, helices, tubes, strings, or shells, or 
folded over, or cut into other shapes. Noodles are usually cooked in boiling water, 
sometimes with cooking oil or salt added. \<close>

section*[def_sec::technical]\<open>Basic definitions\<close>

text*[d1::"definition"]\<open>My first definition\<close>
definition noodle ::"bool" where "noodle = (THE x. True)" 

(*
update_instance*[def1, formal_results:="[@{thm ''noodle_def''}]"]
*)

close_monitor*[this::article]

end
