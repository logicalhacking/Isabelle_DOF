(* Little theory implementing the an assertion command in Isabelle/HOL. *)

theory Assert
  imports Main
      keywords "assert" ::thy_decl

begin
  
  
ML{*

(* Reimplementation needed because not exported from ML structure Value_Command *)
fun value_maybe_select some_name =
  case some_name
    of NONE => Value_Command.value
     | SOME name => Value_Command.value_select name;

(* Reimplementation  structure Value_Command due to tiny modification of value_cmd. *)

fun assert_cmd some_name modes raw_t state =
  let
    val ctxt = Toplevel.context_of state;
    val t = Syntax.read_term ctxt raw_t;
    val t'  = value_maybe_select some_name ctxt t;
    val ty' = Term.type_of t';
    val ty' = case ty' of @{typ "bool"} => ty' | _ =>  error "Assertion expressions must be boolean.";
    val t'  = case t' of @{term "True"} => t' | _ =>  error "Assertion failed.";
    val ctxt' = Variable.auto_fixes t' ctxt;
    val p = Print_Mode.with_modes modes (fn () =>
      Pretty.block [Pretty.quote (Syntax.pretty_term ctxt' t'), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt' ty')]) ();
  in Pretty.writeln p end;

*}

ML{*
(* Reimplementation needed because not exported from ML structure Value_Command *)
val opt_modes =
  Scan.optional (@{keyword "("} |-- Parse.!!! (Scan.repeat1 Parse.name --| @{keyword ")"})) [];

(* Reimplementation needed because not exported from ML structure Value_Command *)
val opt_evaluator =
  Scan.option (@{keyword "["} |-- Parse.name --| @{keyword "]"})

(* NEW *)
val _ =
  Outer_Syntax.command @{command_keyword assert} "evaluate and print term"
    (opt_evaluator -- opt_modes -- Parse.term
      >> (fn ((some_name, modes), t) =>   Toplevel.keep (assert_cmd some_name modes t) ));
*} 

  
(* Test: 
   
 assert ""
 assert "3 = 4"
 assert "False"
 assert "5 * 5 = 25 "

*)
  
assert "True \<and> True "

assert "(5::int) * 5 = 25 "

  
end  
  