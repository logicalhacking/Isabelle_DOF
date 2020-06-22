(*************************************************************************
 * Copyright (C) 
 *               2019      The University of Exeter 
 *               2018-2019 The University of Paris-Saclay
 *               2018      The University of Sheffield
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

theory AssertLong
  imports Main
      keywords "assert" ::thy_decl

begin
  

  
  
ML\<open>

fun value_maybe_select some_name =
  case some_name
    of NONE => Value_Command.value
     | SOME name => Value_Command.value_select name;

val TT = Unsynchronized.ref (HOLogic.boolT);

fun value_cmd2 some_name modes raw_t state =
  let
    val ctxt = Toplevel.context_of state;
    val t = Syntax.read_term ctxt raw_t;
    val t' = value_maybe_select some_name ctxt t;
    val ty' = Term.type_of t';
    val t' = case ty' of @{typ "bool"} => t' | _ =>  error "Assertion expressions must be boolean.";
    val t' = case t' of @{term "True"} => t' | _ =>  error "Assertion failed.";
    val ctxt' = Variable.auto_fixes t' ctxt;
    val p = Print_Mode.with_modes modes (fn () =>
      Pretty.block [Pretty.quote (Syntax.pretty_term ctxt' t'), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt' ty')]) ();
  in Pretty.writeln p end;

\<close>
ML\<open>value_cmd2\<close>
definition ASSERT :: "bool \<Rightarrow> bool" where "ASSERT p == (p=True)"
ML\<open>val x = @{code "ASSERT"}\<close> 
ML\<open>
val opt_modes =
  Scan.optional (@{keyword "("} |-- Parse.!!! (Scan.repeat1 Parse.name --| @{keyword ")"})) [];

val opt_evaluator =
  Scan.option (@{keyword "["} |-- Parse.name --| @{keyword "]"})

val _ =
  Outer_Syntax.command @{command_keyword assert} "evaluate and print term"
    (opt_evaluator -- opt_modes -- Parse.term
      >> (fn ((some_name, modes), t) => 
             let val _ = writeln t in
              (* Toplevel.keep (Value_Command.value_cmd some_name modes (enclose "ASSERT(" ")" t)) *)
                Toplevel.keep (value_cmd2 some_name modes t) 
             end));
\<close>    

assert "True"
assert "True \<and> True "
ML\<open>!TT ;
      @{term "True"}\<close>
