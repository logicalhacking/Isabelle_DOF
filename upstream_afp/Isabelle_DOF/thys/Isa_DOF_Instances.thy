(*************************************************************************
 * Copyright (C) 
 *               2019-2022 The University of Exeter 
 *               2018-2022 The University of Paris-Saclay
 *               2018      The University of Sheffield
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

chapter \<open>The Document Ontology Framework: Instances of Document Classes\<close>

text\<open> The parser of the meta-arguments, the evaluation of terms, and the creation of instances of document classes with their terms, monitors and invariants. \<close>

theory Isa_DOF_Instances   (* Instances *)
  imports Isa_DOF_TA
  keywords "+=" ":="
           and "term*" "value*" "assert*"                  :: document_body
begin

section\<open> Syntax for Annotated Documentation Commands (the '' View'' Part I) \<close>

ML\<open>
structure ODL_Meta_Args_Parser = 
struct

type meta_args_t = (binding * (string * Position.T) option)
                   * ((string * Position.T) * string) list

val empty_meta_args = ((Binding.empty, NONE), [])

val is_improper = not o (Token.is_proper orf Token.is_begin_ignore orf Token.is_end_ignore);
val improper = Scan.many is_improper; (* parses white-space and comments *)

val attribute =
    Parse.position Parse.const
    --| improper 
    -- Scan.optional (Parse.$$$ "=" --| improper |-- Parse.!!! Parse.term --| improper) "True"
   : ((string * Position.T) * string) parser;

val attribute_upd  : (((string * Position.T) * string) * string) parser =
    Parse.position Parse.const 
    --| improper
    -- ((@{keyword "+="} --| improper) || (@{keyword ":="} --| improper))
    -- Parse.!!! Parse.term
    --| improper
    : (((string * Position.T) * string) * string) parser;

val reference =
    Parse.binding
    --| improper
    -- Scan.option (Parse.$$$ "::" 
                    -- improper 
                    |-- (Parse.!!! (Parse.position Parse.name))
                    ) 
    --| improper;

val attributes =  
    ((Parse.$$$ "["
      -- improper 
     |-- (reference -- 
         (Scan.optional(Parse.$$$ "," -- improper |-- (Parse.enum "," (improper |-- attribute)))) []))
     --| Parse.$$$ "]"
     --| improper)  : meta_args_t parser

val opt_attributes = Scan.optional attributes empty_meta_args

val attributes_upd =  
    ((Parse.$$$ "[" 
     -- improper 
     |-- (reference -- 
         (Scan.optional(Parse.$$$ "," -- improper |-- (Parse.enum "," (improper |-- attribute_upd)))) []))
     --| Parse.$$$ "]")
     --| improper

end (* structure ODL_Meta_Args_Parser *)
\<close>

ML\<open>
(* c.f. \<^file>\<open>~~/src/HOL/Tools/value_command.ML\<close> *)
(*
  The value* command uses the same code as the value command
  and adds the evaluation Term Annotation Antiquotations (TA)
  with the help of the DOF_core.transduce_term_global function.
*)
(*  Based on:
    Title:      HOL/Tools/value_command.ML
    Author:     Florian Haftmann, TU Muenchen

Generic value command for arbitrary evaluators, with default using nbe or SML.
*)

(*signature VALUE_COMMAND =
sig
  val value: Proof.context -> term -> term
  val value_without_elaboration: Proof.context -> term -> term
  val value_select: string -> Proof.context -> term -> term
  val value_cmd:  {assert: bool} -> ODL_Command_Parser.meta_args_t option ->
                  string ->  string list ->  string -> Position.T
                  -> theory -> theory
   val add_evaluator: binding * (Proof.context -> term -> term) 
                  -> theory -> string * theory
end;*)


structure DOF_Value_Cmd (*: VALUE_COMMAND*) =
struct

structure Evaluators = Theory_Data
(
  type T = (Proof.context -> term -> term) Name_Space.table;
  val empty = Name_Space.empty_table "evaluator";
  val merge = Name_Space.merge_tables;
)

fun add_evaluator (b, evaluator) thy =
  let
    val (name, tab') = Name_Space.define (Context.Theory thy) true
      (b, evaluator) (Evaluators.get thy);
    val thy' = Evaluators.put tab' thy;
  in (name, thy') end;

fun intern_evaluator thy raw_name =
  if raw_name = "" then ""
  else Name_Space.intern (Name_Space.space_of_table
    (Evaluators.get (thy))) raw_name;

fun default_value ctxt t =
  if null (Term.add_frees t [])
  then Code_Evaluation.dynamic_value_strict ctxt t
  else Nbe.dynamic_value ctxt t;

fun value_select name ctxt =
  if name = ""
  then default_value ctxt
  else Name_Space.get (Evaluators.get (Proof_Context.theory_of ctxt)) name ctxt;

fun value_select' raw_name ctxt raw_t =
  let val thy = Proof_Context.theory_of ctxt
      val t = Syntax.parse_term ctxt raw_t;
      val t' = DOF_core.elaborate_term' ctxt t
      val t'' = Syntax.check_term ctxt t'
  in
    if raw_name = ""
    then t'' |> default_value ctxt
    else let val name = intern_evaluator thy raw_name
         in t'' |> Name_Space.get (Evaluators.get thy) name ctxt
         end
    end

val value = value_select ""

val value_without_elaboration = value_select ""

(* The terms of an instance: its default object and the update by the attributes. *)
structure Instance_Terms =
struct local open DOF_core in

fun create_default_object thy binding class_name typ = 
  let
    val purified_class_name = String.translate (fn #"." => "_" | x => String.implode [x]) class_name
    fun attr_to_s (binding, _, _) = purified_class_name ^ "_"
                                      ^ (Binding.name_of binding)
                                      ^ "_Attribute_Not_Initialized"
    val class_list = get_attributes class_name thy
    fun attrs_filter [] = [] 
      | attrs_filter (x::xs) =
          let val (cid, ys) = x
              fun is_duplicated _ [] = false
                | is_duplicated y (x::xs) =
                    let val (_, ys) = x
                    in if ys |> exists (fn x => (x,y) |> apply2 (#1 #> Binding.name_of)
                                                      |> uncurry equal)
                       then true
                       else is_duplicated y xs end
          in (cid, filter_out (fn y => is_duplicated y xs) ys)::attrs_filter xs end
    val class_list' = rev (attrs_filter (rev class_list))
    val tag_attr_s = serial () |> string_of_int
    fun trans_attr thy trans tag_attr  (cid, filtered_attr_list) =
      if virtual_of cid thy |> #virtual
      then (tag_attr)::(map (trans) filtered_attr_list)
      else (map (trans) filtered_attr_list)
    val test_class = class_list' |> map (trans_attr thy (attr_to_s) tag_attr_s)
                                 |> flat
                                 |> cons tag_attr_s
    val term = test_class |> cons (Long_Name.qualify class_name makeN) |> space_implode Symbol.space
    val ctxt = Proof_Context.init_global thy
    val term' = term |> Syntax.parse_term ctxt |> elaborate_term' ctxt
    val parsed_prop = Const (\<^const_name>\<open>Pure.eq\<close>, dummyT) $ Free (Binding.name_of binding, dummyT) $ term'
    val raw_vars = [(binding, SOME typ, NoSyn)]
    val (_, vars_ctxt) = prep_decls Proof_Context.cert_var raw_vars ctxt
    val concl = Syntax.check_prop vars_ctxt parsed_prop
  in Logic.dest_equals concl |> snd end


fun check_classref {is_monitor=is_monitor} (SOME (cid, pos)) thy =                        
  let
    val ctxt = Proof_Context.init_global thy
    val name_cid_typ = get_onto_class_cid thy cid
    val cid_long = name_cid_typ |> (fst o fst)
    val rex = rex_of cid_long thy
    val _ = if is_monitor andalso (null rex orelse cid_long= default_cid ) 
            then error("should be monitor class!")
            else ()
    val onto_classes = get_onto_classes ctxt
    val markups = get_onto_class_name_global cid_long thy
                 |> Name_Space.markups (Name_Space.space_of_table onto_classes)
    val _ = Context_Position.reports ctxt (map (pair pos) markups);
  in  (name_cid_typ, pos)
  end
  | check_classref _ NONE _ = pair default_cid default_cid
                              |> rpair default_cid_typ
                              |> rpair Position.none

fun calc_update_term {mk_elaboration=mk_elaboration} thy (name, typ)
                     (S:(string * Position.T * string * term)list) term = 
    let val cid_long = name
        val cid_ty = typ
        val ctxt = Proof_Context.init_global thy
        fun read_assn (lhs, pos:Position.T, opr, rhs) term =
            let 
                fun get_class_name parent_cid attribute_name pos =
                  let
                    val Onto_Class {attribute_decl, inherits_from, ...} = 
                                                      get_onto_class_global parent_cid thy
                  in
                    if exists (fn (binding, _, _) => Binding.name_of binding = attribute_name)
                              attribute_decl
                    then parent_cid
                    else
                      case inherits_from of
                          NONE =>
                                ISA_core.err ("Attribute " ^ attribute_name
                                              ^ " not defined for class: " ^ cid_long) pos
                        | SOME (_, parent_name) => get_class_name parent_name attribute_name pos
                  end
                val _ = if mk_elaboration
                        then
                          let val attr_defined_cid = get_class_name cid_long lhs pos
                              val onto_classes = get_onto_classes ctxt
                              val markups = get_onto_class_name_global attr_defined_cid thy
                                           |> Name_Space.markups (Name_Space.space_of_table onto_classes)
                          in Context_Position.reports ctxt (map (pair pos) markups) end
                        else ()
                val info_opt = get_attribute_info cid_long (Long_Name.base_name lhs) thy
                val (ln,lnt,lnu,_) = case info_opt of 
                                           NONE => error ("unknown attribute >" 
                                                          ^((Long_Name.base_name lhs))
                                                          ^"< in class: "^cid_long)
                                        |  SOME{long_name, typ, ...} => (long_name, typ, 
                                                                         long_name ^ Record.updateN,
                                                                         (typ --> typ) 
                                                                          --> cid_ty --> cid_ty)
                val _ = if Long_Name.base_name lhs = lhs orelse ln = lhs then ()
                        else error("illegal notation for attribute of "^cid_long)
                fun join (ttt as \<^Type>\<open>int\<close>) = \<^Const>\<open>Groups.plus ttt\<close>
                   |join \<^Type>\<open>set _\<close> = \<^Const>\<open>Lattices.sup dummyT\<close>
                   |join \<^Type>\<open>list _\<close> = \<^Const>\<open>List.append dummyT\<close>
                   |join _ = error("implicit fusion operation not defined for attribute: "^ lhs)
                 (* could be extended to bool, map, multisets, ... *)
             in case opr of 
                  "=" => Const(lnu, dummyT) $ Abs ("uu_", dummyT, rhs) $ term
                | ":=" => Const(lnu, dummyT) $ Abs ("uu_", dummyT, rhs) $ term
                | "+=" => Const(lnu, dummyT) $ Abs ("uu_u", dummyT, join lnt $ (Bound 0) $ rhs) $ term
                | _ => error "corrupted syntax - oops - this should not occur" 
             end
             val t = fold read_assn S term
             val t' = if mk_elaboration
                      then elaborate_term' ctxt t
                      else check_term' ctxt t
    in if t = term
       then Sign.certify_term thy t'
       else
          let
             val concl = Syntax.check_term ctxt t';
          in Sign.certify_term thy concl end
    end

end (* local *)
end (* structure Instance_Terms *)

(* Evaluation of values and invariants: structural construction of values, evaluation in a
   stable theory, time limit. *)
structure Evaluation =
struct local open DOF_core in

(* Structural construction of the value of an instance.

   The term built by calc_update_term is "C.make a1 ... an" followed by a sequence of record
   updates. Rewriting it with the record definitions and simplification rules of the class and of
   its super-classes (no evaluation involved) yields the record in the normal form of nested
   extensions "C_ext x1 ... xk (D_ext y1 ... yl Unity)". Only the attribute values (the leaves)
   might still need evaluation: leaves that are literals or constructor terms are normal forms
   already (unset attributes are free variables), all others are evaluated one by one.
   The result is the same as the evaluation of the whole term, but avoids the large fixed cost
   of the evaluation of a record term (compare option monitor_trace_check).
   Returns NONE if the term is not of the expected shape: the caller then evaluates the whole
   term. Only used if the term contains free variables (unset attributes), where the evaluation
   of the whole term is a normalization by evaluation (Nbe). *)
fun normalize_object_fast thy cid_long (eval_leaf: term -> term) t =
  if null (Term.add_frees t []) then NONE
  else
    let
      val rules = Record_Normal_Form.rules thy cid_long
      val is_nf = Record_Normal_Form.is_nf thy
      fun norm_leaf a = if is_nf a then a else eval_leaf a
      fun norm_ext t =
        (case strip_comb t of
           (h as Const (c, _), args as _ :: _) =>
             if String.isSuffix Record.extN c
             then
               let val (leaves, more) = split_last args
                   val more' = norm_ext more
               in list_comb (h, map norm_leaf leaves @ [more']) end
             else raise TERM ("normalize_object_fast", [t])
         | (Const (c, _), []) =>
             if c = \<^const_name>\<open>Unity\<close> then t else raise TERM ("normalize_object_fast", [t])
         | _ => raise TERM ("normalize_object_fast", [t]))
    in if null rules then NONE
       else
         let val rewritten = Raw_Simplifier.rewrite_term thy rules [] t
         in SOME (norm_ext rewritten) end
         handle TERM _ => NONE | ERROR _ => NONE
    end

(* Evaluation in a "stable" theory.

   The caches of the code generator (and of Nbe) are valid for one theory only: they are
   discarded as soon as an evaluation is requested in a different theory, i.e. after each command
   that extends the theory, as each text* does. The code generation and the compilation for the
   invariants of a class are then repeated for each instance (about 0.2 s, compared to 15 ms with
   warm caches). Evaluations are therefore done in a fixed earlier theory of the same theory
   file ("static" evaluation, as with Code_Simp.static_conv), as long as this theory is an
   ancestor of the current one and declares all the constants of the term; otherwise the
   evaluation theory is replaced by the current theory. The code equations of constants of the
   term that are changed in the meantime are not seen (option invariants_static_eval). *)
val eval_theory = Synchronized.var "DOF_eval_theory" (NONE : theory option);

fun stable_eval thy (f: Proof.context -> term -> term) t =
  if not (Config.get_global thy invariants_static_eval)
  then f (Proof_Context.init_global thy) t
  else
    let
      val consts = Term.add_const_names t []
      fun usable th0 =
        Context.theory_long_name th0 = Context.theory_long_name thy
        andalso Context.subthy (th0, thy)
        andalso forall (Sign.declared_const th0) consts
      val th_eval = Synchronized.change_result eval_theory (fn cached =>
        (case cached of
           SOME th0 => if usable th0 then (th0, cached) else (thy, SOME thy)
         | NONE => (thy, SOME thy)))
    in
      f (Proof_Context.init_global th_eval) t
      handle ERROR _ => f (Proof_Context.init_global thy) t
           | TERM _ => f (Proof_Context.init_global thy) t
           | TYPE _ => f (Proof_Context.init_global thy) t
           | CTERM _ => f (Proof_Context.init_global thy) t
    end

(* Optional time limit (CPU seconds, scaled by the system option timeout_scale) for the
   evaluation of values and invariants; 0 means no limit. *)
fun apply_timeout thy f x =
  let val secs = Config.get_global thy invariants_timeout
  in if secs <= 0.0 then f x else Timeout.apply (Time.fromReal secs) f x end

fun timeout_msg thy what =
  "Evaluation of " ^ what ^ " exceeded the timeout of "
  ^ Real.toString (Config.get_global thy invariants_timeout)
  ^ " s (configuration option invariants_timeout)"

end (* local *)
end (* structure Evaluation *)

(* The registration of an instance with the open monitors: transitions of their automata
   and extension of their traces. *)
structure Monitor_Registration =
struct local open DOF_core Instance_Terms in

fun msg thy txt pos = if Config.get_global thy strict_monitor_checking
                  then ISA_core.err txt pos
                  else ISA_core.warn txt pos

fun msg_intro get n oid cid = ("accepts clause " ^ Int.toString n 
                               ^ " of monitor " ^ oid
                               ^ get (" not enabled for", " rejected")
                               ^ " doc_class: " ^ cid)

(* Fast path for the update of the trace attribute of a monitor: the stored value of a monitor
   is in normal form, i.e. a (nested) record extension "C_ext a1 ... an more" where the trace is
   an explicit list. Appending the pair (cid, oid) is a purely structural operation and avoids
   the code generation and ML compilation of a call to \<^verbatim>\<open>value\<close>.
   Returns NONE if the value is not of the expected shape; the caller falls back to evaluation. *)
fun append_trace_fast cid_long oid value_term =
  let val pair_T = HOLogic.mk_prodT (Trace_Attribute.doc_class_rexp_T, \<^typ>\<open>string\<close>)
      val trace_T = HOLogic.listT pair_T
      val item = \<^Const>\<open>Pair Trace_Attribute.doc_class_rexp_T \<^typ>\<open>string\<close>\<close>
                   $ Trace_Attribute.doc_class_rexp_t cid_long $ HOLogic.mk_string oid
      fun has_trace_type a = (fastype_of a = trace_T) handle TERM _ => false
      fun upd t =
        let val (h, args) = strip_comb t
            val is_ext = case h of Const (c, _) => String.isSuffix Record.extN c | _ => false
        in if not is_ext orelse null args then NONE
           else
             let val (init, more) = split_last args
                 val idx = map_index (fn (i, a) => if has_trace_type a then [i] else []) init |> flat
             in case idx of
                  [i] => (let val old = HOLogic.dest_list (nth init i)
                              val new = HOLogic.mk_list pair_T (old @ [item])
                          in SOME (list_comb (h, nth_map i (K new) init @ [more])) end
                          handle TERM _ => NONE)
                | [] => (case upd more of
                           SOME more' => SOME (list_comb (h, init @ [more']))
                         | NONE => NONE)
                | _ => NONE
             end
        end
  in upd value_term end

fun register_oid_cid_in_open_monitors binding (name, pos') thy = 
  let 
      val oid = Binding.name_of binding
      val cid_long= name
      val fcm_strict = Config.get_global thy free_class_in_monitor_strict_checking
      val fcm =  Config.get_global thy free_class_in_monitor_checking
      fun is_enabled (n, monitor_info) = 
                     if exists(is_subclass_global thy cid_long)(alphabet_of n thy)
                     then SOME (n, monitor_info)
                     else if fcm_strict orelse  fcm
                          then SOME (n, monitor_info)
                          else NONE
      (* filtering those monitors with automata, whose alphabet contains the
         cid of this oid. The enabled ones were selected and moved to their successor state
         along the super-class id. The evaluation is in parallel, simulating a product
         semantics without expanding the subclass relationship. *)
      fun is_enabled_for_cid (moid , monitor_info) =
        let val Monitor_Info {accepted_cids, automatas, rejected_cids, ...} = monitor_info
            val indexS= 1 upto (length automatas)
            val indexed_autoS = automatas ~~ indexS
            fun check_for_cid (A,n) = 
              let fun direct_super_class _ cid [] = cid
                    | direct_super_class thy cid (x::xs) =
                        if is_subclass_global thy cid x
                        then direct_super_class thy cid xs
                        else direct_super_class thy x xs
                  val accS = (RegExpInterface.enabled A accepted_cids)
                  val accS' = filter (is_subclass_global thy cid_long) accS
                  fun first_super_class cids =
                      case List.getItem cids
                        of  SOME (hd,tl) => SOME (direct_super_class thy hd tl)
                          | NONE => NONE
                  val first_accepted = first_super_class accS'
                  val rejectS = filter (is_subclass_global thy cid_long) rejected_cids
                  val first_rejected = first_super_class rejectS
              in
                case first_accepted of
                    NONE => (case first_rejected of
                                 NONE =>
                                   if fcm_strict
                                   then ISA_core.err (msg_intro fst n moid cid_long) pos'
                                   else if fcm
                                        then (ISA_core.warn (msg_intro fst n moid cid_long) pos';A)
                                        else A
                               | SOME _ => (msg thy (msg_intro snd n moid cid_long) pos';A))
                  | SOME accepted => (case first_rejected of
                                          NONE => RegExpInterface.next A accepted_cids (accepted)
                                        | SOME rejected =>
                                            if is_subclass_global thy accepted rejected
                                            then RegExpInterface.next A accepted_cids (accepted)
                                            else (msg thy (msg_intro snd n moid cid_long) pos';A))
              end
         in (moid,map check_for_cid indexed_autoS, monitor_info)  end  
      val enabled_monitors = List.mapPartial is_enabled
                      (Name_Space.dest_table (get_monitor_infos (Proof_Context.init_global thy)))
      val defined = defined_of oid thy
      val trace_attr = if defined
                       then Trace_Attribute.trace_attr_t cid_long oid 
                       else []
      fun mon_cid oid = cid_of oid thy |> get_onto_class_cid thy
                                                |> (fn ((name, _), typ) => (name, typ))
      val ctxt = Proof_Context.init_global thy
      fun def_trans_value_slow oid =
                (#1 o (calc_update_term {mk_elaboration=true} thy (mon_cid oid) trace_attr))
             #> value ctxt
      val item_oid = oid  (* the new instance; "oid" is shadowed by the monitor's name below *)
      fun def_trans_value oid =
        if null trace_attr orelse not (Config.get_global thy monitor_trace_fast)
        then def_trans_value_slow oid
        else fn v =>
          case append_trace_fast cid_long item_oid v of
            NONE => def_trans_value_slow oid v
          | SOME v' =>
              (if Config.get_global thy monitor_trace_check
                  andalso not (def_trans_value_slow oid v aconv v')
               then error ("monitor_trace_check: fast and slow update of the trace of monitor "
                           ^ oid ^ " differ:\nfast: " ^ Syntax.string_of_term ctxt v'
                           ^ "\nslow: " ^ Syntax.string_of_term ctxt (def_trans_value_slow oid v))
               else (); v')
      val _ = if null enabled_monitors then ()
              else if defined
                   then (tracing "registrating in monitors ..." ;
                         app (fn (n, _) => tracing (oid^" : "^cid_long^" ==> "^n)) enabled_monitors)
                   else ()
      (* check that any transition is possible: *)
      fun class_inv_checks thy =
              enabled_monitors
              |> map (fn (x, _) =>
                        let val cid_long =
                                  let val Instance cid = get_instance_global x thy
                                  in cid |> #cid end
                        in check_ml_invs cid_long x {is_monitor=true} thy end)
      val delta_autoS = map is_enabled_for_cid  enabled_monitors;
      fun update_info (n, aS, monitor_info) =  
        let val Monitor_Info {accepted_cids,rejected_cids,...} = monitor_info
        in Name_Space.map_table_entry n (K ((accepted_cids, rejected_cids, aS)
                                            |> make_monitor_info))
        end
      fun update_trace mon_oid =
        if Config.get_global thy object_value_debug
        then let fun def_trans_input_term  oid =
                   #1 o (calc_update_term {mk_elaboration=false} thy (mon_cid oid) trace_attr)
              in map_input_term mon_oid (def_trans_input_term mon_oid)
                 #> map_value_lazy mon_oid (def_trans_value mon_oid) end
        else map_value_lazy mon_oid (def_trans_value mon_oid)
  in  thy |> (* update traces of all enabled monitors *)
             fold update_trace (map #1 enabled_monitors)
          |> (* check class invariants of enabled monitors: they may inspect the value
                of the new instance, which is available (or pending) at this point *)
             tap class_inv_checks
          |> (* update the automata of enabled monitors *)
              Monitor_Info.map (fold update_info delta_autoS)
  end

end (* local *)
end (* structure Monitor_Registration *)

(* The high-level class invariants of an instance. *)
structure Invariants =
struct local open DOF_core Evaluation in

(* The invariants of the class of the instance oid (and of its super-classes), applied to
   docitem_value, as pairs ((invariant name, position), term to be evaluated). *)
fun invariant_terms thy name docitem_value =
  let
    fun get_all_invariants cid thy =
      case get_onto_class_global cid thy of
          Onto_Class {inherits_from=NONE, invs, ...} => single (cid, invs)
        | Onto_Class {inherits_from=SOME(_, father), invs, ...} =>
                                       (cid, invs) :: get_all_invariants father thy
    val cids_invariants = get_all_invariants name thy
    fun mk_inv_and_apply cid_invs value thy =
      let val ctxt = Proof_Context.init_global thy 
          val (cid_long, invs) = cid_invs
          fun conv bind = let  val inv_name = Binding.name_of bind
                                              |> Long_Name.qualify cid_long
                               val pos = Binding.pos_of bind
                               val inv_def = inv_name |> Syntax.parse_term ctxt
                          in ((inv_name, pos), Syntax.check_term ctxt (inv_def $ value)) end
      in invs |> map (conv o fst) end    
  in cids_invariants |> map (fn cid_invs => mk_inv_and_apply cid_invs docitem_value thy) |> flat
  end

(* pre: optional results of the evaluation of the invariants (in the order of invariant_terms),
   computed in a batch together with the value of the instance. *)

fun check_invariants_value name pre thy binding docitem_value =
  let
    val inv_and_apply_list = invariant_terms thy name docitem_value
    val pre_list = case pre of
                       SOME l => map SOME l
                     | NONE => map (K NONE) inv_and_apply_list
    fun check_invariants' (((inv_name, pos), term), pre_t) =
      let val ctxt = Proof_Context.init_global thy
          val trivial_true = \<^term>\<open>True\<close> |> HOLogic.mk_Trueprop |> Thm.cterm_of ctxt |> Thm.trivial
          val evaluated_term = (case pre_t of SOME t => t | NONE => apply_timeout thy (stable_eval thy value) term)
                handle Timeout.TIMEOUT _ => Free ("invariant_timeout", propT)
                      |  Match => error ("exception Match raised when checking "
                                       ^ inv_name ^ " invariant." ^ Position.here pos ^ "\n"
                                       ^ "You might want to check the definition of the invariant\n"
                                       ^ "against the value specified in the instance\n"
                                       ^ "or the default value declared in the instance class.")
                      | ERROR e =>
                  if (String.isSubstring "Wellsortedness error" e)
                      andalso (Config.get_global thy invariants_checking_with_tactics)
                  then (warning("Invariants checking uses proof tactics");
                         let val prop_term = HOLogic.mk_Trueprop term
                             val thms = Proof_Context.get_thms ctxt (inv_name ^ def_suffixN)
                             (* Get the make definition (def(1) of the record) *)
                             val thms' =
                                  (Proof_Context.get_thms ctxt (Long_Name.append name defsN)) @ thms
                             val _ = Goal.prove ctxt [] [] prop_term
                                                  (K ((unfold_tac ctxt thms') THEN (auto_tac ctxt)))
                                     |> Thm.close_derivation \<^here>
                                     handle ERROR e =>
                                       let
                                         val msg_intro = "Invariant "
                                                      ^ inv_name
                                                      ^ " failed to be checked using proof tactics"
                                                      ^ " with error:\n"
                                       in 
                                         if Config.get_global thy invariants_strict_checking
                                         then ISA_core.err (msg_intro ^ e) pos
                                         else (ISA_core.warn (msg_intro ^ e) pos; trivial_true) end
                         (* If Goal.prove does not fail, then the evaluation is considered True,
                            else an error is triggered by Goal.prove *)
                         in @{term True} end)
                  else \<^term>\<open>True \<Longrightarrow> True\<close>
      in case evaluated_term of
             \<^term>\<open>True\<close> => ((inv_name, pos), term)
           | \<^term>\<open>True \<Longrightarrow> True\<close> =>
                let val msg_intro = "Fail to check invariant "
                                    ^ inv_name
                                    ^ ".\nMaybe you can try "
                                    ^ "to activate invariants_checking_with_tactics\n"
                                    ^ "if your invariant is checked against doc_class algebraic "
                                    ^ "types like 'doc_class list' or 'doc_class set'"
                in if Config.get_global thy invariants_strict_checking
                   then ISA_core.err (msg_intro) pos
                   else (ISA_core.warn (msg_intro) pos; ((inv_name, pos), term)) end
           | Free ("invariant_timeout", _) =>
                let val msg = timeout_msg thy ("invariant " ^ inv_name)
                in if Config.get_global thy invariants_strict_checking
                   then ISA_core.err msg pos
                   else (ISA_core.warn msg pos; ((inv_name, pos), term)) end
           | _ => let val msg_intro = "Invariant " ^ inv_name ^ " violated"
                  in if Config.get_global thy invariants_strict_checking
                     then ISA_core.err msg_intro pos
                     else  (ISA_core.warn msg_intro pos; ((inv_name, pos), term)) end
      end
    val _ = map check_invariants' (inv_and_apply_list ~~ pre_list)
  in thy end

fun check_invariants_with pre thy binding =
  let val oid = Binding.name_of binding
      val name = cid_of oid thy
                 |> get_onto_class_cid thy |> (fst o fst)
  in check_invariants_value name pre thy binding (value_of oid thy) end

fun check_invariants thy binding = check_invariants_with NONE thy binding

end (* local *)
end (* structure Invariants *)

(* The creation of an instance. *)
structure Docitem_Parser =
struct local open DOF_core Instance_Terms Evaluation Monitor_Registration Invariants in

(* Creation of an instance. 

   Pure computations (type-checking of the attributes, the evaluation of the value and of the
   invariants) refer to the theory thy of the call; only their effects are booked in the resulting
   theory, in this order:
   1. the instance, whose terms are the result of a future if the computation runs in parallel,
   2. its registration with the open monitors (transitions of the automata, extension of the
      traces, class invariants of the monitors, which may read the value of the new instance),
   3. the ML invariants of the class,
   4. the high-level invariants of the class, in parallel or sequentially.

   The configuration flags are constant during the command and are inspected once. The routes:
   * an instance without class (default_cid): nothing is computed or checked,
   * an instance of a class: the attributes are parsed and type-checked immediately; the value is
     computed by a closure (one of four evaluators selected by the flags object_value_fast and
     (invariants_checking and invariants_batch)), which is run in a task (invariants_parallel and
     parallel_proofs > 0) or immediately. Errors of the task are reported at this command. *)
fun create_and_check_docitem is_monitor {is_inline=is_inline} {define=define} binding cid_pos doc_attrs thy =
  let
    val oid = Binding.name_of binding
    val (((name, args_cid), typ:typ), pos') = check_classref is_monitor cid_pos thy
    val default_cid = args_cid = default_cid
    val vcid = if default_cid
               then NONE
               else if virtual_of name thy |> #virtual
                    then SOME args_cid
                    else NONE
    (* declare_reference* without arguments is not checked against invariants *)
    val reference_only = not define andalso null doc_attrs

    (* effects on the theory *)
    fun define_instance instance = define_object_global {define = define} (binding, instance)
    fun register_and_check_ml thy' =
      thy' |> register_oid_cid_in_open_monitors binding (name, pos')
           |> (fn thy'' =>
                if reference_only then thy''
                else thy'' |> tap (check_opening_ml_invs name oid is_monitor)
                           |> tap (check_ml_invs name oid is_monitor))
  in
    if default_cid
    then (* Instance without a class associated, for example when you just want a document element
            to be referentiable without using the burden of ontology classes: neither an attribute 
            nor an invariant, and the value is a dummy that needs no evaluation.
            ex: text*[sdf]\<open> Lorem ipsum @{thm refl}\<close> *)
      let val dummy = dest_Free undefined_value
                      |> apfst (fn x => oid ^ "_" ^ x)
                      |> Free
      in thy |> define_instance (make_instance_value (false, is_inline, args_cid, vcid, (dummy, dummy)))
             |> register_and_check_ml
      end
    else
      let
        (* configuration flags *)
        val fast = Config.get_global thy object_value_fast
        val check_wanted = Config.get_global thy invariants_checking andalso not reference_only
        val batched = check_wanted andalso Config.get_global thy invariants_batch
        (* same gate as the forked presentation of Toplevel (Toplevel.present_state);
           declare [[invariants_parallel = false]] makes everything synchronous (debugging) *)
        val parallel = Future.proofs_enabled 1 andalso Config.get_global thy invariants_parallel

        (* The terms of the instance: the attributes are parsed and type-checked. *)
        fun terms () =
          let
            val ctxt = Proof_Context.init_global thy
            fun conv_attrs ((lhs, pos), rhs) = (Protocol_Message.clean_output lhs, pos, "=", 
                                                Syntax.parse_term ctxt rhs)
            val assns' = map conv_attrs doc_attrs
            val defaults_init = create_default_object thy binding name typ
            fun conv (na, _(*ty*), parsed_term) = (Binding.name_of na, Binding.pos_of na, 
                                                   "=", parsed_term);
            val S = map conv (get_attribute_defaults name thy);
            val (defaults, _) = calc_update_term {mk_elaboration=false} thy (name, typ) S defaults_init;
            val (value_term, _) = calc_update_term {mk_elaboration=true} thy (name, typ) assns' defaults
          in if Config.get_global thy object_value_debug
             then let val (input_term, _) = calc_update_term {mk_elaboration=false}
                                                             thy (name, typ) assns' defaults
                  in (input_term, value_term) end
             else (\<^term>\<open>()\<close>, value_term) end

        (* Evaluation. Each call of "value" has a large fixed cost (code generation and compilation):
           the invariants of the class are evaluated in one batch, together with the value if this
           is not built structurally. If a batch fails or exceeds the time limit, the invariants are
           evaluated, and timed, one by one when they are checked. *)
        fun eval_whole value_term =
                   (apply_timeout thy (stable_eval thy value) value_term
                   handle Timeout.TIMEOUT _ => error (timeout_msg thy ("the value of " ^ oid)))
        fun fast_value value_term = (* structural construction of the value (see normalize_object_fast) *)
          ((case normalize_object_fast thy name 
                                       (apply_timeout thy (stable_eval thy Nbe.dynamic_value)) 
                                       value_term 
            of SOME v =>
                (if Config.get_global thy monitor_trace_check
                    andalso not (v aconv eval_whole value_term)
                 then raise Fail ("object_value_fast: structural and evaluated value of "
                                  ^ oid ^ " differ")
                 else ();
                 SOME v)
             | NONE => NONE)
           handle ERROR _ => NONE | Timeout.TIMEOUT _ => NONE)
        fun invariants_of v = invariant_terms thy name v |> map snd
        fun eval_invariants invs = (* NONE if the batch fails *)
                                   (SOME (apply_timeout thy 
                                                        (stable_eval thy value) 
                                                        (HOLogic.mk_list \<^typ>\<open>bool\<close> invs)
                                         |> HOLogic.dest_list)
                                         handle ERROR _ => NONE | TERM _ => NONE | Match => NONE 
                                              | Timeout.TIMEOUT _ => NONE)
                                   |> (fn SOME bs => if length bs = length invs 
                                                     then SOME bs 
                                                     else NONE 
                                        | NONE => NONE)
        fun batch_known v = (* the value is known: only the invariants are evaluated *)
                      (case invariants_of v of [] => (v, NONE) | invs => (v, eval_invariants invs))
        fun batch_unknown value_term = (* value and invariants in one call *)
          (case invariants_of value_term of
             [] => (eval_whole value_term, NONE)
           | invs =>
               (let val (v', l) = apply_timeout thy (stable_eval thy value)
                                    (HOLogic.mk_prod (value_term, HOLogic.mk_list \<^typ>\<open>bool\<close> invs))
                                  |> HOLogic.dest_prod
                    val bs = HOLogic.dest_list l
                in if length bs <> length invs then (eval_whole value_term, NONE)
                   else (if Config.get_global thy monitor_trace_check
                            andalso not (v' aconv eval_whole value_term)
                         then raise Fail ("invariants_batch: batch and separate evaluation results of "
                                          ^ oid ^ " differ")
                         else ();
                         (v', SOME bs)) end
                handle ERROR _ => (eval_whole value_term, NONE) | TERM _ => (eval_whole value_term, NONE)
                     | Timeout.TIMEOUT _ => (eval_whole value_term, NONE) 
                     | Match => (eval_whole value_term, NONE)))

        (* the four evaluators: value, and results of the batch of the invariants if any *)
        val evaluate : term -> term * term list option =
          (case (fast, batched) of
             (true, true)   => (fn vt => case fast_value vt of SOME v => batch_known v
                                                             | NONE => batch_unknown vt)
           | (true, false)  => (fn vt => case fast_value vt of SOME v => (v, NONE)
                                                             | NONE => (eval_whole vt, NONE))
           | (false, true)  => batch_unknown
           | (false, false) => (fn vt => (eval_whole vt, NONE)))

        (* The closure of the instance. The results of the batch of the invariants are passed to the
           check of the invariants (below) by a variable. *)
        val results = Synchronized.var "docitem_results" (NONE : term list option)
        (* The attributes are parsed and type-checked synchronously: their errors abort the command
           at once. Only the evaluation of the value and of the invariants runs in the task. *)
        val (input_term, value_term) = terms ()
        fun closure () =
          let val (value, res) = evaluate value_term
              val _ = Synchronized.change results (K res)
          in (input_term, value) end
        fun check_invariants_of termNvalue =
          if check_wanted
          then ignore (check_invariants_value name (Synchronized.value results) thy binding
                                              (snd (Future.join termNvalue)))
          else ()

        (* In parallel, the check of the invariants is done in a second task: it reports the errors 
           and warnings at the position of this command. Exceptions of a forked task are reported by
           Execution.fork; a failure of the closure is already reported by its task. *)
        val instance = if parallel
                       then make_instance (false, is_inline, args_cid, vcid, closure)
                       else make_instance_value (false, is_inline, args_cid, vcid, closure ())
        val Instance {termNvalue, ...} = instance
      in
        thy |> define_instance instance
            |> register_and_check_ml
            |> (fn thy' => 
                  (if parallel
                   then ignore (Execution.fork {name = DOF_docitemN, 
                                                pos = Position.thread_data (), pri = ~1}
                                  (fn () => case Future.join_result termNvalue of
                                              Exn.Exn _ => () 
                                            | Exn.Res _ => check_invariants_of termNvalue))
                   else check_invariants_of termNvalue;
                   thy'))
      end
  end

end (* local *)
end (* structure Docitem_Parser *)


fun meta_args_exec (meta_args as ((binding, cid_pos), doc_attrs) : ODL_Meta_Args_Parser.meta_args_t) thy =
         thy |> (if meta_args = ODL_Meta_Args_Parser.empty_meta_args
                 then (K thy)
                 else Docitem_Parser.create_and_check_docitem 
                                    {is_monitor = false} {is_inline = true} {define = true}
                                    binding (I cid_pos) (I doc_attrs))

fun value_cmd {assert=assert} meta_args_opt raw_name modes raw_t pos thy  =
  let
    val thy' = meta_args_exec meta_args_opt thy
    val name = intern_evaluator thy' raw_name;
    val t = Syntax.parse_term (Proof_Context.init_global thy') raw_t;
    val term' = DOF_core.parsed_elaborate (Proof_Context.init_global thy') pos t
    val term'' = Syntax.check_term (Proof_Context.init_global thy') term'
    val t' = value_select name (Proof_Context.init_global thy') term'';
    val ty' = Term.type_of t';
    val (ty',t') = if assert
              then case (Term.type_of t',t')  of
                       (\<^typ>\<open>bool\<close>, \<^term>\<open>True\<close>)  => (ty', t')
                     | (_,\<^term>\<open>True\<close>) =>  error "Assertion expressions must be boolean."
                     | _ =>  error "Assertion failed."
              else (ty', t')
    val ctxt' = Proof_Context.augment t' (Proof_Context.init_global thy');
    val p = Print_Mode.with_modes modes 
               (fn () => Pretty.block [Pretty.quote (Syntax.pretty_term ctxt' t'),
                                       Pretty.fbrk, Pretty.str "::", Pretty.brk 1, 
                                       Pretty.quote (Syntax.pretty_typ ctxt' ty')]) ();
    val _ = Pretty.writeln p 
  in  thy' end;

val opt_modes =
  Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.!!! (Scan.repeat1 Parse.name --| \<^keyword>\<open>)\<close>)) [];

val opt_evaluator =
  Scan.optional (\<^keyword>\<open>[\<close> |-- Parse.name --| \<^keyword>\<open>]\<close>) "";

fun pass_trans_to_value_cmd (((name, meta_args_opt), modes), t) trans =
let val pos = Toplevel.pos_of trans
in
   trans |> Toplevel.theory (value_cmd {assert=false} meta_args_opt name modes t pos)
end

\<comment> \<open>c.f. \<^file>\<open>~~/src/Pure/Isar/isar_cmd.ML\<close>\<close>

(*
  term* command uses the same code as term command
  and adds the possibility to check Term Annotation Antiquotations (TA)
  with the help of DOF_core.transduce_term_global function
*)
fun string_of_term  s pos ctxt =
let
  val t = Syntax.read_term ctxt s;
  val T = Term.type_of t;
  val ctxt' = Proof_Context.augment t ctxt;
  val _ = DOF_core.transduce_term_global {mk_elaboration=false} (t , pos)
                                          (Proof_Context.theory_of ctxt');
in
  Pretty.string_of
    (Pretty.block [Pretty.quote (Syntax.pretty_term ctxt' t), Pretty.fbrk,
      Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt' T)])
end;

fun print_item string_of (modes, arg) state =  
    Print_Mode.with_modes modes (fn () => writeln (string_of state arg)) (); 

fun prin t pos state _  = string_of_term t pos (Toplevel.context_of state)

fun print_term meta_args_opt (string_list, string) trans =
let
  val pos = Toplevel.pos_of trans
in meta_args_exec meta_args_opt
   #> tap (fn thy => print_item (prin string pos) 
                                (string_list, string) 
                                (Toplevel.make_state (SOME (Context.Theory thy))))
   |> (fn thy => Toplevel.theory thy trans)
end

val (disable_assert_evaluation, disable_assert_evaluation_setup)
     = Attrib.config_bool \<^binding>\<open>disable_assert_evaluation\<close> (K false);

val _ = Theory.setup disable_assert_evaluation_setup

fun pass_trans_to_assert_value_cmd (((name, meta_args_opt), modes), t) trans =
let val pos = Toplevel.pos_of trans
in trans
   |> Toplevel.theory
        (fn thy =>
           if Config.get_global thy disable_assert_evaluation
           then (meta_args_exec meta_args_opt
                 #> tap (fn thy => print_item (prin t pos) (modes, t) 
                        (Toplevel.make_state (SOME (Context.Theory thy)))))
                thy
           else value_cmd {assert=true} meta_args_opt name modes t pos thy) 
end

(* setup ontology aware commands *)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>term*\<close> "read and print term"
     (ODL_Meta_Args_Parser.opt_attributes -- (opt_modes -- Parse.term) 
     >> (uncurry print_term));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>value*\<close> "evaluate and print term"
    ((opt_evaluator -- ODL_Meta_Args_Parser.opt_attributes -- opt_modes -- Parse.term) 
     >> (pass_trans_to_value_cmd));
                                


val _ =
  Outer_Syntax.command \<^command_keyword>\<open>assert*\<close> "evaluate and assert term"
    ((opt_evaluator -- ODL_Meta_Args_Parser.opt_attributes -- opt_modes -- Parse.term) 
     >> pass_trans_to_assert_value_cmd);


(* setup ontology - aware text and ML antiquotations. Due to lexical restrictions, we can not
   declare them as value* or term*, although we will refer to them this way in papers. *)
local
  fun pretty_term_style ctxt (style: term -> term, t) =
      Document_Output.pretty_term ctxt (style (DOF_core.check_term ctxt t))
  fun print_term ctxt t = ML_Syntax.print_term (DOF_core.check_term (Context.proof_of ctxt) t)
in
val _ = Theory.setup
  (Document_Output.antiquotation_pretty_source_embedded \<^binding>\<open>value_\<close>
    (Scan.lift opt_evaluator -- Term_Style.parse -- Scan.lift Parse.term)
    (fn ctxt => fn ((name, style), t) =>
      Document_Output.pretty_term ctxt (style (value_select' name ctxt t)))
  #> ML_Antiquotation.inline_embedded \<^binding>\<open>value_\<close>
      ((Scan.lift (opt_evaluator -- Parse.term))
      #> (fn ((name, t),(ctxt, ts)) =>
           (((value_select' name (Context.proof_of ctxt) t)
             |> (ML_Syntax.atomic o (print_term ctxt))), (ctxt, ts))))
  #> Document_Output.antiquotation_pretty_source_embedded \<^binding>\<open>term_\<close> 
             (Term_Style.parse -- Args.term) pretty_term_style
  #> ML_Antiquotation.inline_embedded \<^binding>\<open>term_\<close>
       (fn (ctxt, ts) => (Args.term >> (ML_Syntax.atomic o (print_term ctxt))) (ctxt, ts)))
end

(* setup evaluators  *)
val _ = Theory.setup(
     add_evaluator (\<^binding>\<open>simp\<close>, Code_Simp.dynamic_value) #> snd
  #> add_evaluator (\<^binding>\<open>nbe\<close>,  Nbe.dynamic_value) #> snd
  #> add_evaluator (\<^binding>\<open>code\<close>, Code_Evaluation.dynamic_value_strict) #> snd);


end;  (* structure DOF_Value_Cmd *)

\<close>

end
