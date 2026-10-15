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

chapter \<open>The Document Ontology Framework: Term Annotation Antiquotations\<close>

text\<open> The syntax and the semantics of the annotations of terms (the inner-syntax antiquotations, ISA's), and the transformers that check and elaborate them. \<close>

theory Isa_DOF_TA   (* Term Annotation Antiquotations *)
  imports Isa_DOF_core
begin

section\<open> Syntax for Term Annotation Antiquotations (TA)\<close>

text\<open>Isabelle/DOF allows for annotations at the term level, for which an
antiquotation syntax and semantics is defined at the inner syntax level.
(For this reasons, the mechanism has been called somewhat misleading
\<^emph>\<open>inner syntax antiquotations\<close> in earlier versions of Isabelle/DOF.)

For the moment, only a fixed number of builtin TA's is supported, future
versions might extend this feature substantially.\<close>

subsection\<open> Syntax \<close> 

datatype "doc_class" = mk string

ML\<open>
(* Terms of the trace attribute of monitors. *)
structure Trace_Attribute =
struct

val doc_class_rexp_T = \<^typ>\<open>doc_class rexp\<close>
val doc_class_rexp_Ts = "doc_class rexp"
fun doc_class_rexp_t cid = \<^Const>\<open>Atom \<^typ>\<open>doc_class\<close>\<close> $ (\<^Const>\<open>mk\<close> $ HOLogic.mk_string cid)

val trace_attr_Ts = "(" ^ doc_class_rexp_Ts ^ " \<times> string) list"
val trace_attr_ts = ((\<^binding>\<open>trace\<close>, trace_attr_Ts , Mixfix.NoSyn), SOME "[]")
fun trace_attr_t cid oid =
  let val t = [\<^Const>\<open>Pair doc_class_rexp_T \<^typ>\<open>string\<close>\<close>
               $ doc_class_rexp_t cid
               $ HOLogic.mk_string oid]
              |> HOLogic.mk_list \<^Type>\<open>prod doc_class_rexp_T \<^typ>\<open>string\<close>\<close>
  in [(traceN, \<^here>, "+=", t)] end

end (* structure Trace_Attribute *)
\<close>

\<comment> \<open>and others in the future : file, http, thy, ...\<close> 

datatype "typ" = Isabelle_DOF_typ string (\<open>@{typ _}\<close>)
datatype "term" = Isabelle_DOF_term string (\<open>@{term _}\<close>)
datatype "thm" = Isabelle_DOF_thm string (\<open>@{thm _}\<close>)
datatype "file" = Isabelle_DOF_file string (\<open>@{file _}\<close>)
datatype "thy" = Isabelle_DOF_thy string (\<open>@{thy _}\<close>)
consts   Isabelle_DOF_docitem       :: "string \<Rightarrow> 'a" (\<open>@{docitem _}\<close>)
datatype "docitem_attr" = Isabelle_DOF_docitem_attr string  string (\<open>@{docitemattr (_) :: (_)}\<close>)
consts Isabelle_DOF_trace_attribute :: "string \<Rightarrow> (string * string) list" (\<open>@{trace'_attribute _}\<close>)
consts Isabelle_DOF_instances_of :: "string \<Rightarrow> 'a list" (\<open>@{instances'_of _}\<close>)

\<comment> \<open>Dynamic setup of inner syntax cartouche\<close>

ML \<open>
(*  Author:     Frédéric Tuong, Université Paris-Saclay *)
(*  Title:      HOL/ex/Cartouche_Examples.thy
    Author:     Makarius
*)
  local
    fun mk_char (f_char, f_cons, _) (s, _) accu =
        fold
          (fn c => fn (accu, l) =>
            (f_char c accu, f_cons c l))
          (rev (map Char.ord (String.explode s)))
          accu;

    fun mk_string (_, _, f_nil) accu [] = (accu, f_nil)
      | mk_string f accu (s :: ss) = mk_char f s (mk_string f accu ss);
  in
    fun string_tr f f_mk accu content args =
      let fun err () = raise TERM ("string_tr", args) in
        (case args of
          [(c as Const (@{syntax_const "_constrain"}, _)) $ Free (s, _) $ p] =>
            (case Term_Position.decode_position1 p of
              SOME {pos, ...} => c $ f (mk_string f_mk accu (content (s, pos))) $ p
            | NONE => err ())
        | _ => err ())
      end;
  end;
\<close>

syntax "_cartouche_string" :: "cartouche_position \<Rightarrow> _"  (\<open>_\<close>)

ML\<open>
structure Cartouche_Grammar = struct
  fun list_comb_mk cst n c = list_comb (Syntax.const cst, String_Syntax.mk_bits_syntax n c)
  val nil1 = Syntax.const @{const_syntax String.empty_literal}
  fun cons1 c l = list_comb_mk @{const_syntax String.Literal} 7 c $ l

  val default =
    [ ( "char list"  (* what is the status of "char list" ? ? ? bu *)
      , ( Const (@{const_syntax Nil}, @{typ "char list"})
        , fn c => fn l => Syntax.const @{const_syntax Cons} $ list_comb_mk @{const_syntax Char} 8 c $ l
        , snd))
    , ( \<^type_name>\<open>String.literal\<close> , (nil1, cons1, snd))]
end
\<close>

ML\<open>
fun parse_translation_cartouche binding l f_integer accu =
  let val cartouche_type = Attrib.setup_config_string binding (K (fst (hd l)))
      (* if there is no type specified, by default we set the first element
         to be the default type of cartouches *) in
  fn ctxt =>
    let val cart_type = Config.get ctxt cartouche_type in
    case List.find (fn (s, _) => s = cart_type) l of
      NONE => error ("Unregistered return type for the cartouche: \"" ^ cart_type ^ "\"")
    | SOME (_, (nil0, cons, f)) =>
        string_tr f (f_integer, cons, nil0) accu (Symbol_Pos.cartouche_content o Symbol_Pos.explode)
    end
  end
\<close>

parse_translation \<open>
  [( @{syntax_const "_cartouche_string"}
   , parse_translation_cartouche \<^binding>\<open>cartouche_type\<close> Cartouche_Grammar.default (K I) ())]
\<close>

(* tests *)  
term "@{typ  ''int => int''}"  
term "@{term ''Bound 0''}"  
term "@{thm  ''refl''}"  
term "@{docitem  ''<doc_ref>''}"
ML\<open>   @{term "@{docitem  ''<doc_ref>''}"}\<close>

term "@{typ  \<open>int \<Rightarrow> int\<close>}"  
term "@{term \<open>\<forall>x. P x \<longrightarrow> Q\<close>}"  
term "@{thm  \<open>refl\<close>}"  
term "@{docitem  \<open>doc_ref\<close>}"
ML\<open>   @{term "@{docitem  \<open>doc_ref\<close>}"}\<close>
(**)
declare [[cartouche_type = "String.literal"]]
term "\<open>Université\<close> :: String.literal"
declare [[cartouche_type = "char list"]]
term "\<open>Université\<close> :: char list"



subsection\<open> Semantics \<close>

ML\<open>
(* Normal forms of instance values, and structural access to their attributes.

   The value of an instance is a nested record extension "C_ext x1 ... xk (D_ext ... Unity)".
   Rewriting with the record definitions and simplification rules of its class and super-classes
   (no evaluation involved) reduces constructions, updates and projections of such values. *)
structure Record_Normal_Form =
struct

fun ancestry thy cid =
  case DOF_core.get_onto_class_global cid thy of
      DOF_core.Onto_Class {inherits_from=NONE, ...} => [cid]
    | DOF_core.Onto_Class {inherits_from=SOME (_, p), ...} => cid :: ancestry thy p

fun rules thy cid_long =
  let val ctxt = Proof_Context.init_global thy
      fun thms_of cid sfx =
        Proof_Context.get_thms ctxt (Long_Name.append cid sfx) handle ERROR _ => []
  in ancestry thy cid_long
     |> maps (fn c => thms_of c defsN @ thms_of c "simps")
     |> map Simpdata.mk_eq
  end

fun is_literal_head c =
  member (op =) [\<^const_name>\<open>numeral\<close>, \<^const_name>\<open>zero_class.zero\<close>,
                 \<^const_name>\<open>one_class.one\<close>, \<^const_name>\<open>uminus\<close>,
                 \<^const_name>\<open>insert\<close>, \<^const_name>\<open>bot_class.bot\<close>] c

(* terms built from constructors, literals and unset attributes: normal forms for Nbe *)
fun is_nf _ (Free (x, _)) = String.isSuffix "_Attribute_Not_Initialized" x
  | is_nf thy (t as _ $ _) =
      (case strip_comb t of
         (Const (c, _), args) =>
           (Code.is_constr thy c orelse is_literal_head c) andalso forall (is_nf thy) args
       | _ => false)
  | is_nf thy (Const (c, _)) = Code.is_constr thy c orelse is_literal_head c
  | is_nf _ _ = false

(* "f value" with a record field f and a value in normal form: the value of the attribute,
   or NONE if it is not a normal form (the caller then evaluates). *)
fun project thy cid_long t =
  let val rs = rules thy cid_long
  in if null rs then NONE
     else
       let val r = Raw_Simplifier.rewrite_term thy rs [] t
       in if is_nf thy r then SOME r else NONE end
       handle ERROR _ => NONE | TERM _ => NONE
  end

end

structure ISA_core = 
struct

fun err msg pos = error (msg ^ Position.here pos);
fun warn msg pos = warning (msg ^ Position.here pos);

fun ML_isa_check_generic check thy (term, pos) =
  let val name = (HOLogic.dest_string term
                  handle TERM(_,[t]) => error ("wrong term format: must be string constant: " 
                                               ^ Syntax.string_of_term_global thy t ))
      val _ = check thy (name,pos)
  in  SOME term end;  

fun check_identity _ (term, _, _) _ = SOME term

fun ML_isa_check_typ thy (term, _, pos) _ =
  let fun check thy (name, _) = let val ctxt = (Proof_Context.init_global thy)
                                in (Syntax.check_typ ctxt o Syntax.parse_typ ctxt) name end
  in  ML_isa_check_generic check thy (term, pos) end


fun ML_isa_check_term thy (term, _, pos) _ =
  let fun check thy (name, _) = let val ctxt = (Proof_Context.init_global thy)
                                in (Syntax.check_term ctxt o Syntax.parse_term ctxt) name end 
  in  ML_isa_check_generic check thy (term, pos) end


fun ML_isa_check_thm thy (term, _, pos) _ =    
  let fun check thy (name, _) = Global_Theory.check_fact thy (name, Position.none)
  in   ML_isa_check_generic check thy (term, pos) end


fun ML_isa_check_file thy (term, _, pos) _ =
  let fun check thy (name, _) = name |> Syntax.read_input
                                     |> Resources.check_file (Proof_Context.init_global thy) NONE 
  in  ML_isa_check_generic check thy (term, pos) end;

fun check_instance thy (term, _, pos) s =
  let
    val bname = Long_Name.base_name s;
    val qual = Long_Name.qualifier s;
    val class_name = (case try (unprefix DOF_core.doc_class_prefix) bname of
                        NONE => unprefix DOF_core.long_doc_class_prefix bname
                      | SOME name => name)
                     |> Long_Name.qualify qual
    fun check thy (name, _)  =
      let
        val name' = DOF_core.cid_of name thy
                   |> DOF_core.get_onto_class_cid thy |> (fst o fst)
        fun check' (class_name, object_cid) =
          if class_name = object_cid
          then ()
          else err (name ^ " is not an instance of " ^ class_name) pos
      in check' (class_name, name') end;
  in ML_isa_check_generic check thy (term, pos) end

fun check_instance_of thy (term, _, pos) _ =
  let
    fun check thy (name, _)  =
      if equal name DOF_core.default_cid
      then ()
      else
        let
          val class_typ = name |> DOF_core.get_onto_class_cid thy |> snd
          fun check' (class_name, typ) =
            if equal (class_name |> Syntax.read_typ_global thy) typ
            then ()
            else err (name ^ " is not a class name") pos
        in check' (name, class_typ) end;
  in ML_isa_check_generic check thy (term, pos) end

fun ML_isa_id _ (term,_) = SOME term


fun ML_isa_check_docitem thy (term, _, pos) _ =
  let fun check thy (name, _) = DOF_core.get_instance_global name thy
  in  ML_isa_check_generic check thy (term, pos) end

fun ML_isa_check_trace_attribute thy (term, _, _) _ =
  let
    val oid = (HOLogic.dest_string term
                  handle TERM(_,[t]) => error ("wrong term format: must be string constant: " 
                                               ^ Syntax.string_of_term_global thy t ))
    val _ = DOF_core.get_instance_global oid thy
  in SOME term end

fun ML_isa_elaborate_generic (_:theory) isa_name ty term_option _ =
  case term_option of
      NONE => error("Wrong term option. You must use a defined term")
    | SOME term => Const (isa_name, ty) $ term

(* Convert some excluded mixfix symbols that can appear in an inner syntax name. *)
val clean_mixfix = translate_string
  (fn "_" => "'_"
    | "'" => "''"
    | c => c);

fun rm_mixfix name mixfix thy =
  let
    val old_constants =
      Consts.dest (Sign.consts_of thy) |> #constants
      |> map fst
      |> filter (Long_Name.base_name #> equal name)
      |> map (pair mixfix)
      |> map swap
      |> map (apfst (Syntax.read_term_global thy))
      |> map (apsnd Mixfix.mixfix)
  in thy |> (Local_Theory.notation false Syntax.mode_default old_constants
             |> Named_Target.theory_map)
  end

fun elaborate_instance thy _ _ term_option _ =
  case term_option of
      NONE => error ("Malformed term annotation")
    | SOME term => let val instance_name = HOLogic.dest_string term
                   in DOF_core.value_of instance_name thy
                   end

(*
  The function declare_ISA_class_accessor_and_check_instance uses a prefix
  because the class name is already bound to "doc_class Regular_Exp.rexp" constant
  by add_doc_class_cmd function
*)
fun declare_ISA_class_accessor_and_check_instance (params, doc_class_name, bind_pos) thy =
  let
    val bname = Long_Name.base_name doc_class_name
    val bname' = prefix DOF_core.doc_class_prefix bname
    val bind = bname' |> pair bind_pos |> swap |> Binding.make
    val bind' = prefix DOF_core.long_doc_class_prefix bname
                |> pair bind_pos |> swap |> Binding.make
    val typ = Type (doc_class_name, map TFree params)
    val const_typ = \<^typ>\<open>string\<close> --> typ
    fun mixfix_enclose name = name |> enclose "@{"  " _}"
    val mixfix = clean_mixfix bname |> mixfix_enclose
    val mixfix' = clean_mixfix doc_class_name |> mixfix_enclose
    fun add_const (b, T, mx) =
      Sign.add_consts [(b, T, mx)] #>
      DOF_core.add_isa_transformer b
        ((check_instance, elaborate_instance) |> DOF_core.make_isa_transformer)
  in
    thy |> rm_mixfix bname' mixfix
        |> add_const (bind, const_typ, Mixfix.mixfix mixfix)
        |> add_const (bind', const_typ, Mixfix.mixfix mixfix')
  end

fun elaborate_instances_of thy _ _ term_option _ =
  let
    val class_name = case term_option of
                        NONE => error ("Malformed term annotation")
                      | SOME term => HOLogic.dest_string term
    fun mk_list class_typ f =
      let
          val values = thy |> Proof_Context.init_global |> DOF_core.get_instances
                       |> Name_Space.dest_table
                       |> map fst
                       |> f
                       |> map (fn oid => DOF_core.value_of oid thy)
        in HOLogic.mk_list class_typ values end
  in if equal class_name DOF_core.default_cid
     then
       (* When the class name is default_cid = "text",
          return the instances attached to this default class.
          We want the class default_cid to stay abstract
          and not have the capability to be defined with attribute, invariants, etc.
          Hence this can handle docitem without a class associated,
          for example when you just want a document element to be referentiable
          without using the burden of ontology classes.
          ex: text*[sdf]\<open> Lorem ipsum @{thm refl}\<close> *)
       (filter (fn name => DOF_core.cid_of name thy |> equal DOF_core.default_cid))
       |> mk_list DOF_core.default_cid_typ
     else
       let
         val class_typ = class_name |> Syntax.read_typ_global thy
       in
         (filter_out (fn name => DOF_core.cid_of name thy |> equal DOF_core.default_cid)
          #> filter (fn name => DOF_core.cid_of name thy
                                |> Syntax.read_typ_global thy
                                |> equal class_typ))
         |> mk_list class_typ
       end
  end

fun symbex_attr_access0 ctxt cid proj_term term =
let
      val [subterm'] = Type_Infer_Context.infer_types ctxt [proj_term $ term]
      val thy = Proof_Context.theory_of ctxt
      fun eval () = Value_Command.value ctxt subterm'
in
  case Record_Normal_Form.project thy cid subterm' of
      SOME v =>
        (if Config.get_global thy DOF_core.monitor_trace_check andalso not (v aconv eval ())
         then raise Fail ("attribute access: structural and evaluated projection differ for "
                          ^ Syntax.string_of_term ctxt subterm')
         else ();
         v)
    | NONE => eval ()
end

fun compute_attr_access ctxt attr oid pos_option pos' = (* template *)
  let
    val value =  DOF_core.value_of oid (Context.theory_of ctxt)
    val ctxt' =  Context.proof_of ctxt
    val thy = Context.theory_of ctxt
    val DOF_core.Instance {cid,...} =
                                    DOF_core.get_instance_global oid thy
    val instances = DOF_core.get_instances ctxt'
    val markups = DOF_core.get_instance_name_global oid thy
                 |> Name_Space.markups (Name_Space.space_of_table instances)
    val _ = Context_Position.reports ctxt' (map (pair pos') markups);
    val {long_name, typ=ty, ...} = 
      case DOF_core.get_attribute_info_local cid attr ctxt' of
          SOME f => f
        | NONE =>  error("attribute undefined for reference: "
                         ^ oid
                         ^ Position.here
                         (the pos_option handle Option.Option =>
                         error("Attribute "
                               ^ attr
                               ^ " undefined for reference: "
                               ^ oid ^ Position.here pos')))
    val proj_term = Const(long_name,dummyT --> ty)
    val _ = case pos_option of
                NONE => ()
              | SOME pos =>
                  let 
                    val class_name = Long_Name.qualifier long_name
                    val onto_classes = DOF_core.get_onto_classes ctxt'
                    val markups = DOF_core.get_onto_class_name_global class_name thy
                                 |> Name_Space.markups (Name_Space.space_of_table onto_classes)
                  in Context_Position.reports ctxt' (map (pair pos) markups) end
  in  symbex_attr_access0 ctxt' cid proj_term value end

fun ML_isa_elaborate_trace_attribute (thy:theory) _ _ term_option pos =
case term_option of
    NONE => err ("Malformed term annotation") pos
  | SOME term => 
      let
        val oid = HOLogic.dest_string term
        val traces = compute_attr_access (Context.Theory thy) traceN oid NONE pos
        fun conv (\<^Const>\<open>Pair \<^typ>\<open>doc_class rexp\<close> \<^typ>\<open>string\<close>\<close>
                    $ (\<^Const>\<open>Atom \<^typ>\<open>doc_class\<close>\<close> $ (\<^Const>\<open>mk\<close> $ s)) $ S) =
               let val s' =  DOF_core.get_onto_class_name_global (HOLogic.dest_string s) thy 
               in \<^Const>\<open>Pair \<^typ>\<open>string\<close> \<^typ>\<open>string\<close>\<close> $ HOLogic.mk_string s' $ S end
           |conv _ = err ("Malformed term annotation") pos
        val traces' = map conv (HOLogic.dest_list traces)
      in HOLogic.mk_list \<^Type>\<open>prod \<^typ>\<open>string\<close> \<^typ>\<open>string\<close>\<close> traces' end

end; (* struct *)
                                                            
\<close>


subsection\<open> Isar - Setup for Isa Transformers\<close>
(* Declaration of Isa_transformers for term anti-quotations (typ, term, thm, etc.).
   They must be declared in the same theory file as the one of the declaration
   of Isabelle_DOF term anti-quotations !!! *)

ML\<open>
local open DOF_core ISA_core in
val _ = Theory.setup(
           let          fun doit (n, check, elaborate) thy = (
                                  let val ns = Sign.tsig_of thy |> Type.type_space
                                      val name = n
                                      val pos = Name_Space.the_entry_pos ns name
                                      val bname = Long_Name.base_name name
                                      val binding = Binding.make (bname, pos)
                                                         |> Binding.prefix_name ISA_prefix
                                                         |> Binding.prefix false bname
                                  in  add_isa_transformer binding ((check, elaborate) 
                                                            |> make_isa_transformer) thy
                                  end) 
                        fun doit2 (n, check, elaborate) thy = (
                            let val ns = Sign.consts_of thy |> Consts.space_of
                                val name = n
                                val pos = Name_Space.the_entry_pos ns name
                                val bname =  Long_Name.base_name name
                                val binding = Binding.make (bname, pos)
                            in  add_isa_transformer binding ((check, elaborate) 
                                                             |> make_isa_transformer) thy
                            end)
           in
              [   (\<^type_name>\<open>typ\<close>, ML_isa_check_typ, ML_isa_elaborate_generic)
                , (\<^type_name>\<open>term\<close>, ML_isa_check_term, ML_isa_elaborate_generic)
                , (\<^type_name>\<open>thm\<close>, ML_isa_check_thm, ML_isa_elaborate_generic)
                , (\<^type_name>\<open>file\<close>, ML_isa_check_file, ML_isa_elaborate_generic)]
              |> fold doit
           #>
             ([  (\<^const_name>\<open>Isabelle_DOF_docitem\<close>, ML_isa_check_docitem, ML_isa_elaborate_generic)
               , (\<^const_name>\<open>Isabelle_DOF_trace_attribute\<close>, ML_isa_check_trace_attribute, 
                                                             ML_isa_elaborate_trace_attribute)
               , (\<^const_name>\<open>Isabelle_DOF_instances_of\<close>, check_instance_of, elaborate_instances_of)]
             |> fold doit2)
           end)
end (*local*)
\<close>

end
