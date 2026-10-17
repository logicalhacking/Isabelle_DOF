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

chapter \<open>The Core of the Document Ontology Framework for Isabelle\<close>

text\<open> The core of \<^emph>\<open>Isabelle/DOF\<close>: the primitive markup generators, the data of the plugin 
(document classes, instances, monitors, invariants, transformers of the inner-syntax antiquotations), 
and the configuration flags that control the evaluation and the parallelization of the checks. The 
syntax and the commands are defined in the theory \<^verbatim>\<open>Isa_DOF\<close> which imports this theory. \<close>

theory Isa_DOF_core           (* Isabelle Document Ontology Framework: Core *)
  imports  Main  
           RegExpInterface    (* Interface to functional regular automata for monitoring *)
begin

text\<open> @{footnote \<open>sdf\<close>}, @{file "$ISABELLE_HOME/src/Pure/ROOT.ML"}\<close> 

section\<open>Primitive Markup Generators\<close>
ML\<open>

val docrefN   = "docref";    
val docclassN = "doc_class";
val onto_classN = "onto_class";

(** name components **)

val defN = "def"
val def_suffixN = "_" ^ defN
val defsN = defN ^ "s"
val instances_of_suffixN = "_instances"
val invariant_suffixN = "_inv"
val monitor_suffixN = "_monitor"
val instance_placeholderN = "\<sigma>"
val makeN = "make"
val schemeN = "_scheme"
val instanceN = "instance"
val monitor_infoN = "monitor_info"
val isa_transformerN = "isa_transformer"
val ml_invariantN = "ml_invariant"
val traceN = "trace"
val DOF_docitemN = "DOF.docitem"
\<close>

section\<open> A HomeGrown Document Type Management (the ''Model'') \<close>


ML\<open>
structure DOF_core =
 
struct

  datatype onto_class = Onto_Class of 
    {params         : (string * sort) list,
     name           : binding,
     virtual        : {virtual : bool}, 
     inherits_from  : (typ list * string) option,    (* imports *)
     attribute_decl : (binding*typ*term option)list, (* class local *)
     rejectS        : term list,
     rex            : term list,
     invs           : (binding * term) list  } (* monitoring regexps --- product semantics*)

  fun make_onto_class (params, name, virtual, inherits_from, attribute_decl , rejectS, rex, invs) =
    Onto_Class {params = params, name = name, virtual = virtual, inherits_from = inherits_from
                , attribute_decl = attribute_decl, rejectS = rejectS , rex = rex, invs = invs}

  structure Onto_Classes = Theory_Data
  (
    type T =  onto_class Name_Space.table;
    val empty : T = Name_Space.empty_table onto_classN;
    fun merge data : T = Name_Space.merge_tables data;
  );

  val get_onto_classes = Onto_Classes.get o Proof_Context.theory_of

  (* Get the Onto_Class object from its short name or long name *)
  fun get_onto_class_global name thy  =
    Name_Space.check (Context.Theory thy)
                      (get_onto_classes (Proof_Context.init_global thy)) (name, Position.none) |> #2

  fun markup2string s = Protocol_Message.clean_output s
                        |> Symbol.explode
                        |> List.filter (fn c => c <> Symbol.DEL)
                        |> String.concat

  fun get_name name =
     name |>  markup2string
          |> Symbol.explode_words |> split_last |> #2

  (* Get the Onto_Class object.
     The function does not use the abstract syntax of an onto_class.
     and relies entirely on the associated record created with the onto_class and its type.
     The function takes, for the name argument, a string that has the same form as
     the input of an ML \<^typ>\<open>\<close> anti-quotation to get a record type.
     To get the type of the record ('a, 'b) A, we'll use \<^typ>\<open>('a, 'b) A\<close>.
     So the name argument will be "('a, 'b) A" *) 
  (* does not take class synonyms into account *)
  fun get_onto_class_global' name thy  =
    let val name' = name |> get_name
    in Name_Space.check (Context.Theory thy)
                    (get_onto_classes (Proof_Context.init_global thy)) (name', Position.none) |> #2
    end

  (* Get the full-qualified name of an onto_class from its short name or long name *)
  fun get_onto_class_name_global name thy  =
    Name_Space.check (Context.Theory thy)
                      (get_onto_classes (Proof_Context.init_global thy)) (name, Position.none) |> #1

  (* Get the full-qualified name of an onto-class.
     The function does not use the abstract syntax of an onto_class.
     and relies entirely on the associated record created with the onto_class and its type.
     The function takes, for the name argument, a string that has the same form as
     the input of an ML \<^typ>\<open>\<close> anti-quotation to get a record type.
     To get the type of the record ('a, 'b) A, we'll use \<^typ>\<open>('a, 'b) A\<close>.
     So the name argument will be "('a, 'b) A". *)
  (* does not take class synonyms into account *)
  fun get_onto_class_name_global' name thy  =
    let val name' = name |> get_name
    in Name_Space.check (Context.Theory thy)
                    (get_onto_classes (Proof_Context.init_global thy)) (name', Position.none) |> #1
    end

  (* Get the full-qualified name of an onto-class,
     its string representation with arguments and sorts, and its type
     from its short or long name.
     To get the type of the record ('a::one, 'b) A, we'll use \<^typ>\<open>('a::one, 'b) A\<close>.
     So the name argument will be "('a::one, 'b) A" *)
  (* does not takes class synonyms into account *)
  fun get_onto_class_cid thy name =
    let val cid_typ = name |> Syntax.read_typ_global thy
        val (args, name') = name |> Symbol.explode_words |> split_last
        val name'' = (name', Position.none) |> Name_Space.check (Context.Theory thy)
                                               (get_onto_classes (Proof_Context.init_global thy))
                                              |> fst
        val args_cid = append args [name''] |> space_implode Symbol.space
    in ((name'', args_cid), cid_typ)
    end

  fun check_onto_class ctxt =
    #1 o Name_Space.check (Context.Proof ctxt) (get_onto_classes ctxt);

  fun add_onto_class name onto_class thy =
    thy |> Onto_Classes.map (Name_Space.define (Context.Theory thy) true (name, onto_class) #> #2);

  fun update_onto_class name onto_class thy =
    thy |> Onto_Classes.map (Name_Space.define (Context.Theory thy) false (name, onto_class) #> #2);

  fun map_onto_class_entry name f thy =
    thy |> Onto_Classes.map (Name_Space.map_table_entry (get_onto_class_name_global' name thy)
            (fn Onto_Class
                  {params, name, virtual, inherits_from, attribute_decl, rejectS , rex, invs} =>
              make_onto_class (f (params, name, virtual, inherits_from, attribute_decl,
                                  rejectS , rex, invs))));

  fun map_params name f =
    map_onto_class_entry name (fn (params, name, virtual, inherits_from, attribute_decl,
                                  rejectS , rex, invs) =>
      (f params, name, virtual, inherits_from, attribute_decl, rejectS , rex, invs))

  fun map_name name f =
    map_onto_class_entry name (fn (params, name, virtual, inherits_from, attribute_decl,
                                  rejectS , rex, invs) =>
      (params, f name, virtual, inherits_from, attribute_decl, rejectS , rex, invs))

  fun map_virtual name f =
    map_onto_class_entry name (fn (params, name, virtual, inherits_from, attribute_decl,
                                  rejectS , rex, invs) =>
      (params, name, f virtual, inherits_from, attribute_decl, rejectS , rex, invs))

  fun map_inherits_from name f =
    map_onto_class_entry name (fn (params, name, virtual, inherits_from, attribute_decl,
                                  rejectS , rex, invs) =>
      (params, name, virtual, f inherits_from, attribute_decl, rejectS , rex, invs))

  fun map_attribute_decl name f =
    map_onto_class_entry name (fn (params, name, virtual, inherits_from, attribute_decl,
                                  rejectS , rex, invs) =>
      (params, name, virtual, inherits_from, f attribute_decl, rejectS , rex, invs))

  fun map_rejectS name f =
    map_onto_class_entry name (fn (params, name, virtual, inherits_from, attribute_decl,
                                  rejectS , rex, invs) =>
      (params, name, virtual, inherits_from, attribute_decl, f rejectS , rex, invs))

  fun map_rex name f =
    map_onto_class_entry name (fn (params, name, virtual, inherits_from, attribute_decl,
                                  rejectS , rex, invs) =>
      (params, name, virtual, inherits_from, attribute_decl, rejectS , f rex, invs))

  fun map_invs name f =
    map_onto_class_entry name (fn (params, name, virtual, inherits_from, attribute_decl,
                                  rejectS , rex, invs) =>
      (params, name, virtual, inherits_from, attribute_decl, rejectS , rex, f invs))

  fun rep_onto_class cid thy = get_onto_class_global cid thy |> (fn Onto_Class rep => rep)

  fun params_of cid = #params o rep_onto_class cid
  fun name_of cid = #name o rep_onto_class cid
  fun virtual_of cid = #virtual o rep_onto_class cid
  fun inherits_from_of cid = #inherits_from o rep_onto_class cid
  fun attribute_decl_of cid = #attribute_decl o rep_onto_class cid
  fun rejectS_of cid = #rejectS o rep_onto_class cid
  fun rex_of cid = #rex o rep_onto_class cid
  fun invs_of cid = #invs o rep_onto_class cid

  fun print_onto_classes verbose ctxt =
    Pretty.big_list "Isabelle.DOF Onto_Classes:"
      (map (Pretty.marks_str o #1) (Name_Space.markups_table verbose ctxt (get_onto_classes ctxt)))
    |> Pretty.writeln;

  fun the_onto_class T i =
    (case Name_Space.lookup_key T i of
      SOME entry => entry
    | NONE => raise TYPE ("Unknown onto_class: " ^ quote i, [], []));


   val tag_attr = (\<^binding>\<open>tag_attribute\<close>, \<^Type>\<open>int\<close>, Mixfix.NoSyn)
        (* Attribute hidden to the user and used internally by isabelle_DOF.
           For example, this allows to add a specific id to a class
           to be able to reference the class internally.
        *)

   val default_cid = "text"    (* the top (default) document class: everything is a text.*)

   val default_cid_typ = \<^typ>\<open>unit\<close> (* top document class type *)

(* Due to the implementation, is_subclass0 is _NOT_ compatible with DOF classes type synonyms,
   so they must be resolved to full class names before use. *)
  fun is_subclass0 s t ctxt =
    let fun get id = if id = default_cid
                     then default_cid
                     else get_onto_class_name_global id (Proof_Context.theory_of ctxt)
        val s' = get s
        val t' = get t
        fun father_is_sub s = case get_onto_class_global s (Proof_Context.theory_of ctxt)  of 
                                  (Onto_Class {inherits_from=NONE, ...}) => s = t'
                                | (Onto_Class {inherits_from=SOME (_, s''), ...}) =>
                                    s'' = t' orelse father_is_sub s''
        val s'_defined = s' |> Name_Space.declared (get_onto_classes ctxt
                                                    |> Name_Space.space_of_table)
    in s' = t' orelse
       (t' = default_cid  andalso s'_defined) orelse
       (s' <> default_cid andalso father_is_sub s')
    end


  (* An instance of a document class. The input term and the value of an instance, a pair of terms,
     are the result of a future: type-checking of the attributes, evaluation of the value and check
     of the invariants can run in parallel to the following commands. Reading the terms of an 
     instance synchronizes with the future; the meta-data (defined, inline, cid, vcid) is always 
     available. *)
  datatype instance = Instance of 
    {defined: bool,
     inline: bool, 
     cid: string,
     vcid: string option,
     termNvalue: (term * term) future}

  val undefined_instance = "undefined_instance"

  val undefined_value = Free ("Undefined_Value", default_cid_typ)

  fun make_instance_future (defined, inline, cid, vcid, termNvalue) =
    Instance {defined = defined, inline = inline, cid = cid, vcid = vcid, termNvalue = termNvalue}

  (* the terms are known *)
  fun make_instance_value (defined, inline, cid, vcid, input_term_value) =
    make_instance_future (defined, inline, cid, vcid, Future.value input_term_value)

  (* The terms are the result of the closure, which is started here in a task if Isabelle runs 
     in parallel: errors of the task are reported at the position of the command (Execution.fork).
     Without parallelism, the closure is executed immediately and its errors abort the command. *)
  fun make_instance (defined, inline, cid, vcid, closure : unit -> term * term) =
    make_instance_future (defined, inline, cid, vcid,
      if Future.proofs_enabled 1
      then Execution.fork {name = DOF_docitemN, pos = Position.thread_data (), pri = ~1} closure
      else Future.value (closure ()))

  structure Instances = Theory_Data
  (
    type T =  instance Name_Space.table;
    val empty : T = Name_Space.empty_table instanceN;
    fun merge data : T = Name_Space.merge_tables data;
  );

  val get_instances = Instances.get o Proof_Context.theory_of

  fun get_instance_global oid thy  =
    Name_Space.check (Context.Theory thy)
                      (get_instances (Proof_Context.init_global thy)) (oid, Position.none) |> #2

  (* The futures of the instances are joined at the end of a theory: their errors surface, and no 
     unfinished future remains in a finished theory. *)
  fun join_instances thy =
    let val unfinished = Instances.get thy |> Name_Space.dest_table
                         |> filter (fn (_, Instance {termNvalue, ...}) => not (Future.is_finished termNvalue))
    in if null unfinished then NONE
       else SOME (fold (fn (key, Instance {defined, inline, cid, vcid, termNvalue}) =>
                          Instances.map (Name_Space.map_table_entry key (K 
                            (make_instance_value (defined, inline, cid, vcid, Future.join termNvalue)))))
                       unfinished thy)
    end

  (* The join is registered once for each theory (begin hooks are applied until none of them 
     changes the theory), c.f. the initialization of the data of the code generator. *)
  structure Join_Registered = Theory_Data
  (
    type T = string;
    val empty : T = "";
    fun merge (a, _) : T = a;
  );

  val _ = Theory.setup (Theory.at_begin (fn thy =>
            let val name = Context.theory_long_name thy
            in if Join_Registered.get thy = name then NONE
               else SOME (thy |> Join_Registered.put name |> Theory.at_end join_instances)
            end))

  fun get_instance_name_global oid thy  =
    Name_Space.check (Context.Theory thy)
                      (get_instances (Proof_Context.init_global thy)) (oid, Position.none) |> #1

  fun check_instance ctxt =
    #1 o Name_Space.check (Context.Proof ctxt) (get_instances ctxt);

  fun add_instance name instance thy =
    thy |> Instances.map (Name_Space.define (Context.Theory thy) true (name, instance) #> #2);

  fun update_instance name instance thy =
    thy |> Instances.map (Name_Space.define (Context.Theory thy) false (name, instance) #> #2);

  fun map_instance_entry name f thy =
    thy |> Instances.map (Name_Space.map_table_entry (get_instance_name_global name thy)
            (fn Instance {defined, inline, cid, vcid, termNvalue} =>
              make_instance_future (f (defined, inline, cid, vcid, termNvalue))));

  fun map_defined name f =
    map_instance_entry name (fn (defined, inline, cid, vcid, tv) =>
      (f defined, inline, cid, vcid, tv))

  fun map_inline name f =
    map_instance_entry name (fn (defined, inline, cid, vcid, tv) =>
      (defined, f inline, cid, vcid, tv))

  fun map_cid name f =
    map_instance_entry name (fn (defined, inline, cid, vcid, tv) =>
      (defined, inline, f cid, vcid, tv))

  fun map_vcid name f =
    map_instance_entry name (fn (defined, inline, cid, vcid, tv) =>
      (defined, inline, cid, f vcid, tv))

  (* lazy: the terms are mapped without waiting for them *)
  fun map_input_term name f =
    map_instance_entry name (fn (defined, inline, cid, vcid, tv) =>
      (defined, inline, cid, vcid, Future.map (apfst f) tv))

  fun map_value_lazy name f =
    map_instance_entry name (fn (defined, inline, cid, vcid, tv) =>
      (defined, inline, cid, vcid, Future.map (apsnd f) tv))

  (* strict: synchronizes with the terms of the instance, errors of f abort the command *)
  fun map_value name f =
    map_instance_entry name (fn (defined, inline, cid, vcid, tv) =>
      let val (input_term, value) = Future.join tv
      in (defined, inline, cid, vcid, Future.value (input_term, f value)) end)

  fun map_input_term_value name f g thy =
    thy |> map_input_term name f |> map_value name g

  fun print_instances verbose ctxt =
    Pretty.big_list "Isabelle.DOF Instances:"
      (map (Pretty.marks_str o #1) (Name_Space.markups_table verbose ctxt (get_instances ctxt)))
    |> Pretty.writeln;

  fun the_instance T i =
    (case Name_Space.lookup_key T i of
      SOME entry => entry
    | NONE => raise TYPE ("Unknown instance: " ^ quote i, [], []));

  fun rep_instance oid thy = get_instance_global oid thy |> (fn Instance rep => rep)

  fun defined_of oid = #defined o rep_instance oid
  fun input_term_of oid = fst o Future.join o #termNvalue o rep_instance oid
  fun value_of oid = snd o Future.join o #termNvalue o rep_instance oid
  fun inline_of oid = #inline o rep_instance oid
  fun cid_of oid = #cid o rep_instance oid
  fun vcid_of oid = #vcid o rep_instance oid


  datatype isa_transformer = ISA_Transformer of 
    {check     : (theory -> term * typ * Position.T -> string -> term option),
     elaborate : (theory -> string -> typ -> term option -> Position.T -> term)}

  fun make_isa_transformer (check, elaborate) =
    ISA_Transformer {check = check, elaborate = elaborate}

  structure ISA_Transformers = Theory_Data
  (
    type T = isa_transformer Name_Space.table;
    val empty : T = Name_Space.empty_table isa_transformerN;
    fun merge data : T = Name_Space.merge_tables data;
  );

  val get_isa_transformers = ISA_Transformers.get o Proof_Context.theory_of

  fun get_isa_transformer_global id thy  =
    Name_Space.check (Context.Theory thy)
                    (get_isa_transformers (Proof_Context.init_global thy)) (id, Position.none) |> #2

  fun get_isa_transformer_name_global id thy  =
    Name_Space.check (Context.Theory thy)
                    (get_isa_transformers (Proof_Context.init_global thy)) (id, Position.none) |> #1

  fun check_isa_transformer ctxt =
    #1 o Name_Space.check (Context.Proof ctxt) (get_isa_transformers ctxt);

  fun add_isa_transformer name isa_transformer thy =
    thy |> ISA_Transformers.map
      (Name_Space.define (Context.Theory thy) true (name, isa_transformer) #> #2);

  fun update_isa_transformer name isa_transformer thy =
    thy |> ISA_Transformers.map
      (Name_Space.define (Context.Theory thy) false (name, isa_transformer) #> #2);

  fun map_isa_transformer_entry name f thy =
    thy |> ISA_Transformers.map (Name_Space.map_table_entry (get_isa_transformer_name_global name thy)
            (fn ISA_Transformer {check, elaborate} => make_isa_transformer (f (check, elaborate))));

  fun map_check name f =
    map_isa_transformer_entry name (fn (check, elaborate) => (f check, elaborate))

  fun map_elaborate name f =
    map_isa_transformer_entry name (fn (check, elaborate) => (check, f elaborate))

  fun rep_isa_transformer id thy = get_isa_transformer_global id thy
                                   |> (fn ISA_Transformer rep => rep)

  fun check_of id = #check o rep_isa_transformer id
  fun elaborate_of id = #elaborate o rep_isa_transformer id

  fun print_isa_transformers verbose ctxt =
    Pretty.big_list "Isabelle.DOF ISA_Transformers:"
      (map (Pretty.marks_str o #1) (Name_Space.markups_table verbose ctxt (get_isa_transformers ctxt)))
    |> Pretty.writeln;

  fun the_isa_transformer T i =
    (case Name_Space.lookup_key T i of
      SOME entry => entry
    | NONE => raise TYPE ("Unknown isa_transformer: " ^ quote i, [], []));


  datatype ml_invariant = ML_Invariant of
    {check : string -> {is_monitor:bool} -> Context.generic -> bool
     , class : string}

  fun make_ml_invariant (check, class) =
    ML_Invariant {check = check, class = class}

  structure ML_Invariants = Theory_Data
  (
    type T = (ml_invariant Name_Space.table * ml_invariant Name_Space.table)
             * ml_invariant Name_Space.table;
    val empty : T = ((Name_Space.empty_table ml_invariantN
                      , Name_Space.empty_table ("opening_" ^ ml_invariantN))
                      , Name_Space.empty_table ("closing_" ^ ml_invariantN));
    fun merge (((ml_invariants1, opening_ml_invariants1), closing_ml_invariants1)
                , ((ml_invariants2, opening_ml_invariants2), closing_ml_invariants2)) =
        ((Name_Space.merge_tables (ml_invariants1, ml_invariants2)
        , Name_Space.merge_tables (opening_ml_invariants1, opening_ml_invariants2))
        , Name_Space.merge_tables (closing_ml_invariants1, closing_ml_invariants2));
  );

  fun get_invariants which = which o ML_Invariants.get o Proof_Context.theory_of

  val get_ml_invariants = get_invariants (fst o fst)

  val get_opening_ml_invariants = get_invariants (snd o fst)

  val get_closing_ml_invariants = get_invariants snd

  fun get_invariant_global which cid thy  =
    Name_Space.check (Context.Theory thy)
                  (get_invariants which (Proof_Context.init_global thy)) (cid, Position.none) |> #2

  val get_ml_invariant_global = get_invariant_global (fst o fst)

  val get_opening_ml_invariant_global = get_invariant_global (snd o fst)

  val get_closing_ml_invariant_global = get_invariant_global snd

  fun get_invariant_name_global which cid thy  =
    Name_Space.check (Context.Theory thy)
                  (get_invariants which (Proof_Context.init_global thy)) (cid, Position.none) |> #1

  val get_ml_invariant_name_global = get_invariant_name_global (fst o fst)

  val get_opening_ml_invariant_name_global = get_invariant_name_global (snd o fst)

  val get_closing_ml_invariant_name_global = get_invariant_name_global snd

  fun check_invariant which ctxt =
    #1 o Name_Space.check (Context.Proof ctxt) (get_invariants which ctxt);

  val check_ml_invariant = check_invariant (fst o fst)

  val check_opening_ml_invariant = check_invariant (snd o fst)

  val check_closing_ml_invariant = check_invariant snd

  fun add_invariant (get, ap) name invariant thy =
    let
      val table =
        ML_Invariants.get thy |> get
                              |> (Name_Space.define (Context.Theory thy) true (name, invariant))
                              |> snd
    in (ML_Invariants.map o ap) (K table) thy end

  val add_ml_invariant = add_invariant (fst o fst, apfst o apfst)

  val add_opening_ml_invariant = add_invariant (snd o fst, apfst o apsnd)

  val add_closing_ml_invariant = add_invariant (snd, apsnd)

  fun update_invariant (get, ap) name invariant thy =
    let
      val table =
        ML_Invariants.get thy |> get
                              |> (Name_Space.define (Context.Theory thy) false (name, invariant))
                              |> snd
    in (ML_Invariants.map o ap) (K table) thy end

  val update_ml_invariant = update_invariant (fst o fst, apfst o apfst)

  val update_opening_ml_invariant = update_invariant (snd o fst, apfst o apsnd)

  val update_closing_ml_invariant = update_invariant (snd, apsnd)

  fun map_invariant_entry (get, ap) name f thy =
    thy |> (ML_Invariants.map o ap) (Name_Space.map_table_entry (get_invariant_name_global get name thy)
            (fn ML_Invariant {check, class} => make_ml_invariant (f (check, class))));

  val map_ml_invariant_entry = map_invariant_entry (fst o fst, apfst o apfst)

  val map_opening_ml_invariant_entry = map_invariant_entry (snd o fst , apfst o apsnd)

  val map_closing_ml_invariant_entry = map_invariant_entry (snd, apsnd)

  fun map_invariant_check (get, ap) name f =
    map_invariant_entry (get, ap) name (fn (check, class) => (f check, class))

  val map_ml_invariant_check = map_invariant_check (fst o fst, apfst o apfst)

  val map_opening_ml_invariant_check = map_invariant_check (snd o fst, apfst o apsnd)

  val map_closing_ml_invariant_check = map_invariant_check (snd, apsnd)

  fun map_invariant_class (get, ap) name f =
    map_invariant_entry (get, ap) name (fn (check, class) => (check, f class))

  val map_ml_invariant_class = map_invariant_class (fst o fst, apfst o apfst)

  val map_opening_ml_invariant_class = map_invariant_class (snd o fst , apfst o apsnd)

  val map_closing_ml_invariant_class = map_invariant_class (snd, apsnd)

  fun rep_invariant which id thy = get_invariant_global which id thy |> (fn ML_Invariant rep => rep)

  val rep_ml_invariant = rep_invariant (fst o fst)

  val rep_opening_ml_invariant = rep_invariant (snd o fst)

  val rep_closing_ml_invariant = rep_invariant snd

  fun invariant_check_of which id = #check o rep_invariant which id

  val ml_invariant_check_of = invariant_check_of (fst o fst)

  val opening_ml_invariant_check_of = invariant_check_of (snd o fst)

  val closing_ml_invariant_check_of = invariant_check_of snd

  fun invariant_class_of which id = #class o rep_invariant which id

  val ml_invariant_class_of = invariant_class_of (fst o fst)

  val opening_ml_invariant_class_of = invariant_class_of (snd o fst)

  val closing_ml_invariant_class_of = invariant_class_of snd

  fun print_invariants which verbose ctxt =
    Pretty.big_list "Isabelle.DOF ML_Invariants:"
      (map (Pretty.marks_str o #1) (Name_Space.markups_table verbose ctxt (get_invariants which ctxt)))
    |> Pretty.writeln;

  val print_ml_invariants = print_invariants (fst o fst)

  val print_opening_ml_invariants = print_invariants (snd o fst)

  val print_closing_ml_invariants = print_invariants snd

  fun the_invariant which thy i =
    (case (ML_Invariants.get thy |> which |> Name_Space.lookup_key) i of
      SOME entry => entry
    | NONE => raise TYPE ("Unknown ml_invariant: " ^ quote i, [], []));

  val the_ml_invariant = the_invariant (fst o fst)

  val the_opening_ml_invariant = the_invariant (snd o fst)

  val the_closing_ml_invariant = the_invariant snd

  (* Monitor infos are not integrated to an instance datatype
     to avoid issues when comparing objects.
     Indeed automata do not have an equality type and then,
     should two instances with monitor infos be compared, an error will be triggered.
     So monitor infos are defined in their own name space.
     They are declared when opening a monitor and have the same
     reference (the key of the name space table) as their related monitor instance:
     the name of the instance prefixed by the theory. *)
  datatype monitor_info = Monitor_Info of 
    {accepted_cids : RegExpInterface.env,
     rejected_cids : RegExpInterface.env,
     automatas     : RegExpInterface.automaton list}


  fun make_monitor_info (accepted_cids, rejected_cids, automatas) =
    Monitor_Info {accepted_cids = accepted_cids,
                  rejected_cids = rejected_cids,
                  automatas = automatas}

  structure Monitor_Info = Theory_Data
  (
    type T =  monitor_info Name_Space.table;
    val empty : T = Name_Space.empty_table monitor_infoN;
    fun merge data : T = Name_Space.merge_tables data;
  );

  val get_monitor_infos = Monitor_Info.get o Proof_Context.theory_of

  fun get_monitor_info_global oid thy  =
    Name_Space.check (Context.Theory thy)
                      (get_monitor_infos (Proof_Context.init_global thy)) (oid, Position.none) |> #2

  fun get_monitor_info_name_global oid thy  =
    Name_Space.check (Context.Theory thy)
                      (get_monitor_infos (Proof_Context.init_global thy)) (oid, Position.none) |> #1

  fun check_monitor_info ctxt =
    #1 o Name_Space.check (Context.Proof ctxt) (get_monitor_infos ctxt);

  fun add_monitor_info name monitor_info thy =
    thy |> Monitor_Info.map
      (Name_Space.define (Context.Theory thy) true (name, monitor_info) #> #2);

  fun update_monitor_info name monitor_info thy =
    thy |> Monitor_Info.map
      (Name_Space.define (Context.Theory thy) false (name, monitor_info) #> #2);

  fun map_monitor_info_entry name f thy =
    thy |> Monitor_Info.map
            (Name_Space.map_table_entry (get_monitor_info_name_global name thy)
            (fn Monitor_Info {accepted_cids, rejected_cids, automatas} =>
              make_monitor_info (f (accepted_cids, rejected_cids, automatas))));

  fun map_monitor_info_accepted_cids name f =
    map_monitor_info_entry name (fn (accepted_cids, rejected_cids, automatas) =>
                                  (f accepted_cids, rejected_cids, automatas))

  fun map_monitor_info_rejected_cids name f =
    map_monitor_info_entry name (fn (accepted_cids, rejected_cids, automatas) =>
                                  (accepted_cids, f rejected_cids, automatas))

  fun map_monitor_info_automatas name f =
    map_monitor_info_entry name (fn (accepted_cids, rejected_cids, automatas) =>
                                  (accepted_cids, rejected_cids, f automatas))

  fun rep_monitor_info id thy = get_monitor_info_global id thy |> (fn Monitor_Info rep => rep)

  fun accepted_cids_of id = #accepted_cids o rep_monitor_info id
  fun rejected_cids_of id = #rejected_cids o rep_monitor_info id
  fun automatas_of id = #automatas o rep_monitor_info id
  fun alphabet_of id thy = (accepted_cids_of id thy) @ (rejected_cids_of id thy)

  fun print_monitors_infos verbose ctxt =
    Pretty.big_list "Isabelle.DOF Monitor_Infos:"
      (map (Pretty.marks_str o #1) (Name_Space.markups_table verbose ctxt (get_monitor_infos ctxt)))
    |> Pretty.writeln;

  fun the_monitor_info T i =
    (case Name_Space.lookup_key T i of
      SOME entry => entry
    | NONE => raise TYPE ("Unknown monitor_info: " ^ quote i, [], []));


(* doc-class-name management: We still use the record-package for internally 
   representing doc-classes. The main motivation is that "links" to entities are
   types over doc-classes, *types* in the Isabelle sense, enriched by additional data.
   This has the advantage that the type-inference can be abused to infer long-names
   for doc-class-names. Note, however, that doc-classes are currently implemented
   by non-polymorphic records only; this means that the extensible "_ext" versions
   of type names must be reduced to qualifier names only. The used Syntax.parse_typ 
   handling the identification does that already. *)
 
fun is_subclass (ctxt) s t = is_subclass0 s t ctxt
fun is_subclass_global thy s t = let val ctxt = Proof_Context.init_global thy
                                 in  is_subclass0  s t ctxt end

fun check_regexps term = 
    let val _ = case fold_aterms  Term.add_free_names term [] of
                   n::_ => error("No free variables allowed in monitor regexp:" ^ n)
                 | _ => ()  
        val _ = case fold_aterms  Term.add_var_names term [] of
                   (n,_)::_ => error("No schematic variables allowed in monitor regexp:" ^ n)
                 | _ => ()
        (* Missing: Checks on constants such as undefined, ... *)
    in  term end

fun check_reject_atom term = 
    let val _ = case fold_aterms  Term.add_free_names term [] of
                   n::_ => error("No free variables allowed in monitor regexp:" ^ n)
                 | _ => ()  
        val _ = case fold_aterms  Term.add_var_names term [] of
                   (n,_)::_ => error("No schematic variables allowed in monitor regexp:" ^ n)
                 | _ => ()
        (* Missing: Checks on constants such as undefined, ... *)
    in  term end


fun define_doc_class_global (params', binding) parent fields rexp reject_Atoms invs virtual thy  = 
(* This operation is executed in a context where the record has already been defined, but
   its conversion into a class is not yet done. *)
    let val rejectS = map (Syntax.read_term_global thy) reject_Atoms;
        val _ = map (check_reject_atom) rejectS; 
        val reg_exps = map (Syntax.read_term_global thy) rexp;
        val _ = map check_regexps reg_exps
        val _ = if not(null rejectS) andalso (null reg_exps) 
                then  error ("reject clause requires accept clause ! " ) else ();
        val _ = if invs |> map (Binding.name_of o fst) |> has_duplicates (uncurry equal)
                then invs |> hd |> fst |> Binding.pos_of
                     |> (fn pos => error("invariant labels must be unique"^  Position.here pos)) 
                else ()
        val invs' = map (apsnd(Syntax.read_term_global thy)) invs 
    in  thy |> add_onto_class binding (make_onto_class (params', binding, virtual, parent, fields
                                                        , rejectS, reg_exps, invs'))
    end

fun define_object_global {define = define} (binding, instance) thy  = 
  let
    val oid = Binding.name_of binding
    val pos = Binding.pos_of binding
    val _ = if oid = undefined_instance
            then error (oid ^ ": This name is reserved by the implementation" ^ Position.here pos)
            else ()
    val Instance {inline, cid, vcid, termNvalue, ...} = instance
    val instance' = make_instance_future (define, inline, cid, vcid, termNvalue)
  in case try (fn () => Name_Space.check (Context.Theory thy)
                         (get_instances (Proof_Context.init_global thy)) (oid, Position.none)) () of
       NONE => (* declare instance using declare_reference* or else define instance *)
               add_instance binding instance' thy
     | SOME (oid', Instance {defined, ...}) =>
         if define
         then if defined
              then (* trigger error when adding already defined instance *)
                   add_instance binding instance' thy
              else (* define already declared instance *)
                   thy |> Instances.map (Name_Space.map_table_entry oid' (K instance'))
         else (* trigger error with declare_reference* when declaring already declared instance *)
              add_instance binding instance' thy
  end

fun get_attributes_local cid ctxt =
  if cid = default_cid then []
  else let val cid_long = get_onto_class_name_global cid (Proof_Context.theory_of ctxt)
       in 
       case get_onto_class_global cid_long (Proof_Context.theory_of ctxt) of
           Onto_Class {inherits_from=NONE,
                       attribute_decl = X, ...} => [(cid_long,X)]
         | Onto_Class {inherits_from=SOME(_, father), attribute_decl = X, ...} =>
            get_attributes_local father ctxt @ [(cid_long,X)]
       end

fun get_attributes cid thy = get_attributes_local cid (Proof_Context.init_global thy)


fun get_all_attributes_local cid ctxt =
 (tag_attr, get_attributes_local cid ctxt)

fun get_all_attributes cid thy = get_all_attributes_local cid (Proof_Context.init_global thy)


type attributes_info = { def_occurrence : string,
                         def_pos        : Position.T,
                         long_name      : string,
                         typ            : typ
                       }

fun get_attribute_info_local (*long*)cid attr ctxt : attributes_info option=
    let val hierarchy = get_attributes_local cid ctxt  (* search in order *)
        fun found (s,L) = case find_first (fn (bind,_,_) => Binding.name_of bind = attr) L of
                            NONE => NONE
                          | SOME X => SOME(s,X)
    in  case get_first found hierarchy of
           NONE => NONE
         | SOME (cid',(bind, ty,_)) => SOME({def_occurrence = cid,
                                             def_pos = Binding.pos_of bind,
                                             long_name = cid'^"."^(Binding.name_of bind), 
                                             typ = ty})
    end

fun get_attribute_info (*long*)cid attr thy =
  get_attribute_info_local cid attr (Proof_Context.init_global thy)

fun get_attribute_defaults (* long*)cid thy = 
    let val attrS = flat(map snd (get_attributes cid thy))
        fun trans (_,_,NONE) = NONE
           |trans (na,ty,SOME def) =SOME(na,ty, def)
    in  map_filter trans attrS end


fun binding_from_pos get_objects get_object_name name thy  =
  let
    val ns = get_objects (Proof_Context.init_global thy)
                         |> Name_Space.space_of_table 
    val pos = Name_Space.the_entry_pos ns (get_object_name name thy)
  in if Long_Name.is_qualified name
     then Binding.make (Long_Name.base_name name, pos)
     else Binding.make (name, pos)end

fun binding_from_onto_class_pos name thy  =
  binding_from_pos get_onto_classes get_onto_class_name_global name thy

fun binding_from_instance_pos name thy  =
  binding_from_pos get_instances get_instance_name_global name thy

fun check_invs get_ml_invs invariant_class_of invariant_check_of cid_long oid is_monitor thy =
  thy |> Context.Theory
      |> (fn ctxt =>
            let val invs = get_ml_invs (Proof_Context.init_global thy)
                                              |> Name_Space.dest_table
                val checks = invs |> filter (fn (name, _) => 
                                                equal (invariant_class_of name thy) cid_long)
                                  |> map (fn (name, _) => invariant_check_of name thy)
                                  |> map (fn check => check oid is_monitor ctxt)
            in (forall I checks) end)

val check_ml_invs = check_invs get_ml_invariants ml_invariant_class_of ml_invariant_check_of

val check_opening_ml_invs =
  check_invs get_opening_ml_invariants opening_ml_invariant_class_of opening_ml_invariant_check_of

val check_closing_ml_invs =
  check_invs get_closing_ml_invariants closing_ml_invariant_class_of closing_ml_invariant_check_of

(* Output name for LaTeX macros.
   Also rewrite "." to allow macros with objects long names
   and "\<^sub>" allowed in name bindings and then in instance names *)
val output_name = Symbol.explode
                  #> map (fn s => if equal s Symbol.sub then "SUB" else s)
                  #> implode
                  #> translate_string (fn "." => "DOT" | s => s)
                  #> Latex.output_name

val ISA_prefix = "Isabelle_DOF_"

val doc_class_prefix = ISA_prefix ^ "doc_class_"

val long_doc_class_prefix = ISA_prefix ^ "long_doc_class_"

fun is_ISA s = String.isPrefix ISA_prefix (Long_Name.base_name s)

val strip_positions_is_ISA =
  let
    fun strip ((t as Const ("_type_constraint_", \<^Type>\<open>fun A _\<close>)) $ (u as Const (s,_))) =
          if Term_Position.detect_positionT A andalso is_ISA s then u else t $ u
      | strip (t $ u) = strip t $ strip u
      | strip (Abs (a, T, b)) = Abs (a, T, strip b)
      | strip t = t;
  in strip end;

fun transduce_term_global {mk_elaboration=mk_elaboration} (term,pos) thy =
    (* pre: term should be fully typed in order to allow type-related term-transformations *)
    let val ctxt = Proof_Context.init_global thy
        val tab = get_isa_transformers ctxt  
        fun T(Const(s,ty) $ t) =
                if is_ISA s
                then let val name = check_isa_transformer ctxt (s, Position.none)
                         val (_, ISA_Transformer {check, elaborate}) = the_isa_transformer tab name
                     in case check thy (t,ty,pos) s of
                            NONE => Const(s,ty) $ t
                            (* checking isa, may raise error though. *)
                         | SOME t => if mk_elaboration 
                                     then elaborate thy s ty (SOME t) pos
                                     else Const(s,ty) $ t
                                     (* transforming isa *)
                     end
                else (Const(s,ty) $ (T t))
          | T(t1 $ t2) = T(t1) $ T(t2)
          | T(Const(s,ty)) =
                if is_ISA s
                then 
                  let val name = check_isa_transformer ctxt (s, Position.none)
                      val (_, ISA_Transformer {elaborate, ...}) = the_isa_transformer tab name
                  in if mk_elaboration 
                     then elaborate thy s ty NONE pos
                     else Const(s, ty)
                     (* transforming isa *)
                  end
                else Const(s, ty)
          | T(Abs(s,ty,t)) = Abs(s,ty,T t)
          | T t = t
    in T (strip_positions_is_ISA term) end

(* Elaborate an Isabelle_DOF term-antiquotation from an only parsed-term (not checked) *)
fun parsed_elaborate ctxt pos  =
  let
    fun elaborate (Const(s,ty) $ t) =
            if is_ISA s
            then Syntax.check_term ctxt (Const(s, ty) $ t)
                 |> (fn t => transduce_term_global {mk_elaboration=true} (t , pos)
                                      (Proof_Context.theory_of ctxt))
            else (Const(s,ty) $ (elaborate t))
      | elaborate (t1 $ t2) = elaborate (t1) $ elaborate (t2)
      | elaborate (Const(s,ty)) =
            if is_ISA s
            then Syntax.check_term ctxt (Const(s, ty))
                 |> (fn t => transduce_term_global {mk_elaboration=true} (t , pos)
                                      (Proof_Context.theory_of ctxt))
            else Const(s,ty)
      | elaborate (Abs(s,ty,t)) = Abs (s,ty,elaborate t)
      | elaborate t = t
  in elaborate o strip_positions_is_ISA end

fun elaborate_term' ctxt parsed_term = parsed_elaborate ctxt Position.none parsed_term

fun elaborate_term ctxt term = transduce_term_global {mk_elaboration=true}
                                                              (term , Position.none)
                                                              (Proof_Context.theory_of ctxt)

fun check_term ctxt term = transduce_term_global {mk_elaboration=false}
                                                              (term , Position.none)
                                                              (Proof_Context.theory_of ctxt)

(* Check an Isabelle_DOF term-antiquotation from an only parsed-term (not checked) *)
fun parsed_check ctxt pos =
  let
    fun check (Const(s,ty) $ t) =
            if is_ISA s
            then let val _ = Syntax.check_term ctxt (Const(s, ty) $ t)
                             |> (fn t => transduce_term_global {mk_elaboration=false} (t , pos)
                                      (Proof_Context.theory_of ctxt))
                 in (Const(s,ty) $ (check t)) end
            else (Const(s,ty) $ (check t))
      | check (t1 $ t2) = check (t1) $ check (t2)
      | check (Const(s,ty)) =
            if is_ISA s
            then let val _ = Syntax.check_term ctxt (Const(s, ty))
                             |> (fn t => transduce_term_global {mk_elaboration=false} (t , pos)
                                      (Proof_Context.theory_of ctxt))
                 in Const(s,ty) end
            else Const(s,ty)
      | check (Abs(s,ty,t)) = Abs (s,ty,check t)
      | check t = t
  in check o strip_positions_is_ISA end

fun check_term' ctxt parsed_term = parsed_check ctxt Position.none parsed_term

fun prep_decls prep_var raw_vars ctxt =
  let
    val (vars, ctxt') = fold_map prep_var raw_vars ctxt;
    val (xs, ctxt'') = ctxt'
      |> Context_Position.set_visible false
      |> Proof_Context.add_fixes vars
      ||> Context_Position.restore_visible ctxt';
    val _ =
      (map (Binding.pos_of o #1) vars ~~
        map (Variable.markups_entity_def ctxt'' #> map (apsnd (Properties.remove Markup.kindN))) xs)
      |> maps (fn (p, ms) => map (pair p) ms)
      |> Context_Position.reports ctxt''
  in ((vars, xs), ctxt'') end;

fun print_doc_class_tree ctxt P T = 
    let val classes = Name_Space.dest_table (get_onto_classes ctxt)
        fun is_class_son X (_, onto_class) =
          let val Onto_Class inherits_from = onto_class
          in (inherits_from |> #inherits_from) = X end
        fun tree _ [] = ""
           |tree lev ((n,_)::S) = (if P(lev,n) 
                                  then "."^Int.toString lev^" "^(T n)^"{...}.\n"
                                       ^ (tree(lev + 1)(filter(is_class_son(SOME([],n))) classes))
                                  else "."^Int.toString lev^" ... \n") 
                                  ^ (tree lev S)
        val roots = filter(is_class_son NONE) classes
    in  ".0 .\n" ^ tree 1 roots end

val (object_value_debug, object_value_debug_setup)
     = Attrib.config_bool \<^binding>\<open>object_value_debug\<close> (K false);

val (strict_monitor_checking, strict_monitor_checking_setup)
     = Attrib.config_bool \<^binding>\<open>strict_monitor_checking\<close> (K false);

val (free_class_in_monitor_checking, free_class_in_monitor_checking_setup)
     = Attrib.config_bool \<^binding>\<open>free_class_in_monitor_checking\<close> (K false);

val (free_class_in_monitor_strict_checking, free_class_in_monitor_strict_checking_setup)
     = Attrib.config_bool \<^binding>\<open>free_class_in_monitor_strict_checking\<close> (K false);

val (invariants_checking, invariants_checking_setup) 
     = Attrib.config_bool \<^binding>\<open>invariants_checking\<close> (K true);

val (invariants_strict_checking, invariants_strict_checking_setup) 
     = Attrib.config_bool \<^binding>\<open>invariants_strict_checking\<close> (K false);

val (invariants_checking_with_tactics, invariants_checking_with_tactics_setup) 
     = Attrib.config_bool \<^binding>\<open>invariants_checking_with_tactics\<close> (K false);

val (monitor_trace_fast, monitor_trace_fast_setup)
     = Attrib.config_bool \<^binding>\<open>monitor_trace_fast\<close> (K true);
val (invariants_static_eval, invariants_static_eval_setup)
     = Attrib.config_bool \<^binding>\<open>invariants_static_eval\<close> (K true);
val (object_value_fast, object_value_fast_setup)
     = Attrib.config_bool \<^binding>\<open>object_value_fast\<close> (K true);
val (invariants_timeout, invariants_timeout_setup)
     = Attrib.config_real \<^binding>\<open>invariants_timeout\<close> (K 0.0);
val (invariants_parallel, invariants_parallel_setup)
     = Attrib.config_bool \<^binding>\<open>invariants_parallel\<close> (K true);
val (invariants_batch, invariants_batch_setup)
     = Attrib.config_bool \<^binding>\<open>invariants_batch\<close> (K true);
val (monitor_trace_check, monitor_trace_check_setup)
     = Attrib.config_bool \<^binding>\<open>monitor_trace_check\<close> (K false);

end (* struct *)

\<close>

setup\<open>DOF_core.monitor_trace_fast_setup
      #> DOF_core.invariants_batch_setup
      #> DOF_core.invariants_parallel_setup
      #> DOF_core.invariants_timeout_setup
      #> DOF_core.object_value_fast_setup
      #> DOF_core.invariants_static_eval_setup
      #> DOF_core.monitor_trace_check_setup
      #> DOF_core.object_value_debug_setup
      #> DOF_core.strict_monitor_checking_setup
      #> DOF_core.free_class_in_monitor_checking_setup
      #> DOF_core.free_class_in_monitor_strict_checking_setup
      #> DOF_core.invariants_checking_setup
      #> DOF_core.invariants_strict_checking_setup
      #> DOF_core.invariants_checking_with_tactics_setup\<close>
end
