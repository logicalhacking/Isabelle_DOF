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

chapter \<open>The Document Ontology Framework: The Ontology Definition Language\<close>

text\<open> The commands of the Ontology Definition Language (ODL): document classes, their attributes, invariants and monitors, and ontology morphisms. \<close>

theory Isa_DOF_ODL   (* ODL *)
  imports Isa_DOF_Onto_Text_Antiquotations
  keywords "accepts"  "rejects" "invariant"
  and      "doc_class"          "onto_class" (* a syntactic alternative *)
           "onto_morphism"                                 :: thy_decl
  and      "to"
begin

section\<open> Syntax for Ontologies (the '' View'' Part III) \<close> 
ML\<open>
structure OntoParser = 
struct

fun read_parent NONE ctxt = (NONE, ctxt)
  | read_parent (SOME raw_T) ctxt =
      (case Proof_Context.read_typ_abbrev ctxt raw_T of
        Type (name, Ts) => (SOME (Ts, name), fold Variable.declare_typ Ts ctxt)
      | T => error ("Bad parent record specification: " ^ Syntax.string_of_typ ctxt T));


fun read_fields raw_fields ctxt =
    let
      val fields' = raw_fields |> map (apfst (fn (b, ty, mx) => (b, Syntax.read_typ ctxt ty, mx)))
                               |> map (apsnd (Option.map (Syntax.parse_term ctxt #> DOF_core.elaborate_term' ctxt)))
      fun check_default ctxt ((b, ty, _), SOME trm) = 
        let val parsed_prop = Const (\<^const_name>\<open>Pure.eq\<close>, dummyT) $ Free (Binding.name_of b, dummyT) $ trm
            val raw_vars = [(b, SOME ty, NoSyn)]
            val (_, vars_ctxt) = DOF_core.prep_decls Proof_Context.cert_var raw_vars ctxt
            (* check typ unification *)
            val _  = Syntax.check_prop vars_ctxt parsed_prop
        in () end
                                         (* BAD STYLE : better would be catching exn. *) 
        | check_default _ (_, NONE)= ()
      val _ = map (check_default ctxt) fields'
      val ctxt' = fields' |> map (#2 o fst) |> (fn Ts => fold Variable.declare_typ Ts ctxt);
    in (map fst fields', map snd fields', ctxt') end;

fun def_cmd (decl, spec, prems, params) lthy =
  let
    val ((lhs as Free (x, T), _), lthy') = Specification.definition {verbose = false} decl params prems spec lthy;
    val lhs' = Morphism.term (Local_Theory.target_morphism lthy') lhs;
    val _ =
      Proof_Display.print_consts {verbose = true, pos = Position.thread_data ()} lthy'
        (Frees.defined (Frees.build (Frees.add_frees lhs'))) [(x, T)]
  in lthy' end

fun mk_meta_eq (t, u) = \<^Const>\<open>Pure.eq \<open>fastype_of t\<close> for t u\<close>;

fun define_cond bind eq (ctxt:local_theory) =
       let
           val args = (SOME(bind,NONE,NoSyn), (Binding.empty_atts,eq),[],[])
       in def_cmd args ctxt end

fun define_inv (bind, inv) thy = 
    let val ctxt = Proof_Context.init_global thy
        val inv_parsed_term = Syntax.parse_term ctxt inv |> DOF_core.elaborate_term' ctxt
        val abs_term = Term.lambda (Free (instance_placeholderN, dummyT)) inv_parsed_term
        val eq = Logic.mk_equals (Free(Binding.name_of bind, dummyT), abs_term)
                 |> Syntax.check_term (Proof_Context.init_global thy)
    in  thy |> Named_Target.theory_map (define_cond bind eq) end

fun define_monitor_const doc_class_name bind thy = 
  let val bname = Long_Name.base_name doc_class_name
      val rex = DOF_core.rex_of doc_class_name thy
      val monitor_binding = bind |> (Binding.qualify false bname
                                     #> Binding.suffix_name monitor_suffixN)
  in
    if can hd rex
    then
      let val eq = Logic.mk_equals (Free(Binding.name_of monitor_binding, Trace_Attribute.doc_class_rexp_T), hd rex) 
      in thy |> Named_Target.theory_map (define_cond monitor_binding eq) end
    else thy
  end

fun add_doc_class_cmd overloaded (raw_params, binding)
                      raw_parent raw_fieldsNdefaults reject_Atoms regexps invariants thy =
    let
      val bind_pos = Binding.pos_of binding
      val name =
        let val name = Binding.name_of binding
        in case name |> Option.filter (not o equal DOF_core.default_cid) of
                NONE => bind_pos |> ISA_core.err (name
                                                  ^ ": This name is reserved by the implementation")
             | SOME name => name
       end
      val ctxt = Proof_Context.init_global thy;
      val params = map (apsnd (Typedecl.read_constraint ctxt)) raw_params;
      val ctxt1 = fold (Variable.declare_typ o TFree) params ctxt;
      fun markup2string s = String.concat (List.filter (fn c => c <> Symbol.DEL) 
                                            (Symbol.explode (Protocol_Message.clean_output s)))
      val name' =
        case raw_parent of
            NONE => DOF_core.default_cid
          | SOME s => markup2string s |> (fn s => DOF_core.get_onto_class_name_global' s thy)
      fun cid thy = DOF_core.get_onto_class_name_global name thy
      val (parent, ctxt2) = read_parent raw_parent ctxt1;
      val parent' = case parent of
                        NONE => NONE
                      | SOME (Ts, _) => SOME (Ts, name')
      val raw_fieldsNdefaults' = filter (fn((bi,_,_),_) => Binding.name_of bi <> traceN) 
                                        raw_fieldsNdefaults
      val _ = if length raw_fieldsNdefaults' <> length raw_fieldsNdefaults 
              then warning("re-declaration of trace attribute in monitor --- ignored")
              else ()
      val raw_fieldsNdefaults'' = if  null regexps  
                                  then raw_fieldsNdefaults' 
                                  else Trace_Attribute.trace_attr_ts::raw_fieldsNdefaults'
      val (fields, parsed_terms, ctxt3) = read_fields raw_fieldsNdefaults'' ctxt2;
      val fieldsNterms = (map (fn (a,b,_) => (a,b)) fields) ~~ parsed_terms
      val fieldsNterms' = map (fn ((x,y),z) => (x,y,z)) fieldsNterms
      val params' = map (Proof_Context.check_tfree ctxt3) params;
      fun check_n_filter thy (bind,ty,mf) = 
        case DOF_core.get_attribute_info name' (Binding.name_of bind) thy of
            NONE => SOME(bind,ty,mf)
          | SOME{def_occurrence,long_name,typ,...} =>
              if ty = typ 
              then (warning("overriding attribute:"
                            ^ long_name
                            ^ " in doc class:"
                            ^ def_occurrence); NONE)
              else error("no overloading allowed.")
      val record_fields = map_filter (check_n_filter thy) fields
      fun mk_eq_pair name = (Free (name, Trace_Attribute.doc_class_rexp_T), Trace_Attribute.doc_class_rexp_t name)
                            |> mk_meta_eq
      val args = (SOME(binding,NONE,NoSyn)
                  , (Binding.empty_atts, Binding.name_of binding |> mk_eq_pair), [], [])
      fun add record_fields invariants virtual =
        Record.add_record overloaded (params', binding) parent' record_fields
        #> (Local_Theory.notation true Syntax.mode_default RegExpInterface_Notations.notations
            |> Named_Target.theory_map)
        #> DOF_core.define_doc_class_global (params', binding) parent fieldsNterms' regexps 
                                            reject_Atoms invariants virtual
        #> (Local_Theory.notation false Syntax.mode_default RegExpInterface_Notations.notations
            |> Named_Target.theory_map)
       val invariants' = invariants |> map (apfst (Binding.qualify false name
                                                   #> Binding.suffix_name invariant_suffixN))
    in thy    (* adding const symbol representing doc-class for Monitor-RegExps.*)
           |> Named_Target.theory_map (def_cmd args)
           |> (case parent' of
                   NONE => add (DOF_core.tag_attr::record_fields) invariants' {virtual=false}
                 | SOME _  => if (not o null) record_fields
                                then add record_fields invariants' {virtual=false}
                                else add [DOF_core.tag_attr] invariants' {virtual=true})
              (* defines the ontology-checked text antiquotation to this document class *)
           |> (fn thy => OntoLinkParser.docitem_antiquotation binding (cid thy) thy)
           |> (fn thy => fold define_inv (invariants') thy)
           |> (fn thy => define_monitor_const (cid thy) binding thy)
           (* The function declare_ISA_class_accessor_and_check_instance uses a prefix
              because the class name is already bound to "doc_class Regular_Exp.rexp" constant
              by add_doc_class_cmd function *)
           |> (fn thy => ISA_core.declare_ISA_class_accessor_and_check_instance (params', cid thy, bind_pos) thy)
    end;
           

(* repackaging argument list *)
fun add_doc_class_cmd' (((overloaded, hdr), (parent, attrs)),((rejects,accept_rex),invars)) =
    (add_doc_class_cmd {overloaded = overloaded} hdr parent attrs rejects accept_rex invars)

val parse_invariants = Parse.and_list (Parse.binding --| Parse.$$$ "::" -- Parse.term)

val parse_doc_class = (Parse_Spec.overloaded 
      -- (Parse.type_args_constrained  -- Parse.binding) 
      -- (\<^keyword>\<open>=\<close>  
         |-- Scan.option (Parse.typ --| \<^keyword>\<open>+\<close>) 
          -- Scan.repeat1 (Parse.const_binding -- Scan.option (\<^keyword>\<open><=\<close> |-- Parse.term))
          )
      -- (   Scan.optional (\<^keyword>\<open>rejects\<close>    |-- Parse.enum1 "," Parse.term) []
          -- Scan.repeats   (\<^keyword>\<open>accepts\<close>    |-- (Parse.and_list Parse.term))
          -- Scan.repeats ((\<^keyword>\<open>invariant\<close>) |-- parse_invariants))
     )


val _ =
  Outer_Syntax.command \<^command_keyword>\<open>doc_class\<close> 
                       "define document class"
                        (parse_doc_class >> (Toplevel.theory o add_doc_class_cmd'));


(*just an alternative syntax*)
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>onto_class\<close> 
                       "define ontological class"
                        (parse_doc_class >> (Toplevel.theory o add_doc_class_cmd'));



val clean_mixfix_sub = translate_string
  (fn "\<^sub>_" => "_"
    | "\<^sub>'" => "'"
    | c =>  c);

val prefix_sub = prefix "\<^sub>"

val convertN = "convert"

fun add_onto_morphism classes_mappings eqs thy =
  if (length classes_mappings = length eqs) then
    let
      val specs = map (fn x => (Binding.empty_atts, x)) eqs
      val converts =
        map (fn (oclasses, dclass) =>
               let
                 val oclasses_string = map Protocol_Message.clean_output oclasses
                 val dclass_string = Protocol_Message.clean_output dclass
                 val const_sub_name = dclass_string
                                      |> (oclasses_string |> fold_rev (fn x => fn y => x ^ "_" ^ y))
                                      |> String.explode |> map (fn x => "\<^sub>" ^ (String.str x)) |> String.concat
                 val convert_typ = oclasses_string |> rev |> hd
                                   |> (oclasses_string |> rev |> tl |> fold (fn x => fn y => x ^ " \<times> " ^ y))
                 val convert_typ' = convert_typ ^ " \<Rightarrow> " ^ dclass_string
                 val oclasses_sub_string = oclasses_string
                                           |> map (clean_mixfix_sub
                                                   #> String.explode
                                                   #> map (prefix_sub o String.str)
                                                   #> String.concat)
                 val mixfix = oclasses_sub_string |> rev |> hd
                              |> (oclasses_sub_string |> rev |> tl |> fold (fn x => fn y => x ^ "\<^sub>\<times>" ^ y))
                              |> ISA_core.clean_mixfix
                 val mixfix' = convertN ^ mixfix ^ "\<^sub>\<Rightarrow>"
                                ^ (dclass_string |> clean_mixfix_sub |> String.explode
                                   |> map (prefix_sub o String.str) |> String.concat)
               in SOME (Binding.name (convertN ^ const_sub_name), SOME convert_typ', Mixfix.mixfix mixfix') end)
            classes_mappings
      val args = map (fn (x, y) => (x, y, [], [])) (converts ~~ specs)
      val lthy = Named_Target.theory_init thy
      val updated_lthy = fold (fn (decl, spec, prems, params) => fn lthy => 
                        let
                          val (_, lthy') = Specification.definition_cmd {verbose = false} decl params prems spec lthy
                        in lthy' end) args lthy
    in Local_Theory.exit_global updated_lthy end
    (* alternative way to update the theory using the Theory.join_theory function *)
      (*val lthys = map (fn (decl, spec, prems, params) => 
                        let
                          val (_, lthy') = Specification.definition_cmd decl params prems spec true lthy
                        in lthy' end) args
      val thys = map (Local_Theory.exit_global) lthys

    in Theory.join_theory thys end*)
  else error("The number of morphisms declarations does not match the number of definitions")

fun add_onto_morphism' (classes_mappings, eqs) = add_onto_morphism classes_mappings eqs

val parse_onto_morphism = Parse.and_list
                            ((Parse.$$$ "(" |-- Parse.enum1 "," Parse.typ --| Parse.$$$ ")" --| \<^keyword>\<open>to\<close>)
                              -- Parse.typ)
                          --  (\<^keyword>\<open>where\<close> |-- Parse.and_list Parse.prop)

(* The name of the definitions must follow this rule:
   for the declaration "onto_morphism (AA, BB) to CC",
   the name of the constant must be "convert\<^sub>A\<^sub>A\<^sub>\<times>\<^sub>B\<^sub>B\<^sub>\<Rightarrow>\<^sub>C\<^sub>C". *)
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>onto_morphism\<close> "define ontology morpism"
                       (parse_onto_morphism >> (Toplevel.theory o add_onto_morphism'));



end (* struct *)
\<close>

end
