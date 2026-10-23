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

chapter \<open>The Document Ontology Framework: Annotated Text Commands\<close>

text\<open> The commands that create and update instances, monitors, and annotated text elements, and the theorem and definition commands with meta-arguments. \<close>

theory Isa_DOF_Anno_Text_Cmds   (* Annotated text commands *)
  imports Isa_DOF_Instances
  keywords "open_monitor*"      "close_monitor*" 
           "declare_reference*" "update_instance*"        :: thy_decl
  and      "ML*"                                           :: thy_decl
  and      "definition*"                                   :: thy_defn
  and      "theorem*" "lemma*" "corollary*" "proposition*" :: thy_goal_stmt
  and      "schematic_goal*" :: thy_goal_stmt
  and      "text*"              "text-macro*"              :: document_body
  and      "print_doc_classes"        "print_doc_items" 
           "print_doc_class_template" "check_doc_global"   :: diag
begin

ML\<open>
structure Monitor_Command_Parser = 
struct

fun update_instance_command  ((binding, cid_pos),
                              doc_attrs: (((string*Position.T)*string)*string)list) thy
            : theory = 
  let val oid = Binding.name_of binding
      val cid = let val DOF_core.Instance {cid,...} =
                                      DOF_core.get_instance_global oid thy
                    val ctxt =  Proof_Context.init_global thy
                    val instances = DOF_core.get_instances ctxt
                    val markups = DOF_core.get_instance_name_global oid thy
                                 |> Name_Space.markups (Name_Space.space_of_table instances)
                    val _ = Context_Position.reports ctxt (map (pair (Binding.pos_of binding)) markups);
                in  cid end
      val default_cid = cid = DOF_core.default_cid
      val (((name, cid'), typ), pos') = DOF_Value_Cmd.Instance_Terms.check_classref {is_monitor = false}
                                                                              cid_pos thy
      val cid_pos' = (name, pos')
      val cid_long = fst cid_pos'
      val _ = if cid' = DOF_core.default_cid  orelse cid = cid'
              then () 
              else error("incompatible classes:"^cid^":"^cid')
      fun conv_attrs (((lhs, pos), opn), rhs) = ((Protocol_Message.clean_output lhs),pos,opn, 
                                                  Syntax.parse_term (Proof_Context.init_global thy) rhs)
      val assns' = map conv_attrs doc_attrs
      val def_trans_value  =
        #1 o (DOF_Value_Cmd.Instance_Terms.calc_update_term {mk_elaboration=true}
                                                                      thy (name, typ) assns')
        #> DOF_Value_Cmd.value (Proof_Context.init_global thy)
  in     
      thy |> (if Config.get_global thy DOF_core.object_value_debug 
              then let val def_trans_input_term  =
                         #1 o (DOF_Value_Cmd.Instance_Terms.calc_update_term
                                   {mk_elaboration=false} thy (name, typ)  assns')
              in DOF_core.map_input_term_value oid
                         def_trans_input_term def_trans_value end
              else DOF_core.map_value oid def_trans_value)
          |> tap (DOF_core.check_ml_invs cid_long oid {is_monitor=false})
          (* Bypass checking of high-level invariants when the class default_cid = "text",
             the top (default) document class.
             We want the class default_cid to stay abstract
             and not have the capability to be defined with attribute, invariants, etc.
             Hence this bypass handles docitem without a class associated,
             for example when you just want a document element to be referentiable
             without using the burden of ontology classes.
             ex: text*[sdf]\<open> Lorem ipsum @{thm refl}\<close> *)
          |> (fn thy => if default_cid then thy
                        else if Config.get_global thy DOF_core.invariants_checking
                             then DOF_Value_Cmd.Invariants.check_invariants thy binding
                             else thy)
  end


(* General criticism : attributes like "level" were treated here in the kernel instead of dragging
   them out into the COL -- bu *)


fun open_monitor_command  (((binding, raw_parent_pos), doc_attrs) : ODL_Meta_Args_Parser.meta_args_t) thy =
    let fun o_m_c binding params_cid_pos doc_attrs thy =
          DOF_Value_Cmd.Docitem_Parser.create_and_check_docitem 
            {is_monitor=true}  (* this is a monitor *)
            {is_inline=false} (* monitors are always inline *)
            {define=true}
            binding params_cid_pos doc_attrs thy
        fun compute_enabled_set cid thy =
          let
            val DOF_core.Onto_Class X = DOF_core.get_onto_class_global' cid thy
            val ralph = RegExpInterface.alphabet (#rejectS X)
            val aalph = RegExpInterface.alphabet (#rex X)
          in  (aalph, ralph, map (RegExpInterface.rexp_term2da thy aalph)(#rex X)) end 
        fun create_monitor_entry thy =  
          let val cid = case raw_parent_pos of
                            NONE => ISA_core.err ("You must specified a monitor class.") (Binding.pos_of binding)
                          | SOME (raw_parent, _) =>
                              DOF_core.markup2string raw_parent 
                              |> DOF_core.get_onto_class_cid thy |> (fst o fst)
              val (accS, rejectS, aS) = compute_enabled_set cid thy
          in DOF_core.add_monitor_info binding
                                       (DOF_core.make_monitor_info (accS, rejectS, aS)) thy
          end
    in
      thy
      |> o_m_c binding raw_parent_pos doc_attrs
      |> create_monitor_entry
    end;


fun close_monitor_command (args as ((binding, _ (* cid_pos *)),
                                    _: (((string*Position.T)*string)*string)list)) thy = 
    let val oid = Binding.name_of binding
        val pos = Binding.pos_of binding
        fun check_if_final aS = let val i = (find_index (not o RegExpInterface.final) aS) + 1
                                in  if i >= 1 
                                    then
                                      DOF_Value_Cmd.Monitor_Registration.msg thy
                                                    ("accepts clause " ^ Int.toString i 
                                                     ^ " of monitor " ^ oid
                                                     ^ " not in final state.") pos
                                    else ()
                                end
        val _ = let val DOF_core.Monitor_Info {automatas,...} =
                                                  DOF_core.get_monitor_info_global oid thy
                in check_if_final automatas end
        val oid' = DOF_core.get_monitor_info_name_global oid thy
        val delete_monitor_entry = DOF_core.Monitor_Info.map (Name_Space.del_table oid')
        val DOF_core.Instance {cid=cid_long,...} = DOF_core.get_instance_global oid thy
        val ctxt = Proof_Context.init_global thy
        val instances = DOF_core.get_instances ctxt
        val markups = DOF_core.get_instance_name_global oid thy
                      |> Name_Space.markups (Name_Space.space_of_table instances)
        val _ = Context_Position.reports ctxt (map (pair pos) markups);
    in  thy |> tap (DOF_core.check_closing_ml_invs cid_long oid {is_monitor=true})
            |> update_instance_command args
            |> tap (DOF_core.check_ml_invs cid_long oid {is_monitor=true})
            |> (fn thy => if Config.get_global thy DOF_core.invariants_checking
                          then DOF_Value_Cmd.Invariants.check_invariants thy binding
                          else thy)
            |> delete_monitor_entry
    end

(* Core Command Definitions *)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>open_monitor*\<close>
                       "open a document reference monitor"
                       (ODL_Meta_Args_Parser.attributes
                        >> (Toplevel.theory o open_monitor_command));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>close_monitor*\<close>
                       "close a document reference monitor"
                       (ODL_Meta_Args_Parser.attributes_upd
                        >> (Toplevel.theory o close_monitor_command)); 

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>update_instance*\<close>
                       "update meta-attributes of an instance of a document class"
                        (ODL_Meta_Args_Parser.attributes_upd
                         >> (Toplevel.theory o update_instance_command));

end (* structure Monitor_Command_Parser *)
\<close>

ML\<open>
(* The commands that create instances with a document output: text*, text-macro*, declare_reference*. *)
structure Document_Output_Commands = 
struct

fun meta_args_2_latex thy sem_attrs transform_attr
      (((binding, cid_opt), attr_list) : ODL_Meta_Args_Parser.meta_args_t) =
    (* for the moment naive, i.e. without textual normalization of 
       attribute names and adapted term printing *)
    let val lab = Binding.name_of binding
        val l   = DOF_core.get_instance_name_global lab thy |> DOF_core.output_name
                                                            |> enclose "{" "}"
                                                            |> prefix "label = "
        val ((cid_long, _), _) = case cid_opt of
                               NONE => let val DOF_core.Instance cid =
                                             DOF_core.get_instance_global lab thy
                                        in pair (cid |> #cid) (cid |> #cid)
                                           |> rpair DOF_core.default_cid_typ end
                                  
                              | SOME(cid,_) => DOF_core.get_onto_class_cid thy cid        

        val cid_txt  = cid_long |> DOF_core.output_name
                                |> enclose "{" "}"
                                |> prefix "type = "
        fun ltx_of_term _ _ (c as \<^Const_>\<open>Cons \<^Type>\<open>char\<close> for _ _\<close>) = HOLogic.dest_string c
          | ltx_of_term _ _ \<^Const_>\<open>Nil _\<close> = ""
          | ltx_of_term _ _ \<^Const_>\<open>numeral _ for t\<close> = Int.toString(HOLogic.dest_numeral t)
          | ltx_of_term ctx encl \<^Const_>\<open>Cons _ for t1 t2\<close> =
              let val inner = (case t2 of 
                                 \<^Const_>\<open>Nil _\<close> => ltx_of_term ctx true t1
                              | _ => ((ltx_of_term ctx false t1)^", " ^(ltx_of_term ctx false t2)))
              in if encl then enclose "{" "}" inner else inner end
          | ltx_of_term _ _ \<^Const_>\<open>None _\<close> = ""
          | ltx_of_term ctxt _ \<^Const_>\<open>Some _ for t\<close> = ltx_of_term ctxt true t
          | ltx_of_term ctxt _ t = ""^(Sledgehammer_Util.hackish_string_of_term ctxt t)


        fun markup2string s = String.concat (List.filter (fn c => c <> Symbol.DEL) 
                                            (Symbol.explode (Protocol_Message.clean_output s)))
        fun ltx_of_markup ctxt s = let
                                val term = (Syntax.check_term ctxt o Syntax.parse_term ctxt) s
                                val str_of_term = ltx_of_term  ctxt true term 
                                  (*  handle _ => "Exception in ltx_of_term" *)
                              in
                                str_of_term
                              end 
        fun toLong n = #long_name(the(DOF_core.get_attribute_info cid_long (markup2string n) thy))
        val ctxt = Proof_Context.init_global thy
        val actual_args =  map (fn ((lhs,_),rhs) => (toLong lhs, ltx_of_markup ctxt rhs))
                               attr_list
        val default_args =
          (DOF_core.get_attribute_defaults cid_long thy)
          |> map (fn (b,_, parsed_term) =>
                    (toLong (Long_Name.base_name ( Sign.full_name thy b))
                    , ltx_of_term ctxt true (Syntax.check_term ctxt parsed_term)))
              
        val default_args_filtered = filter (fn (a,_) => not (exists (fn b => b = a) 
                                    (map (fn (c,_) => c) actual_args))) default_args
        val transformed_args = (actual_args@default_args_filtered)
                               |> transform_attr
        fun update_sem_std_attrs [] attrs = attrs
          | update_sem_std_attrs (attr::attrs) attrs' =
              let val attrs'' = attrs' |> map (fn (name, value) =>
                                let val value' = value |> Long_Name.base_name
                                in 
                                  if name = attr
                                  then if value' |>  Symbol.is_ascii_identifier
                                        then (name, DOF_core.output_name value')
                                        else ISA_core.err ("Bad name of semantic attribute"
                                                           ^ name ^ ": " ^ value
                                                           ^ ". Name must be ASCII") (Binding.pos_of binding)
                                else (name, value') end)
              in update_sem_std_attrs attrs attrs'' end
        val updated_sem_std_attrs = update_sem_std_attrs sem_attrs transformed_args
        val updated_sem_std_attrs' = updated_sem_std_attrs |> map (apfst DOF_core.output_name)
        val str_args = updated_sem_std_attrs'
                       |> map (fn (lhs,rhs) => lhs^" = "^(enclose "{" "}" rhs)) 
                      
        val label_and_type = String.concat [ l, ",", cid_txt]
        val str_args = label_and_type::str_args
    in
      Latex.string (enclose "[" "]" (String.concat [ label_and_type, ", args={", (commas str_args), "}"]))
    end


(* level-attribute information management *)
fun gen_enriched_document_cmd {inline} cid_transform attr_transform
    (((binding,cid_pos), doc_attrs) : ODL_Meta_Args_Parser.meta_args_t) : theory -> theory =
  DOF_Value_Cmd.Docitem_Parser.create_and_check_docitem {is_monitor = false} {is_inline = inline}
   {define = true} binding (cid_transform cid_pos) (attr_transform doc_attrs);

fun gen_enriched_document_cmd' {inline} cid_transform attr_transform
    (((binding,cid_pos), doc_attrs) : ODL_Meta_Args_Parser.meta_args_t) : theory -> theory =
  DOF_Value_Cmd.Docitem_Parser.create_and_check_docitem {is_monitor = false} {is_inline = inline}
   {define = false} binding (cid_transform cid_pos) (attr_transform doc_attrs);


(* markup reports and document output *)

(* {markdown = true} sets the parsing process such that in the text-core
   markdown elements are accepted. *)

fun document_output {markdown: bool, markup: Latex.text -> Latex.text} sem_attrs transform_attr meta_args text ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val _ = Context_Position.reports ctxt (Document_Output.document_reports text);
    val output_meta = meta_args_2_latex thy sem_attrs transform_attr meta_args;
    val output_text = Document_Output.output_document ctxt {markdown = markdown} text;
  in markup (output_meta @ output_text) end;

fun document_output_reports name {markdown, body} sem_attrs transform_attr meta_args text ctxt =
  let
    fun markup xml =
      let val m = if body then Markup.latex_body else Markup.latex_heading
      in [XML.Elem (m (Latex.output_name name), xml)] end;
    val config = {markdown = markdown, markup = markup}
  in document_output config sem_attrs transform_attr meta_args text ctxt 
  end;


(* document output commands *)

(* The transition of an annotated document command, cf. Document_Output.document_output.
   The meta-arguments are executed by cmd on the theory before the command, synchronously; their
   effects are visible after the command. The text is checked and presented by present, which
   Toplevel forks like the presentation of text (Toplevel.present_state). With a target (in X),
   the text is checked and presented in the context of X, as for text (in X), while the instance
   stays global (Local_Theory.background_theory). Local_Theory.background_theory runs cmd with
   the naming of the target (the mandatory path "X" of a locale), which would define the instance
   as "X.oid", unreachable as "oid"; so cmd runs with the naming of the global theory. *)
fun global_background_theory cmd lthy =
  let val naming = Sign.naming_of (Proof_Context.theory_of lthy)
  in Local_Theory.background_theory (Sign.map_naming (K naming) #> cmd) lthy end;

fun annotated_transition NONE cmd present = Toplevel.theory_presentation cmd present
  | annotated_transition target cmd present =
      Toplevel.local_theory_presentation NONE target (global_background_theory cmd) present;

fun document_command (name, pos) descr mark cmd sem_attrs transform_attr =
  Outer_Syntax.command (name, pos) descr
  (Parse.opt_target -- ODL_Meta_Args_Parser.attributes -- Parse.document_source
    >> (fn ((target, meta_args), text) =>
      annotated_transition target (cmd meta_args)
          (Toplevel.presentation_context 
           #> document_output_reports name mark sem_attrs transform_attr meta_args text))); 

fun onto_macro_cmd_output_reports output_cmd (meta_args, text) ctxt =
 let
   val _ = Context_Position.reports ctxt (Document_Output.document_reports text);
 in output_cmd (meta_args, text) ctxt end

fun onto_macro_cmd_command (name, pos) descr cmd output_cmd = 
  Outer_Syntax.command (name, pos) descr 
  (Parse.opt_target -- ODL_Meta_Args_Parser.attributes -- Parse.document_source >>  
     (fn ((target, meta_args), text) =>
          annotated_transition target (cmd meta_args)
             (Toplevel.presentation_context
              #> onto_macro_cmd_output_reports output_cmd  (meta_args, text)
              )))

(* Core Command Definitions *)

val _ =
  document_command \<^command_keyword>\<open>text*\<close> "formal comment (primary style)"
    {markdown = true, body = true} (gen_enriched_document_cmd {inline=true} I I) [] I;
                                                 

(* This is just a stub at present *)
val _ =
  document_command \<^command_keyword>\<open>text-macro*\<close> "formal comment macro"
    {markdown = true, body = true}
    (gen_enriched_document_cmd {inline=false} (* declare as macro *) I I) [] I;

 
val (declare_reference_default_class, declare_reference_default_class_setup) 
     = Attrib.config_string \<^binding>\<open>declare_reference_default_class\<close> (K "");

val _ = Theory.setup declare_reference_default_class_setup

val _ = 
  let fun default_cid meta_args thy =
        let
          fun default_cid' _ NONE cid_pos = cid_pos
            | default_cid' thy (SOME ncid) NONE =
                let val name = DOF_core.get_onto_class_name_global' ncid thy
                    val ns = DOF_core.get_onto_classes (Proof_Context.init_global thy)
                             |> Name_Space.space_of_table
                    val pos = Name_Space.the_entry_pos ns name
                in SOME (name,pos) end
            | default_cid' _ (SOME _) cid_pos = cid_pos
          val ncid =  Config.get_global thy declare_reference_default_class
          val ncid' = if ncid = ""
                      then NONE
                      else SOME ncid
        in gen_enriched_document_cmd' {inline=true} (default_cid' thy ncid') I meta_args thy
        end
  in  Outer_Syntax.command \<^command_keyword>\<open>declare_reference*\<close>
                       "declare document reference"
                       (ODL_Meta_Args_Parser.attributes 
                        >> (Toplevel.theory o default_cid))
  end;

end (* structure Document_Output_Commands *)
\<close>



ML\<open>
structure Inspection_Commands =
struct

fun print_doc_classes _ ctxt = 
    let val classes = Name_Space.dest_table (DOF_core.get_onto_classes ctxt)
        val _ = writeln "=====================================";    
        fun print_attr (n, _, NONE) = (Binding.print n)
          | print_attr (n, _, SOME t)= (Binding.print n^"("^Syntax.string_of_term ctxt t^")")
        fun print_inv (bind,trm) = ((Binding.name_of bind |> unsuffix invariant_suffixN)
                                     ^"::"^Syntax.string_of_term ctxt trm)
        fun print_virtual {virtual} = Bool.toString virtual
        fun print_class (n, DOF_core.Onto_Class {attribute_decl, name, inherits_from, virtual
                                                 , invs, ...}) =
           (case inherits_from of 
               NONE => writeln ("docclass: "^n)
             | SOME(_,nn) => writeln ("docclass: "^n^" = "^nn^" + ");
            writeln ("    name:       "^(Binding.print name));
            writeln ("    virtual:    "^(print_virtual virtual));
            writeln ("    attrs:      "^commas (map print_attr attribute_decl));
            writeln ("    invs:       "^commas (map print_inv invs))
           );
    in  map print_class classes; 
        writeln "=====================================\n\n\n" 
    end;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_doc_classes\<close> "print document classes"
    (Parse.opt_bang >> (fn b => Toplevel.keep (print_doc_classes b o Toplevel.context_of)));

fun print_docclass_template cid ctxt = 
    let (* takes class synonyms into account *)
        val cid_long = DOF_core.get_onto_class_name_global' cid (Proof_Context.theory_of ctxt)
        val brute_hierarchy = (DOF_core.get_attributes_local cid_long ctxt)
        val flatten_hrchy = flat o (map(fn(lname, attrS) => 
                                           map (fn (s,_,_)=>(lname,(Binding.name_of s))) attrS))
        fun filter_overrides [] = []
           |filter_overrides ((ln,s)::S) = (ln,s):: filter_overrides(filter(fn(_,s')=> s<>s')S) 
        val hierarchy = map (fn(ln,s)=>ln^"."^s)(filter_overrides(flatten_hrchy brute_hierarchy)) 
        val args = String.concatWith "=%\n , " ("  label=,type":: hierarchy);
        val template = "\\newisadof{"^cid_long^"}%\n["^args^"=%\n][1]\n{%\n#1%\n}\n\n";
    in writeln template end;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_doc_class_template\<close> 
                       "print document class latex template"
    (Parse.string >> (fn b => Toplevel.keep (print_docclass_template b o Toplevel.context_of)));

fun print_doc_items _ ctxt =
    let val x = DOF_core.get_instances ctxt
        val _ = writeln "=====================================";  
        fun dfg true = "true" 
           |dfg false= "false"   
        fun print_item (n, DOF_core.Instance {defined,cid,vcid, inline, termNvalue}) =
                 let val (input_term, value) = Future.join termNvalue
                 in ((if defined then 
                  writeln ("docitem:             "^n)
                  else
                  writeln ("forward reference for docitem: "^n));
                  writeln ("    defined:         "^dfg defined);
                  writeln ("    type:            "^cid);
                  case vcid of NONE => () | SOME (s) => 
                  writeln ("    virtual type:    "^ s);
                  writeln ("    inline:          "^dfg inline);
                  (if Config.get ctxt DOF_core.object_value_debug
                   then  writeln ("    input_term:      "^ (Syntax.string_of_term ctxt input_term))
                   else ());
                  writeln ("    value:           "^ (Syntax.string_of_term ctxt value))
                 ) end
    in  map print_item (Name_Space.dest_table x); 
        writeln "=====================================\n\n\n" end;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_doc_items\<close>  "print document items"
    (Parse.opt_bang >> (fn b => Toplevel.keep (print_doc_items b o Toplevel.context_of)));

fun check_doc_global (_ (* strict_checking *) : bool) ctxt = 
  let val S = ctxt |> DOF_core.get_instances |> Name_Space.dest_table
              |> filter (fn (_, DOF_core.Instance {defined,...}) => (not defined))
              |> map #1
      val T = map fst (Name_Space.dest_table (DOF_core.get_monitor_infos ctxt))
  in if null S 
     then if null T then ()
          else error("Global consistency error - there are open monitors:  "
                ^ String.concatWith "," T) 
     else error("Global consistency error - Unresolved forward references: "
                ^ String.concatWith "," S)   
  end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>check_doc_global\<close> "check global document consistency"
    (Parse.opt_bang >> (fn b => Toplevel.keep (check_doc_global b o Toplevel.context_of)));

end (* structure Inspection_Commands *)
\<close>

\<comment> \<open>c.f. \<^file>\<open>~~/src/Pure/Isar/outer_syntax.ML\<close>\<close>
(*
  The ML* generates an "ontology-aware" version of the SML code-execution command.
*)
ML\<open>
structure ML_star_Command =
struct

fun meta_args_exec (meta_args as ((binding,cid_pos), doc_attrs) : ODL_Meta_Args_Parser.meta_args_t) ctxt = 
         ctxt |> (if meta_args = ODL_Meta_Args_Parser.empty_meta_args
                 then (K ctxt)                               
                 else Context.map_theory (DOF_Value_Cmd.Docitem_Parser.create_and_check_docitem 
                                    {is_monitor = false} {is_inline = true} 
                                    {define = true} binding (I cid_pos) (I doc_attrs)))

val attributes_opt = Scan.option ODL_Meta_Args_Parser.attributes

val _ =
  Outer_Syntax.command ("ML*", \<^here>) "ODL annotated ML text within theory or local theory"
    ((ODL_Meta_Args_Parser.attributes -- Parse.ML_source) 
     >> (fn (meta_args_opt, source) =>
            Toplevel.generic_theory
              ((meta_args_exec meta_args_opt)
               #> (ML_Context.exec (fn () =>  
                     (ML_Context.eval_source (ML_Compiler.verbose true ML_Compiler.flags) source)) 
               #> Local_Theory.propagate_ml_env))));

end
\<close>

\<comment> \<open>c.f. \<^file>\<open>~~/src/Pure/Isar/specification.ML\<close> and \<^file>\<open>~~/src/Pure/Pure.thy\<close>\<close>
ML\<open>
structure Definition_Star_Command =
struct

fun get_positions ctxt x =
  let
    fun get Cs (Const ("_type_constraint_", C) $ t) = get (C :: Cs) t
      | get Cs (Free (y, T)) =
          if x = y then
            maps Term_Position.decode_positionT
              (T :: map (Type.constraint_type ctxt) Cs)
          else []
      | get _ (t $ u) = get [] t @ get [] u
      | get _ (Abs (_, _, t)) = get [] t
      | get _ _ = [];
  in map #pos o get [] end;

fun dummy_frees ctxt xs tss =
  let
    val names =
      Variable.names_of ((fold o fold) Variable.declare_term tss ctxt)
      |> fold Name.declare xs;
    val (tss', _) = (fold_map o fold_map) Term.free_dummy_patterns tss names;
  in tss' end;

fun prep_spec_open prep_var parse_prop raw_vars raw_params raw_prems raw_concl ctxt =
  let
    val ((vars, xs), vars_ctxt) = DOF_core.prep_decls prep_var raw_vars ctxt;
    val (ys, params_ctxt) = vars_ctxt |> fold_map prep_var raw_params |-> Proof_Context.add_fixes;
    val props =  map (parse_prop params_ctxt) (raw_concl :: raw_prems)
                 |> singleton (dummy_frees params_ctxt (xs @ ys));
    val props' = props |> map (DOF_core.elaborate_term' ctxt)
    val concl :: prems = Syntax.check_props params_ctxt props';
    val spec = Logic.list_implies (prems, concl);
    val spec_ctxt = Variable.declare_term spec params_ctxt;

    fun get_pos x = maps (get_positions spec_ctxt x) props;
    in ((vars, xs, get_pos, spec), spec_ctxt) end;

val read_spec_open = prep_spec_open Proof_Context.read_var Syntax.parse_prop;

(* definition *)

fun gen_def prep_spec prep_att raw_var raw_params raw_prems ((a, raw_atts), raw_spec) lthy =
  let
    val atts = map (prep_att lthy) raw_atts;

    val ((vars, xs, get_pos, spec), _) = lthy
        |> prep_spec (the_list raw_var) raw_params raw_prems raw_spec;
    val (((x, T), rhs), prove) = Local_Defs.derived_def lthy get_pos {conditional = true} spec;
    val _ = Name.reject_internal (x, []);
    val (b, mx) =
      (case (vars, xs) of
        ([], []) => (Binding.make (x, (case get_pos x of [] => Position.none | p :: _ => p)), NoSyn)
      | ([(b, _, mx)], [y]) =>
          if x = y then (b, mx)
          else
            error ("Head of definition " ^ quote x ^ " differs from declaration " ^ quote y ^
              Position.here (Binding.pos_of b))
      | _ => error "internal naming error: gen_def");

    val name = Thm.def_binding_optional b a;
    val ((lhs, (_, raw_th)), lthy2) = lthy
      |> Local_Theory.define_internal ((b, mx), ((Binding.suffix_name "_raw" name, []), rhs));

    val th = prove lthy2 raw_th;
    val lthy3 = lthy2 |> Spec_Rules.add name Spec_Rules.equational [lhs] [th];

    val ([(def_name, [th'])], lthy4) = lthy3
      |> Local_Theory.notes [((name, Code.singleton_default_equation_attrib :: atts), [([th], [])])];

    val lhs' = Morphism.term (Local_Theory.target_morphism lthy) lhs;

    val _ = Proof_Display.print_consts {verbose = true, pos = Position.thread_data ()} lthy4
              (Frees.defined (Frees.build (Frees.add_frees lhs'))) [(x, T)];
  in ((lhs, (def_name, th')), lthy4) end;

val definition_cmd = gen_def read_spec_open Attrib.check_src;

fun definition_cmd' meta_args_opt decl params prems spec ctxt =
  Local_Theory.background_theory (DOF_Value_Cmd.meta_args_exec meta_args_opt) ctxt
  |> definition_cmd decl params prems spec

val _ =
  Outer_Syntax.local_theory \<^command_keyword>\<open>definition*\<close> "constant definition"
    (ODL_Meta_Args_Parser.opt_attributes --
      (Scan.option Parse_Spec.constdecl -- (Parse_Spec.opt_thm_name ":" -- Parse.prop) --
        Parse_Spec.if_assumes -- Parse.for_fixes)
     >> (fn (meta_args_opt, (((decl, spec), prems), params)) => 
                                    #2 o definition_cmd' meta_args_opt decl params prems spec));
end
\<close>

\<comment> \<open>c.f. \<^file>\<open>~~/src/Pure/Isar/specification.ML\<close> and \<^file>\<open>~~/src/Pure/Pure.thy\<close>\<close>
ML\<open>
structure Theorem_Star_Command =
struct
(* theorem*, lemma*, etc. commands *)

local

fun elaborate stmt ctxt = stmt |> map (apsnd (map (apfst (DOF_core.elaborate_term ctxt)
                                              #> apsnd (map (DOF_core.elaborate_term ctxt)))))

fun prep_statement prep_att prep_stmt raw_elems raw_stmt ctxt =
  let
    val (stmt, elems_ctxt) = prep_stmt raw_elems raw_stmt ctxt;
    val prems = Assumption.local_prems_of elems_ctxt ctxt;
    val stmt_ctxt = fold (fold (Proof_Context.augment o fst) o snd) stmt elems_ctxt;
  in
    (case raw_stmt of
      Element.Shows _ =>
        let val stmt' = Attrib.map_specs (map prep_att) stmt
            val stmt'' = elaborate stmt' ctxt
        in (([], prems, stmt'', NONE), stmt_ctxt) end
    | Element.Obtains raw_obtains =>
        let
          val asms_ctxt = stmt_ctxt
            |> fold (fn ((name, _), asm) =>
                snd o Proof_Context.add_assms Assumption.assume_export
                  [((name, [Context_Rules.intro_query NONE]), asm)]) stmt;
          val that = Assumption.local_prems_of asms_ctxt stmt_ctxt;
          val ([(_, that')], that_ctxt) = asms_ctxt
                        |> Proof_Context.set_stmt true
                        |> Proof_Context.note_thmss "" [((Binding.name Auto_Bind.thatN, []), 
                                                        [(that, [])])]
                        ||> Proof_Context.restore_stmt asms_ctxt;

          val stmt' = [(Binding.empty_atts, [(#2 (#1 (Obtain.obtain_thesis ctxt)), [])])];
          val stmt'' = elaborate stmt' ctxt
        in ((Obtain.obtains_attribs raw_obtains, prems, stmt'', SOME that'), that_ctxt) end)
  end;

fun gen_theorem schematic bundle_includes prep_att prep_stmt
    long kind before_qed after_qed (name, raw_atts) raw_includes raw_elems raw_concl lthy =
  let
    val _ = Local_Theory.assert lthy;

    val elems = raw_elems |> map (Element.map_ctxt_attrib (prep_att lthy));
    val ((more_atts, prems, stmt, facts), goal_ctxt) = lthy
      |> bundle_includes raw_includes
      |> prep_statement (prep_att lthy) prep_stmt elems raw_concl;
    val atts = more_atts @ map (prep_att lthy) raw_atts;

    val print_results =
      Proof_Display.print_results {verbose = true, pos = Position.thread_data ()};

    fun after_qed' results goal_ctxt' =
      let
        val results' =
          burrow (map (Goal.norm_result lthy) o Proof_Context.export goal_ctxt' lthy) results;
        val (res, lthy') =
          if forall (Binding.is_empty_atts o fst) stmt then (map (pair "") results', lthy)
          else
            Local_Theory.notes_kind kind
              (map2 (fn (b, _) => fn ths => (b, [(ths, [])])) stmt results') lthy;
        val lthy'' =
          if Binding.is_empty_atts (name, atts)
          then (print_results lthy' ((kind, ""), res); lthy')
          else
            let
              val ([(res_name, _)], lthy'') =
                 Local_Theory.notes_kind kind [((name, atts), [(maps #2 res, [])])] lthy';
              val _ = print_results lthy' ((kind, res_name), res);
            in lthy'' end;
      in after_qed results' lthy'' end;

    val prems_name = if long then Auto_Bind.assmsN else Auto_Bind.thatN;
  in
    goal_ctxt
    |> not (null prems) ?
      (Proof_Context.note_thmss "" [((Binding.name prems_name, []), [(prems, [])])] #> snd)
    |> Proof.theorem before_qed after_qed' (map snd stmt)
    |> (case facts of NONE => I | SOME ths => Proof.refine_insert ths)
    |> tap (fn state => not schematic andalso Proof.schematic_goal state andalso
        error "Illegal schematic goal statement")
  end;

in

val theorem_cmd =
  gen_theorem false Bundle.includes_cmd Attrib.check_src Expression.read_statement;

fun theorem_cmd' meta_args_opt long kind before_qed after_qed (name, raw_atts) raw_includes raw_elems raw_concl lthy =
  Local_Theory.background_theory (DOF_Value_Cmd.meta_args_exec meta_args_opt) lthy
  |> theorem_cmd long kind before_qed after_qed (name, raw_atts) raw_includes raw_elems raw_concl;

val schematic_theorem_cmd =
  gen_theorem true Bundle.includes_cmd Attrib.check_src Expression.read_statement;

fun schematic_theorem_cmd' meta_args_opt long kind before_qed after_qed (name, raw_atts) raw_includes raw_elems raw_concl lthy =
  Local_Theory.background_theory (DOF_Value_Cmd.meta_args_exec meta_args_opt) lthy
  |> schematic_theorem_cmd long kind before_qed after_qed (name, raw_atts) raw_includes raw_elems raw_concl;

end;

local
val long_keyword =
  Parse_Spec.includes >> K "" ||
  Parse_Spec.long_statement_keyword;

val long_statement =
  ODL_Meta_Args_Parser.opt_attributes --
  Scan.optional (Parse_Spec.opt_thm_name ":" --| Scan.ahead long_keyword) Binding.empty_atts --
  Scan.optional Parse_Spec.includes [] -- Parse_Spec.long_statement
    >> (fn (((meta_args_opt, binding), includes), (elems, concl)) => (meta_args_opt, true, binding, includes, elems, concl));

val short_statement =
  ODL_Meta_Args_Parser.opt_attributes --
  Parse_Spec.statement -- Parse_Spec.if_statement -- Parse.for_fixes
    >> (fn (((meta_args_opt, shows), assumes), fixes) =>
      (meta_args_opt, false, Binding.empty_atts, [], [Element.Fixes fixes, Element.Assumes assumes],
        Element.Shows shows));

fun theorem spec schematic descr =
  Outer_Syntax.local_theory_to_proof spec ("state " ^ descr)
    ((long_statement || short_statement) >> (fn (meta_args_opt, long, binding, includes, elems, concl) =>
      ((if schematic then schematic_theorem_cmd' else theorem_cmd')
        meta_args_opt long Thm.theoremK NONE (K I) binding includes elems concl)));

val _ = theorem \<^command_keyword>\<open>theorem*\<close> false "theorem";
val _ = theorem \<^command_keyword>\<open>lemma*\<close> false "lemma";
val _ = theorem \<^command_keyword>\<open>corollary*\<close> false "corollary";
val _ = theorem \<^command_keyword>\<open>proposition*\<close> false "proposition";
val _ = theorem \<^command_keyword>\<open>schematic_goal*\<close> true "schematic goal";
in end

end (* structure Theorem_Star_Command *)
\<close>

end
