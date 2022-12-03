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

chapter \<open>The Document Ontology Framework for Isabelle\<close>

text\<open> Offering 
\<^item> text-elements that can be annotated with meta-information
\<^item> typed links to text-elements via specifically generated anti-quotations
\<^item> typed structure of this meta-information specifiable in an Ontology-Language ODL
  providing syntax and PIDE support of document classes 
\<^item> inner-syntax-antiquotations (ISA's) allowing to reference Isabelle-entities such as 
  types, terms, theorems inside the meta-information
\<^item> monitors allowing to enforce a specific textual structure of an Isabelle Document
\<^item> a basic infrastructure to define class invariants
  (for continuous checking of meta-information side-conditions of text-elements 
\<^item> LaTeX support. \<close> 
  
text\<open> In this section, we develop on the basis of a management of references Isar-markups
that provide direct support in the PIDE framework. \<close> 
  
theory Isa_DOF                (* Isabelle Document Ontology Framework *)
  imports  Main  
           RegExpInterface    (* Interface to functional regular automata for monitoring *)
           
  keywords "+=" ":=" "accepts"  "rejects" "invariant"
           
  and      "open_monitor*"      "close_monitor*" 
           "declare_reference*" "update_instance*"
           "doc_class"          "onto_class" (* a syntactic alternative *)   
           "ML*"
           "define_shortcut*"   "define_macro*"          :: thy_decl

  and      "text*"              "text-macro*"            :: document_body
  and      "term*"   "value*"   "assert*"                :: document_body

  and      "use_template" "use_ontology"                 :: thy_decl
  and      "define_template" "define_ontology"           :: thy_load
  and      "print_doc_classes"        "print_doc_items" 
           "print_doc_class_template" "check_doc_global" :: diag

      

           
  
begin

text\<open> @{footnote \<open>sdf\<close>}, @{file "$ISABELLE_HOME/src/Pure/ROOT.ML"}\<close> 

section\<open>Primitive Markup Generators\<close>
ML\<open>

val docrefN   = "docref";    
val docclassN = "doc_class";

(** name components **)

val defN = "def"
val def_suffixN = "_" ^ defN
val defsN = defN ^ "s"
val instances_of_suffixN = "_instances"
val invariant_suffixN = "_inv"
val invariantN = "\<sigma>"
val makeN = "make"
val schemeN = "_scheme"

(* derived from: theory_markup *) 
fun docref_markup_gen refN def name id pos =
  if id = 0 then Markup.empty
  else Position.make_entity_markup {def = def} id refN (name, pos);   (* or better store the thy-name as property ? ? ? *)

val docref_markup = docref_markup_gen docrefN

val docclass_markup = docref_markup_gen docclassN

\<close>

section\<open> Utilities\<close>

ML\<open>
fun spy x y = (writeln (x ^ y); y)

fun markup2string x = XML.content_of (YXML.parse_body x)

(* a hacky, but save encoding of unicode comming from the interface to the string format
   that can be parsed by the inner-syntax string parser ''dfdf''. *)
fun bstring_to_holstring ctxt x (* (x:bstring) *) : string =
    let val term = Syntax.parse_term ctxt (markup2string x)
        fun hpp x = if x = #"\\" then "@" else 
                    if x = #"@"  then "@@" else String.implode [x] 
    in  term |>  Sledgehammer_Util.hackish_string_of_term ctxt
             |>  map hpp o String.explode |> String.concat
    end;


fun chopper p (x:string) = 
    let fun hss buff [] = rev buff
           |hss buff (S as a::R) = if p a then let val (front,rest) = chop_prefix p S
                                               in hss (String.implode front :: buff) rest end
                                   else        let val (front,rest) = chop_prefix (not o p) S
                                               in hss (String.implode front ::buff) rest end
    in hss [] (String.explode x) end;


fun holstring_to_bstring ctxt (x:string) : bstring  =
    let fun collapse "" = ""
           |collapse S = if String.sub(S,0) = #"@" 
                         then let val n = String.size S
                                  val front = replicate (n div 2) #"@" 
                                  val back  = if (n mod 2)=1 then [#"\\"] else []
                              in String.implode (front @ back) end 
                         else S;
        val t = String.concat (map collapse (chopper (fn x => x = #"@") x));
    in  t |>  Syntax.string_of_term ctxt o Syntax.parse_term ctxt end;

fun map_option _ NONE = NONE 
   |map_option f (SOME x) = SOME (f x);

fun map_optional _ s NONE = s 
   |map_optional f _ (SOME x) = f x;

fun map_fst f (x,y) = (f x,y)
fun map_snd f (x,y) = (x,f y)

fun map_eq_fst_triple f (x,_,_) (y,_,_) = equal (f x) (f y)

\<close>

section\<open> A HomeGrown Document Type Management (the ''Model'') \<close>


ML\<open> 
structure DOF_core = 
 
struct
   type virtual = {virtual : bool}
   type docclass_struct = {params         : (string * sort) list,          (*currently not used *)
                           name           : binding,
                           virtual        : virtual, 
                           thy_name       : string, id : serial,           (* for pide *)
                           inherits_from  : (typ list * string) option,    (* imports *)
                           attribute_decl : (binding*typ*term option)list, (* class local *)
                           rejectS        : term list,
                           rex            : term list,
                           invs           : ((string * Position.T) * term) list  } (* monitoring regexps --- product semantics*)


   type docclass_tab = docclass_struct Symtab.table

   val  initial_docclass_tab = Symtab.empty:docclass_tab 

   fun  merge_docclass_tab (otab,otab') = Symtab.merge (op =) (otab,otab') 

   val tag_attr = (\<^binding>\<open>tag_attribute\<close>, \<^Type>\<open>int\<close>, Mixfix.NoSyn)
        (* Attribute hidden to the user and used internally by isabelle_DOF.
           For example, this allows to add a specific id to a class
           to be able to reference the class internally.
        *)

   val  default_cid = "text"    (* the top (default) document class: everything is a text.*)

   fun  is_subclass0 (tab:docclass_tab) s t =
        let val _ = case Symtab.lookup tab t of 
                          NONE => if t <> default_cid 
                                  then error ("document superclass not defined: "^t) 
                                  else default_cid
                       |  SOME _ => ""
            fun father_is_sub s = case Symtab.lookup tab s of 
                          NONE => error ("document subclass not defined: "^s)
                       |  SOME ({inherits_from=NONE, ...}) => s = t
                       |  SOME ({inherits_from=SOME (_,s'), ...}) => 
                                  s' = t orelse father_is_sub s' 
        in s = t orelse 
           (t = default_cid  andalso Symtab.defined tab s ) orelse
           (s <> default_cid andalso father_is_sub s)
        end

   type docobj =    {pos      : Position.T, 
                     thy_name : string,
                     input_term : term,
                     value    : term,
                     inline   : bool, 
                     id       : serial, 
                     cid      : string,
                     vcid     : string option}

   type docobj_tab ={tab      : (docobj option) Symtab.table,
                     maxano   : int
                    }
   
   val  initial_docobj_tab:docobj_tab = {tab = Symtab.empty, maxano = 0} 

   fun  merge_docobj_tab ({tab=otab,maxano=m}, {tab=otab',maxano=m'}) = 
                    (let fun X(NONE,NONE)       = false
                            |X(SOME _, NONE)    = false
                            |X(NONE, SOME _)    = false
                            |X(SOME b, SOME b') =  true (* b = b' *) 
                    in {tab=Symtab.merge X (otab,otab'),maxano=Int.max(m,m')}
                    end) 
   type ISA_transformers = {check     :
                              (theory -> term * typ * Position.T -> string -> term option),
                            elaborate : (theory -> string -> typ -> term option -> Position.T -> term)
                           }

   type ISA_transformer_tab = ISA_transformers Symtab.table
   val  initial_ISA_tab:ISA_transformer_tab = Symtab.empty

   type docclass_inv_tab = (string -> {is_monitor:bool} -> Context.generic -> bool) Symtab.table
   val  initial_docclass_inv_tab : docclass_inv_tab = Symtab.empty

  type docclass_eager_inv_tab =
                              (string -> {is_monitor:bool} -> Context.generic -> bool) Symtab.table
  val  initial_docclass_eager_inv_tab : docclass_eager_inv_tab = Symtab.empty

  type docclass_lazy_inv_tab =
                              (string -> {is_monitor:bool} -> Context.generic -> bool) Symtab.table
  val  initial_docclass_lazy_inv_tab : docclass_lazy_inv_tab = Symtab.empty

   type open_monitor_info = {accepted_cids : string list,
                             rejected_cids : string list,
                             automatas     : RegExpInterface.automaton list
   }

   type monitor_tab = open_monitor_info Symtab.table
   val  initial_monitor_tab:monitor_tab = Symtab.empty

   fun override(t1,t2) = fold(Symtab.update)(Symtab.dest t2)(t1)

(* registrating data of the Isa_DOF component *)
structure Data = Generic_Data
(
  type T =     {docobj_tab          : docobj_tab,
                docclass_tab        : docclass_tab,
                ISA_transformer_tab : ISA_transformer_tab,
                monitor_tab         : monitor_tab,
                docclass_inv_tab    : docclass_inv_tab,
                docclass_eager_inv_tab : docclass_eager_inv_tab,
                docclass_lazy_inv_tab : docclass_lazy_inv_tab}
  val empty  = {docobj_tab          = initial_docobj_tab,
                docclass_tab        = initial_docclass_tab,
                ISA_transformer_tab = initial_ISA_tab,
                monitor_tab         = initial_monitor_tab,
                docclass_inv_tab    = initial_docclass_inv_tab,
                docclass_eager_inv_tab = initial_docclass_eager_inv_tab,
                docclass_lazy_inv_tab = initial_docclass_lazy_inv_tab
               } 
  fun merge(   {docobj_tab=d1,docclass_tab = c1,
                 ISA_transformer_tab = e1, monitor_tab=m1,
                 docclass_inv_tab = n1,
                 docclass_eager_inv_tab = en1, docclass_lazy_inv_tab = ln1},
               {docobj_tab=d2,docclass_tab = c2,
                 ISA_transformer_tab = e2, monitor_tab=m2,
                 docclass_inv_tab = n2,
                 docclass_eager_inv_tab = en2, docclass_lazy_inv_tab = ln2})  = 
               {docobj_tab=merge_docobj_tab   (d1,d2), 
                docclass_tab = merge_docclass_tab (c1,c2),
                (*
                  The following merge is ultra-critical: the transformer tabs were
                  just extended by letting *the first* entry with the same long-name win.
                  Since the range is a (call-back) function, a comparison on its content
                  is impossible and some choice has to be made... Alternative: Symtab.join ?
                *)
                ISA_transformer_tab = Symtab.merge (fn (_ , _) => true)(e1,e2),
                monitor_tab =  override(m1,m2), 
                     (* PROVISORY  ... ITS A REAL QUESTION HOW TO DO THIS!*)
                docclass_inv_tab = override(n1,n2),
                     (* PROVISORY  ... ITS A REAL QUESTION HOW TO DO THIS!*)
                docclass_eager_inv_tab = override(en1,en2),
                     (* PROVISORY  ... ITS A REAL QUESTION HOW TO DO THIS!*)
                docclass_lazy_inv_tab = override(ln1,ln2)
                     (* PROVISORY  ... ITS A REAL QUESTION HOW TO DO THIS!*)
               }
);


val get_data = Data.get o Context.Proof;
val map_data = Data.map;
val get_data_global = Data.get o Context.Theory;
val map_data_global = Context.theory_map o map_data;


fun upd_docobj_tab f {docobj_tab,docclass_tab,ISA_transformer_tab,
                      monitor_tab,docclass_inv_tab,
                      docclass_eager_inv_tab, docclass_lazy_inv_tab} = 
            {docobj_tab = f docobj_tab, docclass_tab=docclass_tab, 
             ISA_transformer_tab=ISA_transformer_tab, monitor_tab=monitor_tab,
             docclass_inv_tab=docclass_inv_tab,
             docclass_eager_inv_tab=docclass_eager_inv_tab,
             docclass_lazy_inv_tab=docclass_lazy_inv_tab};
fun upd_docclass_tab f {docobj_tab=x,docclass_tab = y,ISA_transformer_tab = z,
                        monitor_tab,  docclass_inv_tab,
                        docclass_eager_inv_tab, docclass_lazy_inv_tab} = 
            {docobj_tab=x,docclass_tab = f y,ISA_transformer_tab = z, monitor_tab=monitor_tab,
             docclass_inv_tab=docclass_inv_tab,
             docclass_eager_inv_tab=docclass_eager_inv_tab,
             docclass_lazy_inv_tab=docclass_lazy_inv_tab};
fun upd_ISA_transformers f {docobj_tab=x,docclass_tab = y,ISA_transformer_tab = z,
                            monitor_tab, docclass_inv_tab,
                            docclass_eager_inv_tab, docclass_lazy_inv_tab} = 
            {docobj_tab=x,docclass_tab = y,ISA_transformer_tab = f z, monitor_tab=monitor_tab, 
             docclass_inv_tab=docclass_inv_tab,
             docclass_eager_inv_tab=docclass_eager_inv_tab,
             docclass_lazy_inv_tab=docclass_lazy_inv_tab};
fun upd_monitor_tabs f {docobj_tab,docclass_tab,ISA_transformer_tab,
                        monitor_tab, docclass_inv_tab,
                        docclass_eager_inv_tab, docclass_lazy_inv_tab} =
            {docobj_tab = docobj_tab,docclass_tab = docclass_tab,
             ISA_transformer_tab = ISA_transformer_tab, monitor_tab = f monitor_tab, 
             docclass_inv_tab=docclass_inv_tab,
             docclass_eager_inv_tab=docclass_eager_inv_tab,
             docclass_lazy_inv_tab=docclass_lazy_inv_tab};             
fun upd_docclass_inv_tab f {docobj_tab,docclass_tab,ISA_transformer_tab,
                            monitor_tab, docclass_inv_tab,
                            docclass_eager_inv_tab, docclass_lazy_inv_tab} =
            {docobj_tab = docobj_tab,docclass_tab = docclass_tab,
             ISA_transformer_tab = ISA_transformer_tab, monitor_tab = monitor_tab, 
             docclass_inv_tab    = f docclass_inv_tab,
             docclass_eager_inv_tab=docclass_eager_inv_tab,
             docclass_lazy_inv_tab=docclass_lazy_inv_tab};

fun upd_docclass_eager_inv_tab f {docobj_tab,docclass_tab,ISA_transformer_tab,
                            monitor_tab, docclass_inv_tab,
                            docclass_eager_inv_tab, docclass_lazy_inv_tab} =
            {docobj_tab = docobj_tab,docclass_tab = docclass_tab,
             ISA_transformer_tab = ISA_transformer_tab, monitor_tab = monitor_tab, 
             docclass_inv_tab=docclass_inv_tab,
             docclass_eager_inv_tab=f docclass_eager_inv_tab,
             docclass_lazy_inv_tab=docclass_lazy_inv_tab};

fun upd_docclass_lazy_inv_tab f {docobj_tab,docclass_tab,ISA_transformer_tab,
                            monitor_tab, docclass_inv_tab,
                            docclass_eager_inv_tab, docclass_lazy_inv_tab} =
            {docobj_tab = docobj_tab,docclass_tab = docclass_tab,
             ISA_transformer_tab = ISA_transformer_tab, monitor_tab = monitor_tab, 
             docclass_inv_tab=docclass_inv_tab,
             docclass_eager_inv_tab=docclass_eager_inv_tab,
             docclass_lazy_inv_tab=f docclass_lazy_inv_tab};

fun get_accepted_cids  ({accepted_cids, ... } : open_monitor_info) = accepted_cids
fun get_automatas      ({automatas, ... }     : open_monitor_info) = automatas


(* doc-class-name management: We still use the record-package for internally 
   representing doc-classes. The main motivation is that "links" to entities are
   types over doc-classes, *types* in the Isabelle sense, enriched by additional data.
   This has the advantage that the type-inference can be abused to infer long-names
   for doc-class-names. Note, however, that doc-classes are currently implemented
   by non-polymorphic records only; this means that the extensible "_ext" versions
   of type names must be reduced to qualifier names only. The used Syntax.parse_typ 
   handling the identification does that already. 
   However, we use Syntax.read_typ in order to allow type-synonyms which requires
   an appropriate adaption in read_cid.*)
 
fun is_subclass (ctxt) s t = is_subclass0(#docclass_tab(get_data ctxt)) s t
fun is_subclass_global thy s t = is_subclass0(#docclass_tab(get_data_global thy)) s t


fun typ_to_cid (Type(s,[\<^Type>\<open>unit\<close>])) = Long_Name.qualifier s
   |typ_to_cid (Type(_,[T])) = typ_to_cid T
   |typ_to_cid _ = error("type is not an ontological type.")


fun parse_cid ctxt cid =
(* parses a type lexically/syntactically, checks absence of type vars *) 
         (case Syntax.parse_typ ctxt cid of
                 Type(tyname, [])  =>  tyname
                | _ => error "illegal type-format for doc-class-name.")
         handle ERROR _ => "" (* ignore error *)


fun read_cid ctxt "text" = default_cid (* text = default_cid *)
  | read_cid ctxt cid =
(* parses a type syntactically, type-identification, checking as class id *)
         (case Syntax.read_typ ctxt cid of
                 ty as Type(tyname, _)  => let val res = typ_to_cid ty
                                               val t = #docclass_tab(get_data ctxt)
                                           in  if Symtab.defined t res 
                                               then res
                                               else error("type identifier not a class id:"^res) 
                                           end
                | _ => error "illegal type-format for doc-class-name.")
         handle ERROR _ =>  error("type identifier not a class id:"^cid) 

fun parse_cid_global thy cid = parse_cid (Proof_Context.init_global thy) cid
fun read_cid_global thy cid  = read_cid (Proof_Context.init_global thy) cid
        

fun is_defined_cid_global cid thy = 
(* works with short and long names *)
                                    let val t = #docclass_tab(get_data_global thy)
                                    in  cid=default_cid orelse 
                                        Symtab.defined t (parse_cid_global thy cid) 
                                    end

fun is_defined_cid_global' cid_long thy = 
(* works with long names only *)
                                    let val t = #docclass_tab(get_data_global thy)
                                    in  cid_long=default_cid orelse  Symtab.defined t cid_long end


fun is_defined_cid_local cid ctxt  = 
(* works with short and long names *)
                                     let val t = #docclass_tab(get_data ctxt)
                                     in  cid=default_cid orelse 
                                         Symtab.defined t (parse_cid ctxt cid) 
                                     end

fun is_defined_cid_local' cid_long ctxt  = 
(* works with long names only *)
                                     let val t = #docclass_tab(get_data ctxt)
                                     in  cid_long=default_cid orelse Symtab.defined t cid_long  end


fun is_declared_oid_global oid thy = let val {tab,...} = #docobj_tab(get_data_global thy)
                                     in  Symtab.defined tab oid end

fun is_declared_oid_local oid thy  = let val {tab,...} = #docobj_tab(get_data thy)
                                     in  Symtab.defined tab oid end

fun is_defined_oid_global oid thy  = let val {tab,...} = #docobj_tab(get_data_global thy)
                                     in  case Symtab.lookup tab oid of 
                                           NONE => false
                                          |SOME(NONE) => false
                                          |SOME _ => true
                                     end

fun is_defined_oid_local oid thy   = let val {tab,...} = #docobj_tab(get_data thy)
                                     in  case Symtab.lookup tab oid of 
                                           NONE => false
                                          |SOME(NONE) => false
                                          |SOME _ => true
                                     end

fun is_virtual cid thy = let val tab = (#docclass_tab(get_data_global thy))
                             (* takes class synonyms into account *)
                             val long_name = read_cid_global thy cid
                         in case Symtab.lookup tab long_name of
                                NONE =>  error("Undefined class id: " ^ cid)
                              | SOME ({virtual=virtual, ...}) => #virtual virtual
                         end

fun declare_object_global oid thy  =  
    let fun decl {tab=t,maxano=x} = {tab=Symtab.update_new(oid,NONE)t, maxano=x}
    in (map_data_global (upd_docobj_tab(decl)) (thy)
       handle Symtab.DUP _ => error("multiple declaration of document reference"))
    end

fun declare_object_local oid ctxt  =
    let fun decl {tab,maxano} = {tab=Symtab.update_new(oid,NONE) tab, maxano=maxano}
    in  (map_data(upd_docobj_tab decl)(ctxt)
        handle Symtab.DUP _ => error("multiple declaration of document reference"))
    end


fun update_class_invariant cid_long f thy = 
    let val  _ = if is_defined_cid_global' cid_long thy then () 
                 else error("undefined class id : " ^cid_long)
    in  map_data_global (upd_docclass_inv_tab (Symtab.update (cid_long, 
                        (fn ctxt => ((writeln("Inv check of : " ^cid_long); f ctxt )))))) 
                        thy
    end

fun update_class_eager_invariant cid_long f thy = 
    let val  _ = if is_defined_cid_global' cid_long thy then () 
                 else error("undefined class id : " ^cid_long)
    in  map_data_global (upd_docclass_eager_inv_tab (Symtab.update (cid_long, 
                        (fn ctxt => ((writeln("Eager Invariant check of: " ^cid_long); f ctxt )))))) 
                        thy
    end

fun update_class_lazy_invariant cid_long f thy = 
    let val  _ = if is_defined_cid_global' cid_long thy then () 
                 else error("undefined class id : " ^cid_long)
    in  map_data_global (upd_docclass_lazy_inv_tab (Symtab.update (cid_long, 
                        (fn ctxt => ((writeln("Lazy Invariant check of: " ^cid_long); f ctxt )))))) 
                        thy
    end

fun get_class_invariant cid_long thy =
    let val  _ = if is_defined_cid_global' cid_long thy then () 
                 else error("undefined class id : " ^cid_long)
        val {docclass_inv_tab, ...} =  get_data_global thy
    in  case Symtab.lookup  docclass_inv_tab cid_long of 
            NONE   => K(K(K true))
          | SOME f => f
    end

fun get_class_eager_invariant cid_long thy =
    let val  _ = if is_defined_cid_global' cid_long thy then () 
                 else error("undefined class id : " ^cid_long)
        val {docclass_eager_inv_tab, ...} =  get_data_global thy
    in  case Symtab.lookup  docclass_eager_inv_tab cid_long of 
            NONE   => K(K(K true))
          | SOME f => f
    end

fun get_class_lazy_invariant cid_long thy =
    let val  _ = if is_defined_cid_global' cid_long thy then () 
                 else error("undefined class id : " ^cid_long)
        val {docclass_lazy_inv_tab, ...} =  get_data_global thy
    in  case Symtab.lookup  docclass_lazy_inv_tab cid_long of 
            NONE   => K(K(K true))
          | SOME f => f
    end

val SPY = Unsynchronized.ref(Bound 0)

fun check_regexps term = 
    let val _ = case fold_aterms  Term.add_free_names term [] of
                   n::_ => error("No free variables allowed in monitor regexp:" ^ n)
                 | _ => ()  
        val _ = case fold_aterms  Term.add_var_names term [] of
                   (n,_)::_ => error("No schematic variables allowed in monitor regexp:" ^ n)
                 | _ => ()
        (* Missing: Checks on constants such as undefined, ... *)
    in  term end

fun check_reject_atom cid_long term = 
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
    let val nn = Context.theory_name thy (* in case that we need the thy-name to identify
                                            the space where it is ... *)
        val cid = (Binding.name_of binding)
        val pos = (Binding.pos_of binding)
    
        val _   = if is_defined_cid_global cid thy
                  then error("redefinition of document class:"^cid )
                  else ()
        val parent' = map_option (map_snd (read_cid_global thy)) parent
        (* weird construction. Necessary since parse produces at rare cases 
           string representations that do no longer have the lexis of a type name. *)
        val cid_long  = parse_cid_global thy cid
        val cid_long' = parse_cid_global thy cid_long
        val _ = if cid_long' <> "" then ()
                else error("Could not construct type from doc_class (lexical problem?)")

        val id = serial ();
        val _ = Position.report pos (docclass_markup true cid id pos);
    
        val rejectS = map (Syntax.read_term_global thy) reject_Atoms;
        val _ = map (check_reject_atom cid_long)  rejectS; 
        val reg_exps = map (Syntax.read_term_global thy) rexp;
        val _ = map check_regexps reg_exps
        val _ = if not(null rejectS) andalso (null reg_exps) 
                then  error ("reject clause requires accept clause ! " ) else ();
        val _ = if has_duplicates (op =) (map (fst o fst) invs) 
                then error("invariant labels must be unique"^  Position.here (snd(fst(hd invs)))) 
                else ()
        val invs' = map (map_snd(Syntax.read_term_global thy)) invs 
        val info = {params=params', 
                    name = binding,
                    virtual = virtual,
                    thy_name = nn, 
                    id = id, (* for pide --- really fresh or better reconstruct 
                                from prior record definition ? For the moment: own
                                generation of serials ... *)
                    inherits_from = parent',
                    attribute_decl = fields , 
                    rejectS = rejectS,
                    rex = reg_exps, 
                    invs =  invs'}
    
    in   map_data_global(upd_docclass_tab(Symtab.update(cid_long,info)))(thy)
    end


fun define_object_global (oid, bbb) thy  = 
    let val nn = Context.theory_name thy (* in case that we need the thy-name to identify
                                            the space where it is ... *)
    in  if is_defined_oid_global oid thy 
        then error("multiple definition of document reference")
        else map_data_global  (upd_docobj_tab(fn {tab=t,maxano=x} =>            
                                        {tab=Symtab.update(oid,SOME bbb) t,
                                         maxano=x}))
                              (thy)
    end
            
fun define_object_local (oid, bbb) ctxt  = 
    map_data (upd_docobj_tab(fn{tab,maxano}=>{tab=Symtab.update(oid,SOME bbb)tab,maxano=maxano})) ctxt


(* declares an anonyme label of a given type and generates a unique reference ...  *)
fun declare_anoobject_global thy cid = 
    let fun declare {tab,maxano} = let val str = cid^":"^Int.toString(maxano+1)
                                       val _ = writeln("Anonymous reference declared: " ^ str)
                                   in  {tab=Symtab.update(str,NONE)tab,maxano= maxano+1} end
    in  map_data_global (upd_docobj_tab declare) (thy)
    end

fun declare_anoobject_local ctxt cid = 
    let fun declare {tab,maxano} = let val str = cid^":"^Int.toString(maxano+1)
                                           val _ = writeln("Anonymous reference declared: " ^str)
                                       in  {tab=Symtab.update(str,NONE)tab, maxano=maxano+1} end
    in map_data (upd_docobj_tab declare) (ctxt) 
    end


fun get_object_global_opt oid thy  = Symtab.lookup (#tab(#docobj_tab(get_data_global thy))) oid 

fun get_object_global oid thy  = case get_object_global_opt oid thy of 
                                       NONE => error("undefined reference: "^oid)
                                      |SOME(bbb) => bbb

fun get_object_local_opt oid ctxt  = Symtab.lookup (#tab(#docobj_tab(get_data ctxt))) oid

fun get_object_local oid ctxt  = case get_object_local_opt oid ctxt of 
                                       NONE => error("undefined reference: "^oid)
                                      |SOME(bbb) => bbb

fun get_doc_class_global cid thy = 
    if cid = default_cid then error("default class access") (* TODO *)
    else let val t = #docclass_tab(get_data_global thy)
         in  (Symtab.lookup t cid) end
    

fun get_doc_class_local cid ctxt = 
    if cid = default_cid then error("default class access") (* TODO *)
    else let val t = #docclass_tab(get_data ctxt)
         in  (Symtab.lookup t cid) end


fun is_defined_cid_local cid ctxt  = let val t = #docclass_tab(get_data ctxt)
                                     in  cid=default_cid orelse 
                                         Symtab.defined t (parse_cid ctxt cid) 
                                     end

fun get_attributes_local cid ctxt =
  if cid = default_cid then []
  else let val t = #docclass_tab(get_data ctxt)
           val cid_long = read_cid ctxt cid (* to assure that the given cid is really a long_cid *)
       in  case Symtab.lookup t cid_long of
             NONE => error("undefined class id for attributes: "^cid)
             | (SOME ({inherits_from=NONE,
                       attribute_decl = X, ...})) => [(cid_long,X)]
             | (SOME ({inherits_from=SOME(_,father),
                       attribute_decl = X, ...})) =>
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

fun get_value_global oid thy  = case get_object_global oid thy of
                                   SOME{value=term,...} => SOME term
                                 | NONE => NONE  

fun get_value_local oid ctxt  = case get_object_local oid ctxt of
                                   SOME{value=term,...} => SOME term
                                 | NONE => NONE  

(* missing : setting terms to ground (no type-schema vars, no schema vars. )*)
fun update_value_global oid upd_input_term upd_value thy  = 
          case get_object_global oid thy of
               SOME{pos,thy_name, input_term, value,inline,id,cid,vcid} => 
                   let val tab' = Symtab.update(oid,SOME{pos=pos,thy_name=thy_name,
                                                         input_term=upd_input_term input_term,
                                                         value=upd_value value,id=id, 
                                                         inline=inline,cid=cid, vcid=vcid})
                   in  map_data_global (upd_docobj_tab(fn{tab,maxano}=>{tab=tab' tab,maxano=maxano})) thy end
             | NONE => error("undefined doc object: "^oid)  


val ISA_prefix = "ISA_"  (* ISA's must be declared in Isa_DOF.thy  !!! *)

val doc_class_prefix = ISA_prefix ^ "doc_class_"

fun is_ISA s = String.isPrefix ISA_prefix (Long_Name.base_name s)

fun get_class_name_without_prefix s = String.extract (s, String.size(doc_class_prefix), NONE)

fun get_doc_class_name_without_ISA_prefix s = String.extract (s, String.size(ISA_prefix), NONE)

fun is_class_ISA thy s = let val bname = Long_Name.base_name s
                             val qual = Long_Name.qualifier s
                         in
                           if String.isPrefix doc_class_prefix bname then
                             let
                               val class_name =
                                        Long_Name.qualify qual (get_class_name_without_prefix bname)
                             in
                               is_defined_cid_global (class_name) thy end
                           else false end

fun get_isa_global isa thy  =  
            case Symtab.lookup (#ISA_transformer_tab(get_data_global thy)) (ISA_prefix^isa) of 
                 NONE      => error("undefined inner syntax antiquotation: "^isa)
               | SOME(bbb) => bbb
                               

fun get_isa_local isa ctxt  = case Symtab.lookup (#ISA_transformer_tab(get_data ctxt)) (ISA_prefix^isa) of 
                                       NONE => error("undefined inner syntax antiquotation: "^isa)
                                      |SOME(bbb) => bbb

fun update_isa map_data_fun (isa, trans) ctxt =
  let
    val bname = Long_Name.base_name isa;
    val qual = Long_Name.qualifier isa;
    val long_name = Long_Name.qualify qual (ISA_prefix ^ bname);
  in map_data_fun (upd_ISA_transformers(Symtab.update(long_name, trans))) ctxt end

 fun update_isa_local (isa, trans) ctxt  = update_isa  map_data (isa, trans) ctxt

fun update_isa_global (isa, trans) thy  = update_isa  map_data_global (isa, trans) thy

fun transduce_term_global {mk_elaboration=mk_elaboration} (term,pos) thy =
    (* pre: term should be fully typed in order to allow type-related term-transformations *)
    let val tab = #ISA_transformer_tab(get_data_global thy)
        fun T(Const(s,ty) $ t) = if is_ISA s
                                 then case Symtab.lookup tab s of
                                          NONE => error("undefined inner syntax antiquotation: "^s)
                                        | SOME({check=check, elaborate=elaborate}) =>
                                            case check thy (t,ty,pos) s of
                                               NONE => Const(s,ty) $ t
                                               (* checking isa, may raise error though. *)
                                             | SOME t => if mk_elaboration 
                                                         then elaborate thy s ty (SOME t) pos
                                                         else Const(s,ty) $ t
                                                         (* transforming isa *)
                                 else (Const(s,ty) $ (T t))
          |T(t1 $ t2) = T(t1) $ T(t2)
          |T(Const(s,ty)) = if is_ISA s
                            then case Symtab.lookup tab s of
                                     NONE => error("undefined inner syntax antiquotation: "^s)
                                   | SOME({elaborate=elaborate, ...}) =>
                                       if mk_elaboration 
                                       then elaborate thy s ty NONE pos
                                       else Const(s, ty)
                                       (* transforming isa *)
                            else Const(s, ty)
          |T(Abs(s,ty,t)) = Abs(s,ty,T t)
          |T t = t
    in T term end

fun writeln_classrefs ctxt = let  val tab = #docclass_tab(get_data ctxt)
                             in   writeln (String.concatWith "," (Symtab.keys tab)) end


fun writeln_docrefs ctxt = let  val {tab,...} = #docobj_tab(get_data ctxt)
                           in   writeln (String.concatWith "," (Symtab.keys tab)) end





fun print_doc_class_tree ctxt P T = 
    let val {docobj_tab={tab = x, ...},docclass_tab, ...} = get_data ctxt;
        val class_tab:(string * docclass_struct)list = (Symtab.dest docclass_tab)
        fun is_class_son X (n, dc:docclass_struct) = (X = #inherits_from dc)
        fun tree lev ([]:(string * docclass_struct)list) = ""
           |tree lev ((n,R)::S) = (if P(lev,n) 
                                  then "."^Int.toString lev^" "^(T n)^"{...}.\n"
                                       ^ (tree(lev + 1)(filter(is_class_son(SOME([],n)))class_tab))
                                  else "."^Int.toString lev^" ... \n") 
                                  ^ (tree lev S)
        val roots = filter(is_class_son NONE) class_tab
    in  ".0 .\n" ^ tree 1 roots end


val (strict_monitor_checking, strict_monitor_checking_setup)
     = Attrib.config_bool \<^binding>\<open>strict_monitor_checking\<close> (K false);

val (invariants_checking, invariants_checking_setup) 
     = Attrib.config_bool \<^binding>\<open>invariants_checking\<close> (K false);

val (invariants_checking_with_tactics, invariants_checking_with_tactics_setup) 
     = Attrib.config_bool \<^binding>\<open>invariants_checking_with_tactics\<close> (K false);


end (* struct *)

\<close>

setup\<open>DOF_core.strict_monitor_checking_setup
      #> DOF_core.invariants_checking_setup
      #> DOF_core.invariants_checking_with_tactics_setup\<close>

section\<open> Syntax for Term Annotation Antiquotations (TA)\<close>

text\<open>Isabelle/DOF allows for annotations at the term level, for which an
antiquotation syntax and semantics is defined at the inner syntax level.
(For this reasons, the mechanism has been called somewhat misleading
\<^emph>\<open>inner syntax antiquotations\<close> in earlier versions of Isabelle/DOF.)

For the moment, only a fixed number of builtin TA's is supported, future
versions might extend this feature substantially.\<close>

subsection\<open> Syntax \<close> 

datatype "doc_class" = mk string

\<comment> \<open>and others in the future : file, http, thy, ...\<close> 

datatype "typ" = ISA_typ string  ("@{typ _}")
datatype "term" = ISA_term string  ("@{term _}")
consts ISA_term_repr    :: "string \<Rightarrow> term"              ("@{termrepr _}")
datatype "thm" = ISA_thm string  ("@{thm _}")
datatype "file" = ISA_file string  ("@{file _}")
datatype "thy" = ISA_thy string  ("@{thy _}")
consts ISA_docitem      :: "string \<Rightarrow> 'a"                ("@{docitem _}")
datatype "docitem_attr" = ISA_docitem_attr string  string ("@{docitemattr (_) :: (_)}")
consts ISA_trace_attribute :: "string \<Rightarrow> (string * string) list" ("@{trace-attribute _}")

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
            (case Term_Position.decode_position p of
              SOME (pos, _) => c $ f (mk_string f_mk accu (content (s, pos))) $ p
            | NONE => err ())
        | _ => err ())
      end;
  end;
\<close>

syntax "_cartouche_string" :: "cartouche_position \<Rightarrow> _"  ("_")

ML\<open>
structure Cartouche_Grammar = struct
  fun list_comb_mk cst n c = list_comb (Syntax.const cst, String_Syntax.mk_bits_syntax n c)
  val nil1 = Syntax.const @{const_syntax String.empty_literal}
  fun cons1 c l = list_comb_mk @{const_syntax String.Literal} 7 c $ l

  val default =
    [ ( "char list"
      , ( Const (@{const_syntax Nil}, @{typ "char list"})
        , fn c => fn l => Syntax.const @{const_syntax Cons} $ list_comb_mk @{const_syntax Char} 8 c $ l
        , snd))
    , ( "String.literal", (nil1, cons1, snd))]
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
structure ISA_core = 
struct

fun err msg pos = error (msg ^ Position.here pos);

fun check_path check_file ctxt dir (name, pos) =
  let
    val _ = Context_Position.report ctxt pos (Markup.language_path true); (* TODO: pos should be 
                                                                                   "lifted" to 
                                                                                   type source *)

    val path = Path.append dir (Path.explode name) handle ERROR msg => err msg pos;
    val _ = Path.expand path handle ERROR msg => err msg pos;
    val _ = Context_Position.report ctxt pos (Markup.path (Path.implode_symbolic path));
    val _ =
      (case check_file of
        NONE => path
      | SOME check => (check path handle ERROR msg => err msg pos));
  in path end;


fun ML_isa_antiq check_file thy (name, _, pos) =
  let val path = check_path check_file (Proof_Context.init_global thy) Path.current (name, pos);
  in "Path.explode " ^ ML_Syntax.print_string (Path.implode path) end;


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
  (* this works for long-names only *)
  let fun check thy (name, _) = case Proof_Context.lookup_fact (Proof_Context.init_global thy) name of
                                  NONE => err ("No Theorem:" ^name) pos
                                | SOME X => X
  in   ML_isa_check_generic check thy (term, pos) end


fun ML_isa_check_file thy (term, _, pos) _ =
  let fun check thy (name, pos) = check_path (SOME File.check_file) 
                                             (Proof_Context.init_global thy) 
                                             (Path.current) 
                                             (name, pos);
  in  ML_isa_check_generic check thy (term, pos) end;

fun check_instance thy (term, _, pos) s =
  let
    val bname = Long_Name.base_name s;
    val qual = Long_Name.qualifier s;
    val class_name =
        Long_Name.qualify qual (String.extract(bname , String.size(DOF_core.doc_class_prefix), NONE));
    fun check thy (name, _)  =
      let
        val object_cid = case DOF_core.get_object_global name thy of
                          NONE =>  err ("No class instance: " ^ name) pos
                          | SOME(object) => #cid object
        fun check' (class_name, object_cid) =
          if class_name = object_cid then
            DOF_core.get_value_global name thy
          else err (name ^ " is not an instance of " ^ class_name) pos
      in check' (class_name, object_cid) end;
  in ML_isa_check_generic check thy (term, pos) end


fun ML_isa_id thy (term,pos) = SOME term


fun ML_isa_check_docitem thy (term, req_ty, pos) _ =
  let fun check thy (name, _) s =
           if DOF_core.is_declared_oid_global name thy 
           then case DOF_core.get_object_global name thy of
                    NONE => warning("oid declared, but not yet defined --- "^
                                    " type-check incomplete")
                 |  SOME {pos=pos_decl,cid,id,...} => 
                         let val ctxt = (Proof_Context.init_global thy)
                             val req_class = case req_ty of 
                                         \<^Type>\<open>fun _ T\<close> => DOF_core.typ_to_cid T
                                       | _ => error("can not infer type for: "^ name)
                         in if cid <> DOF_core.default_cid 
                               andalso not(DOF_core.is_subclass ctxt cid req_class)
                            then error("reference ontologically inconsistent: "
                                       ^cid^" vs. "^req_class^ Position.here pos_decl)
                            else ()
                         end
           else err ("faulty reference to docitem: "^name) pos
  in  ML_isa_check_generic check thy (term, pos) end

fun ML_isa_check_trace_attribute thy (term, _, pos) s =
  let
    fun check thy (name, _)  =
      case DOF_core.get_object_global name thy of
          NONE =>  err ("No class instance: " ^ name) pos
        | SOME(_) => ()
  in ML_isa_check_generic check thy (term, pos) end

fun ML_isa_elaborate_generic (_:theory) isa_name ty term_option _ =
  case term_option of
      NONE => error("Wrong term option. You must use a defined term")
    | SOME term => Const (isa_name, ty) $ term

fun elaborate_instance thy _ _ term_option pos =
  case term_option of
      NONE => error ("Malformed term annotation")
    | SOME term => let val instance_name = HOLogic.dest_string term
                   in case DOF_core.get_value_global instance_name thy of
                          NONE => error ("No class instance: " ^ instance_name)
                        | SOME(value) =>
                            DOF_core.transduce_term_global {mk_elaboration=true} (value, pos) thy
                   end

(*
  The function declare_ISA_class_accessor_and_check_instance uses a prefix
  because the class name is already bound to "doc_class Regular_Exp.rexp" constant
  by add_doc_class_cmd function
*)
fun declare_ISA_class_accessor_and_check_instance doc_class_name =
  let
    val bind = Binding.prefix_name DOF_core.doc_class_prefix doc_class_name
    val typestring = "string => " ^ (Binding.name_of doc_class_name)
    (* Unfortunately due to different lexical conventions for constant symbols and mixfix symbols
       we can not use "_" for classes names in term antiquotation.
       We chose to convert "_" to "-".*)
    val conv_class_name = String.translate (fn #"_" => "-"
                                            | x => String.implode [x] )
                                                (Binding.name_of doc_class_name)
    val mixfix_string = "@{" ^ conv_class_name ^ " _}"
  in
    Sign.add_consts_cmd [(bind, typestring, Mixfix.mixfix(mixfix_string))]
    #> (fn thy => let
                    val long_name = DOF_core.read_cid_global thy (Binding.name_of doc_class_name)
                    val qual = Long_Name.qualifier long_name
                    val class_name = Long_Name.qualify qual
                            (DOF_core.get_doc_class_name_without_ISA_prefix (Binding.name_of bind))
                  in
                    DOF_core.update_isa_global
                             (class_name, {check=check_instance, elaborate=elaborate_instance}) thy
                  end)
  end

fun elaborate_instances_list thy isa_name _ _ _ =
  let
    val base_name = Long_Name.base_name isa_name
    fun get_isa_name_without_intances_suffix s =
      String.extract (s, 0, SOME (String.size(s) - String.size(instances_of_suffixN)))
    val base_name_without_suffix = get_isa_name_without_intances_suffix base_name
    val base_name' = DOF_core.get_class_name_without_prefix (base_name_without_suffix)
    val class_typ = Proof_Context.read_typ (Proof_Context.init_global thy)
                                                (base_name')
    val tab = #tab(#docobj_tab(DOF_core.get_data_global thy))
    val table_list = Symtab.dest tab
    fun get_instances_name_list _ [] = []
      | get_instances_name_list class_name (x::xs) =
          let 
            val (_, docobj_option) = x
          in 
            case docobj_option of
                NONE => get_instances_name_list class_name xs
              | SOME {cid=cid, value=value, ...} =>
                  if cid = class_name
                  then value::get_instances_name_list class_name xs
                  else get_instances_name_list class_name xs
          end
    val long_class_name = DOF_core.read_cid_global thy base_name'
    val values_list = get_instances_name_list long_class_name table_list
  in HOLogic.mk_list class_typ values_list end

fun declare_class_instances_annotation thy doc_class_name =
  let
    val bind = Binding.prefix_name DOF_core.doc_class_prefix doc_class_name
    val bind' = Binding.suffix_name instances_of_suffixN bind
    val class_list_typ = Proof_Context.read_typ (Proof_Context.init_global thy)
                                                ((Binding.name_of doc_class_name) ^ " List.list")
    (* Unfortunately due to different lexical conventions for constant symbols and mixfix symbols
       we can not use "_" for classes names in term antiquotation.
       We chose to convert "_" to "-".*)
    val conv_class_name' = String.translate (fn #"_" => "-" | x=> String.implode [x])
                                        ((Binding.name_of doc_class_name) ^ instances_of_suffixN)
    val mixfix_string = "@{" ^ conv_class_name' ^ "}"
  in
    Sign.add_consts [(bind', class_list_typ, Mixfix.mixfix(mixfix_string))]
    #> (fn thy => let
                    val long_name = DOF_core.read_cid_global thy (Binding.name_of doc_class_name)
                    val qual = Long_Name.qualifier long_name
                    val transformer_name = Long_Name.qualify qual
                                (DOF_core.get_doc_class_name_without_ISA_prefix (Binding.name_of bind'))
                  in
                    DOF_core.update_isa_global (transformer_name,
                    {check=check_identity, elaborate= elaborate_instances_list}) thy end)
  end                            

fun symbex_attr_access0 ctxt proj_term term =
let
      val [subterm'] = Type_Infer_Context.infer_types ctxt [proj_term $ term]
in Value_Command.value ctxt (subterm') end

fun compute_attr_access ctxt attr oid pos_option pos' = (* template *)
    case DOF_core.get_value_global oid (Context.theory_of ctxt) of 
            SOME term => let val ctxt =  (Proof_Context.init_global (Context.theory_of ctxt))
                              val SOME{cid,pos=pos_decl,id,...} = DOF_core.get_object_local oid ctxt
                              val docitem_markup = docref_markup false oid id pos_decl; 
                              val _ = Context_Position.report ctxt pos' docitem_markup;
                              val (* (long_cid, attr_b,ty) = *)
                                  {long_name, typ=ty, def_pos, ...} = 
                                       case DOF_core.get_attribute_info_local cid attr ctxt of
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
                                              val SOME{id,...} = DOF_core.get_doc_class_local class_name ctxt
                                              val class_markup = docclass_markup false class_name id def_pos
                                            in Context_Position.report ctxt pos class_markup end
                          in  symbex_attr_access0 ctxt proj_term term end
                          (*in  Value_Command.value ctxt term end*)
           | NONE => error("identifier not a docitem reference" ^ Position.here pos')

fun ML_isa_elaborate_trace_attribute (thy:theory) _ _ term_option pos =
case term_option of
    NONE => err ("Malformed term annotation") pos
  | SOME term => 
      let
        val oid = HOLogic.dest_string term
        val traces = compute_attr_access (Context.Theory thy) "trace" oid NONE pos
        fun conv (\<^Const>\<open>Pair \<^typ>\<open>doc_class rexp\<close> \<^typ>\<open>string\<close>\<close>
                    $ (\<^Const>\<open>Atom \<^typ>\<open>doc_class\<close>\<close> $ (\<^Const>\<open>mk\<close> $ s)) $ S) =
          let val s' =  DOF_core.read_cid (Proof_Context.init_global thy) (HOLogic.dest_string s)
          in \<^Const>\<open>Pair \<^typ>\<open>string\<close> \<^typ>\<open>string\<close>\<close> $ HOLogic.mk_string s' $ S end
        val traces' = map conv (HOLogic.dest_list traces)
      in HOLogic.mk_list \<^Type>\<open>prod \<^typ>\<open>string\<close> \<^typ>\<open>string\<close>\<close> traces' end

(* utilities *)

fun property_list_dest ctxt X =
  map (fn \<^Const_>\<open>ISA_term for s\<close> => HOLogic.dest_string s
         |\<^Const_>\<open>ISA_term_repr for s\<close> => holstring_to_bstring ctxt (HOLogic.dest_string s))
    (HOLogic.dest_list X)

end; (* struct *)
                                                            
\<close>


subsection\<open> Isar - Setup\<close>

setup\<open>DOF_core.update_isa_global("Isa_DOF.typ.typ",
                  {check=ISA_core.ML_isa_check_typ, elaborate=ISA_core.ML_isa_elaborate_generic}) \<close>
setup\<open>DOF_core.update_isa_global("Isa_DOF.term.term",
                  {check=ISA_core.ML_isa_check_term, elaborate=ISA_core.ML_isa_elaborate_generic}) \<close>
setup\<open>DOF_core.update_isa_global("Isa_DOF.term_repr",
                    {check=ISA_core.check_identity, elaborate=ISA_core.ML_isa_elaborate_generic}) \<close>
setup\<open>DOF_core.update_isa_global("Isa_DOF.thm.thm",
                  {check=ISA_core.ML_isa_check_thm, elaborate=ISA_core.ML_isa_elaborate_generic}) \<close>
setup\<open>DOF_core.update_isa_global("Isa_DOF.file.file",
                  {check=ISA_core.ML_isa_check_file, elaborate=ISA_core.ML_isa_elaborate_generic}) \<close>
setup\<open>DOF_core.update_isa_global("Isa_DOF.docitem",
              {check=ISA_core.ML_isa_check_docitem, elaborate=ISA_core.ML_isa_elaborate_generic}) \<close>
setup\<open>DOF_core.update_isa_global("Isa_DOF.trace_attribute",
              {check=ISA_core.ML_isa_check_trace_attribute, elaborate=ISA_core.ML_isa_elaborate_trace_attribute}) \<close>
section\<open> Syntax for Annotated Documentation Commands (the '' View'' Part I) \<close>


(*
================== 2018 ====================================================== 
(* Exported from Pure_Syn *)

fun output_document state markdown txt =
  let
    val ctxt = Toplevel.presentation_context state;
    val _ =
      Context_Position.report ctxt
        (Input.pos_of txt) (Markup.language_document (Input.is_delimited txt));
  in Thy_Output.output_document ctxt markdown txt end;

fun document_command markdown (loc, txt) =
  Toplevel.keep (fn state =>
    (case loc of
      NONE => ignore (output_document state markdown txt)
    | SOME (_, pos) =>
        error ("Illegal target specification -- not a theory context" ^ Position.here pos))) o
  Toplevel.present_local_theory loc (fn state =>
    ignore (output_document state markdown txt));


====================== 2017 ===================================================

(* Exported from Thy_Output *)
fun document_command markdown (loc, txt) =
  Toplevel.keep (fn state =>
    (case loc of
      NONE => ignore (output_text state markdown txt)
    | SOME (_, pos) =>
        error ("Illegal target specification -- not a theory context" ^ Position.here pos))) o
  Toplevel.present_local_theory loc (fn state => ignore (output_text state markdown txt));


 *)


ML\<open>
structure ODL_Meta_Args_Parser = 
struct


type meta_args_t = (((string * Position.T) *
                     (string * Position.T) option)
                    * ((string * Position.T) * string) list)

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
    Parse.position Parse.name 
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


structure Value_Command (*: VALUE_COMMAND*) =
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

fun value ctxt term = value_select "" ctxt
                      (DOF_core.transduce_term_global {mk_elaboration=true} (term , \<^here>)
                                          (Proof_Context.theory_of ctxt))
val value_without_elaboration = value_select ""

structure Docitem_Parser = 
struct

fun cid_2_cidType cid_long thy =
    if cid_long = DOF_core.default_cid then \<^Type>\<open>unit\<close>
    else let val t = #docclass_tab(DOF_core.get_data_global thy)
             fun ty_name cid = cid^"."^  Long_Name.base_name cid ^ Record.extN
             fun fathers cid_long = case Symtab.lookup t cid_long of
                       NONE => let val ctxt = Proof_Context.init_global thy
                                   val tty = Syntax.parse_typ (Proof_Context.init_global thy) cid_long
                               in  error("undefined doc class id :"^cid_long)
                               end 
                     | SOME ({inherits_from=NONE, ...}) => [cid_long]
                     | SOME ({inherits_from=SOME(_,father), ...}) => 
                           cid_long :: (fathers father) 
         in fold (fn x => fn y => Type(ty_name x,[y])) (fathers cid_long) \<^Type>\<open>unit\<close>  
         end

fun create_default_object thy class_name = 
  let
    val purified_class_name = String.translate (fn #"." => "_" | x => String.implode [x]) class_name
    val make_const = Syntax.read_term_global thy (Long_Name.qualify class_name makeN);
    fun attr_to_free (binding, typ, _) = Free (purified_class_name ^ "_"
                                               ^ (Binding.name_of binding)
                                               ^ "_Attribute_Not_Initialized", typ)
    val class_list = DOF_core.get_attributes class_name thy
    fun attrs_filter [] = [] 
      | attrs_filter (x::xs) =
          let val (cid, ys) = x
              fun is_duplicated _ [] = false
                | is_duplicated y (x::xs) =
                    let val (_, ys) = x
                    in if exists (map_eq_fst_triple Binding.name_of y) ys
                       then true
                       else is_duplicated y xs end
          in (cid, filter_out (fn y => is_duplicated y xs) ys)::attrs_filter xs end
    val class_list' = rev (attrs_filter (rev class_list))
    val tag_attr = HOLogic.mk_number \<^Type>\<open>int\<close>
    fun add_tag_to_attrs_free' tag_attr thy (cid, filtered_attr_list) =
      if DOF_core.is_virtual cid thy
      then (tag_attr (serial ()))::(map (attr_to_free) filtered_attr_list)
      else (map (attr_to_free) filtered_attr_list)
    val class_list'' = flat (map (add_tag_to_attrs_free' tag_attr thy) class_list')
  in list_comb (make_const, (tag_attr (serial()))::class_list'') end


fun check_classref {is_monitor=is_monitor} (SOME(cid,pos')) thy = 
          let 
              val cid_long = DOF_core.read_cid_global thy cid  
                            
              val {id, name=bind_target,rex,...} = the(DOF_core.get_doc_class_global cid_long thy)
              val _ = if is_monitor andalso (null rex orelse cid_long= DOF_core.default_cid ) 
                      then error("should be monitor class!")
                      else ()
              val markup = docclass_markup false cid id (Binding.pos_of bind_target);
              val ctxt = Context.Theory thy
              val _    = Context_Position.report_generic ctxt pos' markup;
          in  cid_long 
          end
   | check_classref _ NONE _ = DOF_core.default_cid 


fun generalize_typ n = Term.map_type_tfree (fn (str,sort)=> Term.TVar((str,n),sort));
fun infer_type thy term = hd (Type_Infer_Context.infer_types (Proof_Context.init_global thy) [term])


fun calc_update_term {mk_elaboration=mk_elaboration} thy cid_long
                     (S:(string * Position.T * string * term)list) term = 
    let val cid_ty = cid_2_cidType cid_long thy
        val generalize_term =  Term.map_types (generalize_typ 0)
        fun toString t = Syntax.string_of_term (Proof_Context.init_global thy) t  
        fun instantiate_term S t =
          Term_Subst.map_types_same (Term_Subst.instantiateT (TVars.make S)) (t)
        fun read_assn (lhs, pos:Position.T, opr, rhs) term =
            let 
                fun get_class_name parent_cid attribute_name pos =
                  let
                    val {attribute_decl, inherits_from, ...} =
                                                   the (DOF_core.get_doc_class_global parent_cid thy)
                  in
                    if exists (fn (binding, _, _) => Binding.name_of binding = attribute_name)
                              attribute_decl
                    then parent_cid
                    else
                      case inherits_from of
                          NONE =>
                                ISA_core.err ("Attribute not defined for class: " ^ cid_long) pos
                        | SOME (_, parent_name) =>
                                              get_class_name parent_name attribute_name pos
                  end
                val attr_defined_cid = get_class_name cid_long lhs pos
                val {id, name, ...} = the (DOF_core.get_doc_class_global attr_defined_cid thy)
                val markup = docclass_markup false cid_long id (Binding.pos_of name);
                val ctxt = Context.Theory thy
                val _    = Context_Position.report_generic ctxt pos markup;
                val info_opt = DOF_core.get_attribute_info cid_long (Long_Name.base_name lhs) thy
                val (ln,lnt,lnu,lnut) = case info_opt of 
                                           NONE => error ("unknown attribute >" 
                                                          ^((Long_Name.base_name lhs))
                                                          ^"< in class: "^cid_long)
                                        |  SOME{long_name, typ, ...} => (long_name, typ, 
                                                                         long_name ^ Record.updateN,
                                                                         (typ --> typ) 
                                                                          --> cid_ty --> cid_ty)
                val tyenv = Sign.typ_match thy  ((generalize_typ 0)(type_of rhs), lnt) (Vartab.empty)
                            handle Type.TYPE_MATCH => (error ("type of attribute: " ^ ln 
                                                             ^ " does not fit to term: " 
                                                             ^ toString rhs));
                val tyenv' = (map (fn (s,(t,u)) => ((s,t),u)) (Vartab.dest tyenv))
                val _ = if Long_Name.base_name lhs = lhs orelse ln = lhs then ()
                        else error("illegal notation for attribute of "^cid_long)
                fun join (ttt as \<^Type>\<open>int\<close>) = \<^Const>\<open>Groups.plus ttt\<close>
                   |join (ttt as \<^Type>\<open>set _\<close>) = \<^Const>\<open>Lattices.sup ttt\<close>
                   |join \<^Type>\<open>list A\<close> = \<^Const>\<open>List.append A\<close>
                   |join _ = error("implicit fusion operation not defined for attribute: "^ lhs)
                 (* could be extended to bool, map, multisets, ... *)
                val rhs' = instantiate_term tyenv' (generalize_term rhs)
                val rhs'' = DOF_core.transduce_term_global {mk_elaboration=mk_elaboration}
                                                           (rhs',pos) thy
             in case opr of 
                  "=" => Const(lnu,lnut) $ Abs ("uu_", lnt, rhs'') $ term
                | ":=" => Const(lnu,lnut) $ Abs ("uu_", lnt, rhs'') $ term
                | "+=" => Const(lnu,lnut) $ Abs ("uu_", lnt, join lnt $ (Bound 0) $ rhs'') $ term
                | _ => error "corrupted syntax - oops - this should not occur" 
             end   
     in Sign.certify_term thy  (fold read_assn S term) end

fun msg thy txt = if Config.get_global thy DOF_core.strict_monitor_checking
                  then error txt
                  else warning txt 

fun register_oid_cid_in_open_monitors oid pos cid_long thy = 
      let val {monitor_tab,...} = DOF_core.get_data_global thy
          fun is_enabled (n, info) = 
                         if exists (DOF_core.is_subclass_global thy cid_long) 
                                   (DOF_core.get_accepted_cids info) 
                         then SOME n 
                         else NONE
          (* filtering those monitors with automata, whose alphabet contains the
             cid of this oid. The enabled ones were selected and moved to their successor state
             along the super-class id. The evaluation is in parallel, simulating a product
             semantics without expanding the subclass relationship. *)
          fun is_enabled_for_cid moid =
                         let val {accepted_cids, automatas, ...} = 
                                              the(Symtab.lookup monitor_tab moid)
                             val indexS= 1 upto (length automatas)
                             val indexed_autoS = automatas ~~ indexS
                             fun check_for_cid (A,n) = 
                                   let val accS = (RegExpInterface.enabled A accepted_cids)
                                       val is_subclass = DOF_core.is_subclass_global thy
                                       val idx = find_index (is_subclass cid_long) accS
                                   in  if idx < 0 
                                       then (msg thy ("monitor "^moid^"(" ^ Int.toString n 
                                                       ^") not enabled for doc_class: "^cid_long);A)
                                       else RegExpInterface.next A accepted_cids (nth accS idx)
                                   end
                         in (moid,map check_for_cid indexed_autoS)  end  
          val enabled_monitors = List.mapPartial is_enabled (Symtab.dest monitor_tab)
          fun conv_attrs (((lhs, pos), opn), rhs) = (markup2string lhs,pos,opn, 
                                                     Syntax.read_term_global thy rhs)
          val trace_attr = [((("trace", @{here}), "+="), "[("^cid_long^", ''"^oid^"'')]")]
          val assns' = map conv_attrs trace_attr
          fun cid_of oid = #cid(the(DOF_core.get_object_global oid thy))
          fun def_trans_input_term  oid =
            #1 o (calc_update_term {mk_elaboration=false} thy (cid_of oid) assns')
          fun def_trans_value oid =
            (#1 o (calc_update_term {mk_elaboration=true} thy (cid_of oid) assns'))
            #> value (Proof_Context.init_global thy)
          val _ = if null enabled_monitors then () else writeln "registrating in monitors ..." 
          val _ = app (fn n => writeln(oid^" : "^cid_long^" ==> "^n)) enabled_monitors;
           (* check that any transition is possible : *)
          fun inst_class_inv x = DOF_core.get_class_invariant(cid_of x) thy x {is_monitor=false}
          fun class_inv_checks ctxt = map (fn x => inst_class_inv x ctxt) enabled_monitors
          val delta_autoS = map is_enabled_for_cid enabled_monitors; 
          fun update_info (n, aS) (tab: DOF_core.monitor_tab) =  
                         let val {accepted_cids,rejected_cids,...} = the(Symtab.lookup tab n)
                         in Symtab.update(n, {accepted_cids=accepted_cids, 
                                              rejected_cids=rejected_cids,
                                              automatas=aS}) tab end
          fun update_trace mon_oid = DOF_core.update_value_global mon_oid (def_trans_input_term mon_oid) (def_trans_value mon_oid)
          val update_automatons    = DOF_core.upd_monitor_tabs(fold update_info delta_autoS)
      in  thy |> (* update traces of all enabled monitors *)
                 fold (update_trace) (enabled_monitors)
              |> (* check class invariants of enabled monitors *)
                 (fn thy => (class_inv_checks (Context.Theory thy); thy))
              |> (* update the automata of enabled monitors *)
                 DOF_core.map_data_global(update_automatons)
      end

fun check_invariants thy oid =
  let
    val docitem_value = the (DOF_core.get_value_global oid thy)
    val cid = #cid (the (DOF_core.get_object_global oid thy))
    fun get_all_invariants cid thy =
       case DOF_core.get_doc_class_global cid thy of
          NONE => error("undefined class id for invariants: " ^ cid)
        | SOME ({inherits_from=NONE, invs, ...}) => invs
        | SOME ({inherits_from=SOME(_,father), invs, ...}) => (invs) @ (get_all_invariants father thy)
    val invariants = get_all_invariants cid thy
    val inv_and_apply_list = 
      let fun mk_inv_and_apply inv value thy =
            let val ((s, pos), _ (*term*)) = inv
                val inv_def = Syntax.read_term_global thy (s ^ invariant_suffixN)
                val inv_def_typ = Term.type_of value
            in case inv_def of
                   Const (s, Type (st, [_ (*ty*), ty'])) =>
                                        ((s, pos), Const (s, Type (st,[inv_def_typ, ty'])) $ value)
                 | _ => ((s, pos), inv_def $ value)
            end    
      in map (fn inv => mk_inv_and_apply inv docitem_value thy) invariants
      end
    fun check_invariants' ((inv_name, pos), term) =
      let val ctxt = Proof_Context.init_global thy
          val evaluated_term = value ctxt term
                handle ERROR e =>
                  if (String.isSubstring "Wellsortedness error" e)
                      andalso (Config.get_global thy DOF_core.invariants_checking_with_tactics)
                   then (warning("Invariants checking uses proof tactics");
                         let val prop_term = HOLogic.mk_Trueprop term
                             val thms = Proof_Context.get_thms ctxt (inv_name ^ def_suffixN)
                             (* Get the make definition (def(1) of the record) *)
                             val thms' =
                                  (Proof_Context.get_thms ctxt (Long_Name.append cid defsN)) @ thms
                             val _ = Goal.prove ctxt [] [] prop_term
                                                  (K ((unfold_tac ctxt thms') THEN (auto_tac ctxt)))
                                     |> Thm.close_derivation \<^here>
                                     handle ERROR e =>
                                       ISA_core.err ("Invariant "
                                                      ^ inv_name
                                                      ^ " failed to be checked using proof tactics"
                                                      ^ " with error: "
                                                      ^ e) pos
                         (* If Goal.prove does not fail, then the evaluation is considered True,
                            else an error is triggered by Goal.prove *)
                         in @{term True} end)
                   else ISA_core.err ("Invariant " ^ inv_name ^ " violated." ) pos
      in (if evaluated_term = \<^term>\<open>True\<close>
          then ((inv_name, pos), term)
          else ISA_core.err ("Invariant " ^ inv_name ^ " violated") pos)
      end
    val _ = map check_invariants' inv_and_apply_list 
  in thy end

fun create_and_check_docitem is_monitor {is_inline=is_inline} oid pos cid_pos doc_attrs thy = 
  let
    val id = serial ();                                 
    val _ = Position.report pos (docref_markup true oid id pos);
    (* creates a markup label for this position and reports it to the PIDE framework;
     this label is used as jump-target for point-and-click feature. *)
    val cid_long = check_classref is_monitor cid_pos thy
    val vcid = case cid_pos of   NONE => NONE
                               | SOME (cid,_) => if (DOF_core.is_virtual cid thy)
                                                 then SOME (DOF_core.parse_cid_global thy cid)
                                                 else NONE
    val value_terms = if (cid_long = DOF_core.default_cid)
                      then let
                            val undefined_value = Free ("Undefined_Value", \<^Type>\<open>unit\<close>)
                           in (undefined_value, undefined_value) end
                          (* 
                             Handle initialization of docitem without a class associated,
                             for example when you just want a document element to be referenceable
                             without using the burden of ontology classes.
                             ex: text*[sdf]\<open> Lorem ipsum @{thm refl}\<close>
                          *)
                     else let
                            val defaults_init = create_default_object thy cid_long
                            fun conv (na, _(*ty*), term) =(Binding.name_of na, Binding.pos_of na, "=", term);
                            val S = map conv (DOF_core.get_attribute_defaults cid_long thy);
                            val (defaults, _(*ty*), _) = calc_update_term {mk_elaboration=false}
                                                                      thy cid_long S defaults_init;
                            fun conv_attrs ((lhs, pos), rhs) = (markup2string lhs,pos,"=", Syntax.read_term_global thy rhs)
                            val assns' = map conv_attrs doc_attrs
                            val (input_term, _(*ty*), _) = calc_update_term {mk_elaboration=false}
                                                                        thy cid_long assns' defaults
                            val (value_term', _(*ty*), _) = calc_update_term {mk_elaboration=true}
                                                                        thy cid_long assns' defaults
                          in (input_term, value_term') end
    val check_inv =   (DOF_core.get_class_invariant cid_long thy oid is_monitor) 
                            o Context.Theory

  in thy |> DOF_core.define_object_global (oid, {pos        = pos, 
                                                 thy_name   = Context.theory_name thy,
                                                 input_term = fst value_terms,
                                                 value      = value (Proof_Context.init_global thy)
                                                                    (snd value_terms),
                                                 inline     = is_inline,
                                                 id         = id,
                                                 cid        = cid_long,
                                                 vcid       = vcid})
         |> register_oid_cid_in_open_monitors oid pos cid_long
         |> (fn thy => if #is_monitor(is_monitor)
                       then (((DOF_core.get_class_eager_invariant cid_long thy oid) is_monitor 
                               o Context.Theory) thy; thy)
                       else thy)
         |> (fn thy => (check_inv thy; thy))
         |> (fn thy => if Config.get_global thy DOF_core.invariants_checking = true
                       then check_invariants thy oid
                       else thy)
  end

end (* structure Docitem_Parser *)

fun meta_args_exec NONE thy = thy
   |meta_args_exec (SOME ((((oid,pos),cid_pos), doc_attrs) : ODL_Meta_Args_Parser.meta_args_t)) thy = 
         thy |> (Docitem_Parser.create_and_check_docitem 
                                    {is_monitor = false} {is_inline = false} 
                                    oid pos (I cid_pos) (I doc_attrs))

fun value_cmd {assert=assert} meta_args_opt raw_name modes raw_t pos thy  =
  let
    val thy' = meta_args_exec meta_args_opt thy
    val name = intern_evaluator thy' raw_name;
    val t = Syntax.read_term_global thy' raw_t;
    val term' = DOF_core.transduce_term_global {mk_elaboration=true} (t , pos)
                                          (thy');
    val t' = value_select name (Proof_Context.init_global thy') term';
    val ty' = Term.type_of t';
    val ty' = if assert
              then case ty' of
                       \<^typ>\<open>bool\<close> => ty'
                     | _ =>  error "Assertion expressions must be boolean."
              else ty'
    val t'  = if assert
              then case t'  of
                       \<^term>\<open>True\<close> => t'
                     | _ =>  error "Assertion failed."
              else t'
    val ctxt' = Proof_Context.augment t' (Proof_Context.init_global thy');
    val p = Print_Mode.with_modes modes (fn () =>
      Pretty.block [Pretty.quote (Syntax.pretty_term ctxt' t'), Pretty.fbrk,
        Pretty.str "::", Pretty.brk 1, Pretty.quote (Syntax.pretty_typ ctxt' ty')]) ();
    val _ = Pretty.writeln p 
  in  thy' end;

val opt_modes =
  Scan.optional (\<^keyword>\<open>(\<close> |-- Parse.!!! (Scan.repeat1 Parse.name --| \<^keyword>\<open>)\<close>)) [];

val opt_evaluator =
  Scan.optional (\<^keyword>\<open>[\<close> |-- Parse.name --| \<^keyword>\<open>]\<close>) "";

(*
  We want to have the current position to pass it to transduce_term_global in
  value_cmd, so we pass the Toplevel.transition
*)

val opt_attributes = Scan.option ODL_Meta_Args_Parser.attributes

fun pass_trans_to_value_cmd meta_args_opt ((name, modes), t)  =
let val pos = Position.none
in
   Toplevel.theory (value_cmd {assert=false} meta_args_opt name modes t pos) 
end

fun pass_trans_to_assert_value_cmd meta_args_opt ((name, modes), t) =
let val pos = Position.none
in
  Toplevel.theory (value_cmd {assert=true} meta_args_opt name modes t pos) 
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

(*
  We want to have the current position to pass it to transduce_term_global in
  string_of_term, so we pass the Toplevel.transition
*)


fun print_term meta_args_opt (string_list, string) trans =
let
  val pos = Toplevel.pos_of trans
  fun prin state str = string_of_term string pos (Toplevel.context_of state) 
in
  Toplevel.theory(fn thy =>
                     (print_item prin (string_list, string) (Toplevel.theory_toplevel thy); 
                     thy |> meta_args_exec meta_args_opt ) 
                 ) trans                    
end

val _ = Toplevel.theory
val _ = Toplevel.theory_toplevel 



(* setup ontology aware commands *)
val _ =
  Outer_Syntax.command \<^command_keyword>\<open>term*\<close> "read and print term"
    (opt_attributes -- (opt_modes -- Parse.term) 
     >> (fn (meta_args_opt, eval_args ) => print_term meta_args_opt eval_args));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>value*\<close> "evaluate and print term"
    (opt_attributes -- (opt_evaluator -- opt_modes -- Parse.term) 
     >> (fn (meta_args_opt, eval_args ) => pass_trans_to_value_cmd meta_args_opt eval_args));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>assert*\<close> "evaluate and assert term"
    (opt_attributes -- (opt_evaluator -- opt_modes -- Parse.term) 
     >> (fn (meta_args_opt, eval_args ) => pass_trans_to_assert_value_cmd meta_args_opt eval_args));

(* setup ontology - aware text antiquotations. Due to lexical restrictions, we can not
   declare them as value* or term*, although we will refer to them this way in papers. *)
local 
  fun pretty_term_style ctxt (style: term -> term, t) =
      Document_Output.pretty_term ctxt (style t);
in
val _ = Theory.setup
  (Document_Output.antiquotation_pretty_source_embedded \<^binding>\<open>value_\<close>
    (Scan.lift opt_evaluator -- Term_Style.parse -- Args.term)
    (fn ctxt => fn ((name, style), t) =>
      Document_Output.pretty_term ctxt (style (value_select name ctxt t)))
     (* incomplete : without validation and expansion TODO *)
  #> Document_Output.antiquotation_pretty_source_embedded \<^binding>\<open>term_\<close> 
             (Term_Style.parse -- Args.term) pretty_term_style 
     (* incomplete : without validation TODO *))
end

(* setup evaluators  *)
val _ = Theory.setup(
     add_evaluator (\<^binding>\<open>simp\<close>, Code_Simp.dynamic_value) #> snd
  #> add_evaluator (\<^binding>\<open>nbe\<close>, Nbe.dynamic_value) #> snd
  #> add_evaluator (\<^binding>\<open>code\<close>, Code_Evaluation.dynamic_value_strict) #> snd);


end;  (* structure Value_Command *)


structure Monitor_Command_Parser = 
struct

fun update_instance_command  (((oid:string,pos),cid_pos),
                              doc_attrs: (((string*Position.T)*string)*string)list) thy
            : theory = 
            let val cid = case DOF_core.get_object_global oid thy of 
                               SOME{pos=pos_decl,cid,id,...} => 
                                   let val markup = docref_markup false oid id pos_decl;
                                       val ctxt = Proof_Context.init_global thy;
                                       val _ = Context_Position.report ctxt pos markup;
                                   in  cid end
                             | NONE => error("undefined doc_class.")
                val cid_long = Value_Command.Docitem_Parser.check_classref {is_monitor = false}
                                                                                        cid_pos thy
                val _ = if cid_long = DOF_core.default_cid  orelse cid = cid_long 
                        then () 
                        else error("incompatible classes:"^cid^":"^cid_long)
         
                fun conv_attrs (((lhs, pos), opn), rhs) = ((markup2string lhs),pos,opn, 
                                                           Syntax.read_term_global thy rhs)
                val assns' = map conv_attrs doc_attrs
                val def_trans_input_term  =
                  #1 o (Value_Command.Docitem_Parser.calc_update_term {mk_elaboration=false}
                                                                                thy cid_long assns')
                val def_trans_value  =
                  #1 o (Value_Command.Docitem_Parser.calc_update_term {mk_elaboration=true}
                                                                                thy cid_long assns')
                  #> Value_Command.value (Proof_Context.init_global thy)
                fun check_inv thy =((DOF_core.get_class_invariant cid_long thy oid {is_monitor=false} 
                                     o Context.Theory ) thy ;
                                    thy)
            in     
                thy |> DOF_core.update_value_global oid def_trans_input_term def_trans_value
                    |> check_inv
                    |> (fn thy => if Config.get_global thy DOF_core.invariants_checking = true
                                  then Value_Command.Docitem_Parser.check_invariants thy oid
                                  else thy)
            end


(* General criticism : attributes like "level" were treated here in the kernel instead of dragging
   them out into the COL -- bu *)

fun open_monitor_command  ((((oid,pos),cid_pos), doc_attrs) : ODL_Meta_Args_Parser.meta_args_t) =
    let fun o_m_c oid pos cid_pos doc_attrs thy =
          Value_Command.Docitem_Parser.create_and_check_docitem 
            {is_monitor=true}  (* this is a monitor *)
            {is_inline=false} (* monitors are always inline *)                                                               
            oid pos cid_pos doc_attrs thy
        fun compute_enabled_set cid thy =
          let
            val long_cid = DOF_core.read_cid (Proof_Context.init_global thy) cid
          in
            case DOF_core.get_doc_class_global long_cid thy of
                SOME X => let val ralph = RegExpInterface.alphabet (#rejectS X)
                                     val alph = RegExpInterface.ext_alphabet ralph (#rex X)
                                 in  (alph, map (RegExpInterface.rexp_term2da alph)(#rex X)) end 
              | NONE => error("Internal error: class id undefined. ")
          end
        fun create_monitor_entry thy =  
            let val cid = case cid_pos of
                              NONE => ISA_core.err ("You must specified a monitor class.") pos
                            | SOME (cid, _) => cid
                val (S, aS) = compute_enabled_set cid thy
                val info = {accepted_cids = S, rejected_cids = [], automatas  = aS }
            in  DOF_core.map_data_global(DOF_core.upd_monitor_tabs(Symtab.update(oid, info )))(thy)
            end
    in
        create_monitor_entry  #> o_m_c oid pos cid_pos doc_attrs
    end;


fun close_monitor_command (args as (((oid:string,pos),cid_pos),
                                    doc_attrs: (((string*Position.T)*string)*string)list)) thy = 
    let val {monitor_tab,...} = DOF_core.get_data_global thy
        fun check_if_final aS = let val i = find_index (not o RegExpInterface.final) aS
                                in  if i >= 0 
                                    then
                                      Value_Command.Docitem_Parser.msg thy
                                        ("monitor number "^Int.toString i^" not in final state.")
                                    else ()
                                end
        val _ =  case Symtab.lookup monitor_tab oid of
                     SOME {automatas,...} => check_if_final automatas 
                  |  NONE => error ("Not belonging to a monitor class: "^oid)
        val delete_monitor_entry = DOF_core.map_data_global (DOF_core.upd_monitor_tabs (Symtab.delete oid))
        val {cid=cid_long, id, ...} = the(DOF_core.get_object_global oid thy)
        val markup = docref_markup false oid id pos;
        val _ = Context_Position.report (Proof_Context.init_global thy) pos markup;
        val check_inv =   (DOF_core.get_class_invariant cid_long thy oid) {is_monitor=true} 
                           o Context.Theory
        val check_lazy_inv =   (DOF_core.get_class_lazy_invariant cid_long thy oid) {is_monitor=true} 
                           o Context.Theory 
    in  thy |> (fn thy => (check_lazy_inv thy; thy))
            |> update_instance_command args
            |> (fn thy => (check_inv thy; thy))
            |> (fn thy => if Config.get_global thy DOF_core.invariants_checking = true
                          then Value_Command.Docitem_Parser.check_invariants thy oid
                          else thy)
            |> delete_monitor_entry
    end 


fun meta_args_2_latex thy ((((lab, _), cid_opt), attr_list) : ODL_Meta_Args_Parser.meta_args_t) =
    (* for the moment naive, i.e. without textual normalization of 
       attribute names and adapted term printing *)
    let val l   = "label = "^ (enclose "{" "}" lab)
      (*  val _   = writeln("meta_args_2_string lab:"^ lab ^":"^ (@{make_string } cid_opt) ) *)
        val cid_long = case cid_opt of
                                NONE => (case DOF_core.get_object_global lab thy of
                                           NONE => DOF_core.default_cid
                                         | SOME X => #cid X)
                              | SOME(cid,_) => DOF_core.parse_cid_global thy cid        
        (* val _   = writeln("meta_args_2_string cid_long:"^ cid_long ) *)
        val cid_txt  = "type = " ^ (enclose "{" "}" cid_long);

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


        fun ltx_of_term_dbg ctx encl term  = let 
              val t_str = ML_Syntax.print_term term  
                          handle (TERM _) => "Exception TERM in ltx_of_term_dbg (print_term)"
              val ltx = ltx_of_term ctx encl term
              val _ = writeln("<STRING>"^(Sledgehammer_Util.hackish_string_of_term ctx term)^"</STRING>")
              val _ = writeln("<LTX>"^ltx^"</LTX>")
              val _ = writeln("<TERM>"^t_str^"</TERM>")
            in ltx end 


        fun markup2string s = String.concat (List.filter (fn c => c <> Symbol.DEL) 
                                            (Symbol.explode (YXML.content_of s)))
        fun ltx_of_markup ctxt s = let
  	                            val term = (Syntax.check_term ctxt o Syntax.parse_term ctxt) s
                                val str_of_term = ltx_of_term  ctxt true term 
                                    handle _ => "Exception in ltx_of_term"
                              in
                                str_of_term
                              end 
        fun toLong n =  #long_name(the(DOF_core.get_attribute_info cid_long (markup2string n) thy))

        val ctxt = Proof_Context.init_global thy
        val actual_args =  map (fn ((lhs,_),rhs) => (toLong lhs, ltx_of_markup ctxt rhs))
                               attr_list  
	      val default_args = map (fn (b,_,t) => (toLong (Long_Name.base_name ( Sign.full_name thy b)), 
                                                       ltx_of_term ctxt true t))
                               (DOF_core.get_attribute_defaults cid_long thy)

        val default_args_filtered = filter (fn (a,_) => not (exists (fn b => b = a) 
                                    (map (fn (c,_) => c) actual_args))) default_args
        val str_args = map (fn (lhs,rhs) => lhs^" = "^(enclose "{" "}" rhs)) 
                      (actual_args@default_args_filtered)
        val label_and_type = String.concat [ l, ",", cid_txt]
        val str_args = label_and_type::str_args
    in
      Latex.string (enclose "[" "]" (String.concat [ label_and_type, ", args={", (commas str_args), "}"]))
    end

(* level-attribute information management *)
fun gen_enriched_document_cmd {inline} cid_transform attr_transform
    ((((oid,pos),cid_pos), doc_attrs) : ODL_Meta_Args_Parser.meta_args_t) : theory -> theory =
  Value_Command.Docitem_Parser.create_and_check_docitem {is_monitor = false} {is_inline = inline}
    oid pos (cid_transform cid_pos) (attr_transform doc_attrs);


(* markup reports and document output *)

(* {markdown = true} sets the parsing process such that in the text-core
   markdown elements are accepted. *)

fun document_output {markdown: bool, markup: Latex.text -> Latex.text} meta_args text ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val _ = Context_Position.reports ctxt (Document_Output.document_reports text);
    val output_meta = meta_args_2_latex thy meta_args;
    val output_text = Document_Output.output_document ctxt {markdown = markdown} text;
  in markup (output_meta @ output_text) end;

fun document_output_reports name {markdown, body} meta_args text ctxt =
  let
    val pos = Input.pos_of text;
    val _ =
      Context_Position.reports ctxt
        [(pos, Markup.language_document (Input.is_delimited text)),
         (pos, Markup.plain_text)];
    fun markup xml =
      let val m = if body then Markup.latex_body else Markup.latex_heading
      in [XML.Elem (m (Latex.output_name name), xml)] end;
  in document_output {markdown = markdown, markup = markup} meta_args text ctxt end;


(* document output commands *)

fun document_command (name, pos) descr mark cmd =
  Outer_Syntax.command (name, pos) descr
    (ODL_Meta_Args_Parser.attributes -- Parse.document_source >> (fn (meta_args, text) =>
      Toplevel.theory' (fn _ => cmd meta_args)
      (Toplevel.presentation_context #> document_output_reports name mark meta_args text #> SOME)));


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

val _ =
  document_command \<^command_keyword>\<open>text*\<close> "formal comment (primary style)"
    {markdown = true, body = true} (gen_enriched_document_cmd {inline=true} I I);


(* This is just a stub at present *)
val _ =
  document_command \<^command_keyword>\<open>text-macro*\<close> "formal comment macro"
    {markdown = true, body = true}
    (gen_enriched_document_cmd {inline=false} (* declare as macro *) I I);

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>declare_reference*\<close>
                       "declare document reference"
                       (ODL_Meta_Args_Parser.attributes >> (fn (((oid,pos),cid),doc_attrs) =>  
                                      (Toplevel.theory (DOF_core.declare_object_global oid))));

end (* structure Monitor_Command_Parser *)
\<close>



ML\<open>
fun print_doc_classes b ctxt = 
    let val {docobj_tab={tab = x, ...},docclass_tab, ...} = DOF_core.get_data ctxt;
        val _ = writeln "=====================================";    
        fun print_attr (n, ty, NONE) = (Binding.print n)
          | print_attr (n, ty, SOME t)= (Binding.print n^"("^Syntax.string_of_term ctxt t^")")
        fun print_inv ((lab,pos),trm) = (lab ^"::"^Syntax.string_of_term ctxt trm)
        fun print_virtual {virtual} = Bool.toString virtual
        fun print_class (n, {attribute_decl, id, inherits_from, name, virtual, params, thy_name, rejectS, rex,invs}) =
           (case inherits_from of 
               NONE => writeln ("docclass: "^n)
             | SOME(_,nn) => writeln ("docclass: "^n^" = "^nn^" + ");
            writeln ("    name:       "^(Binding.print name));
            writeln ("    virtual:    "^(print_virtual virtual));
            writeln ("    origin:     "^thy_name);
            writeln ("    attrs:      "^commas (map print_attr attribute_decl));
            writeln ("    invs:       "^commas (map print_inv invs))
           );
    in  map print_class (Symtab.dest docclass_tab); 
        writeln "=====================================\n\n\n" 
    end;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_doc_classes\<close> "print document classes"
    (Parse.opt_bang >> (fn b => Toplevel.keep (print_doc_classes b o Toplevel.context_of)));

fun print_docclass_template cid ctxt = 
    let val cid_long = DOF_core.read_cid ctxt cid  (* assure that given cid is really a long_cid *)
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

fun print_doc_items b ctxt = 
    let val {docobj_tab={tab = x, ...},...}= DOF_core.get_data ctxt;
        val _ = writeln "=====================================";  
        fun dfg true = "true" 
           |dfg false= "false"   
        fun print_item (n, SOME({cid,vcid,id,pos,thy_name,inline, input_term, value})) =
                 (writeln ("docitem:             "^n);
                  writeln ("    type:            "^cid);
                  case vcid of NONE => () | SOME (s) => 
                  writeln ("    virtual type:    "^ s);
                  writeln ("    origin:          "^thy_name);
                  writeln ("    inline:          "^dfg inline);
                  writeln ("    input_term:      "^ (Syntax.string_of_term ctxt input_term));
                  writeln ("    value:           "^ (Syntax.string_of_term ctxt value))
                 )
          | print_item (n, NONE) = 
                 (writeln ("forward reference for docitem: "^n));
    in  map print_item (Symtab.dest x); 
        writeln "=====================================\n\n\n" end;

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>print_doc_items\<close>  "print document items"
    (Parse.opt_bang >> (fn b => Toplevel.keep (print_doc_items b o Toplevel.context_of)));

fun check_doc_global (strict_checking : bool) ctxt = 
    let val {docobj_tab={tab = x, ...}, monitor_tab, ...} = DOF_core.get_data ctxt;
        val S = map_filter (fn (s,NONE) => SOME s | _ => NONE) (Symtab.dest x)
        val T = map fst (Symtab.dest monitor_tab)
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

\<close>

\<comment> \<open>c.f. \<^file>\<open>~~/src/Pure/Isar/outer_syntax.ML\<close>\<close>
(*
  The ML* generates an "ontology-aware" version of the SML code-execution command.
*)
ML\<open>
structure ML_star_Command =
struct

fun meta_args_exec NONE  = I:generic_theory -> generic_theory
   |meta_args_exec (SOME ((((oid,pos),cid_pos), doc_attrs) : ODL_Meta_Args_Parser.meta_args_t))  = 
          Context.map_theory (Value_Command.Docitem_Parser.create_and_check_docitem 
                                    {is_monitor = false} {is_inline = false} 
                                    oid pos (I cid_pos) (I doc_attrs))

val attributes_opt = Scan.option ODL_Meta_Args_Parser.attributes

val _ =
  Outer_Syntax.command ("ML*", \<^here>) "ODL annotated ML text within theory or local theory"
    ((attributes_opt -- Parse.ML_source) 
     >> (fn (meta_args_opt, source) =>
            (*Toplevel.theory (meta_args_exec meta_args_opt)
            #>*)
            Toplevel.generic_theory
              ((ML_Context.exec (fn () =>  
                     (ML_Context.eval_source (ML_Compiler.verbose true ML_Compiler.flags) source)) 
              #> (meta_args_exec meta_args_opt) 
              #> Local_Theory.propagate_ml_env))));

end
\<close>

ML\<open>
structure ODL_LTX_Converter = 
struct

fun meta_args_2_string thy ((((lab, _), cid_opt), attr_list) : ODL_Meta_Args_Parser.meta_args_t) = 
    (* for the moment naive, i.e. without textual normalization of 
       attribute names and adapted term printing *)
    let val l   = "label = "^ (enclose "{" "}" lab)
      (*  val _   = writeln("meta_args_2_string lab:"^ lab ^":"^ (@{make_string } cid_opt) ) *)
        val cid_long = case cid_opt of
                                NONE => (case DOF_core.get_object_global lab thy of
                                           NONE => DOF_core.default_cid
                                         | SOME X => #cid X)
                              | SOME(cid,_) => DOF_core.parse_cid_global thy cid        
        (* val _   = writeln("meta_args_2_string cid_long:"^ cid_long ) *)
        val cid_txt  = "type = " ^ (enclose "{" "}" cid_long);

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


        fun ltx_of_term_dbg ctx encl term  = let 
              val t_str = ML_Syntax.print_term term  
                          handle (TERM _) => "Exception TERM in ltx_of_term_dbg (print_term)"
              val ltx = ltx_of_term ctx encl term
              val _ = writeln("<STRING>"^(Sledgehammer_Util.hackish_string_of_term ctx term)^"</STRING>")
              val _ = writeln("<LTX>"^ltx^"</LTX>")
              val _ = writeln("<TERM>"^t_str^"</TERM>")
            in ltx end 


        fun markup2string s = String.concat (List.filter (fn c => c <> Symbol.DEL) 
                                            (Symbol.explode (YXML.content_of s)))
        fun ltx_of_markup ctxt s = let
  	                            val term = (Syntax.check_term ctxt o Syntax.parse_term ctxt) s
                                val str_of_term = ltx_of_term  ctxt true term 
                                    handle _ => "Exception in ltx_of_term"
                              in
                                str_of_term
                              end 
        fun toLong n =  #long_name(the(DOF_core.get_attribute_info cid_long (markup2string n) thy))

        val ctxt = Proof_Context.init_global thy
        val actual_args =  map (fn ((lhs,_),rhs) => (toLong lhs, ltx_of_markup ctxt rhs))
                               attr_list  
	      val default_args = map (fn (b,_,t) => (toLong (Long_Name.base_name ( Sign.full_name thy b)), 
                                                       ltx_of_term ctxt true t))
                               (DOF_core.get_attribute_defaults cid_long thy)

        val default_args_filtered = filter (fn (a,_) => not (exists (fn b => b = a) 
                                    (map (fn (c,_) => c) actual_args))) default_args
        val str_args = map (fn (lhs,rhs) => lhs^" = "^(enclose "{" "}" rhs)) 
                      (actual_args@default_args_filtered)
        val label_and_type = String.concat [ l, ",", cid_txt]
        val str_args = label_and_type::str_args
    in
      (enclose "[" "]" (String.concat [ label_and_type, ", args={", (commas str_args), "}"])) 
end

end

\<close>

 
section\<open> Syntax for Ontological Antiquotations (the '' View'' Part II) \<close>

ML\<open>
structure OntoLinkParser = 
struct

val basic_entity = Document_Output.antiquotation_pretty_source
    : binding -> 'a context_parser -> (Proof.context -> 'a -> Pretty.T) -> theory -> theory;

fun check_and_mark ctxt cid_decl (str:{strict_checking: bool}) {inline=inline_req} pos name  =
  let
    val thy = Proof_Context.theory_of ctxt;
  in 
    if DOF_core.is_defined_oid_global name thy 
    then let val {pos=pos_decl,id,cid,inline,...} = the(DOF_core.get_object_global name thy)
             val _ = if not inline_req 
                     then if inline then () else error("referred text-element is macro! (try option display)")
                     else if not inline then () else error("referred text-element is no macro!")
             val markup = docref_markup false name id pos_decl;
             val _ = Context_Position.report ctxt pos markup;
                     (* this sends a report for a ref application to the PIDE interface ... *) 
             val _ = if not(DOF_core.is_subclass ctxt cid cid_decl)
                     then error("reference ontologically inconsistent: "^cid
                                ^" must be subclass of "^cid_decl^ Position.here pos_decl)
                     else ()
         in () end
    else if   DOF_core.is_declared_oid_global name thy 
         then (if #strict_checking str 
               then warning("declared but undefined document reference: "^name) 
               else ())
         else error("undefined document reference: "^name)
  end

val _ =  check_and_mark : Proof.context ->  string ->  
                          {strict_checking: bool} -> {inline:bool} ->
                          Position.T -> Symtab.key -> unit

(* generic syntax for doc_class links. *) 

val defineN    = "define"
val uncheckedN = "unchecked" 

val docitem_modes = Scan.optional (Args.parens (Args.$$$ defineN || Args.$$$ uncheckedN) 
                                   >> (fn str => if str = defineN 
                                                 then {unchecked = false, define= true}  
                                                 else {unchecked = true,  define= false})) 
                                   {unchecked = false, define= false} (* default *);


val docitem_antiquotation_parser = (Scan.lift (docitem_modes -- Parse.embedded_input))
                                   : ({define:bool,unchecked:bool} * Input.source) context_parser;


fun pretty_docitem_antiquotation_generic cid_decl ctxt ({unchecked, define}, src ) = 
    let val (str,pos) = Input.source_content src
        val inline = Config.get ctxt Document_Antiquotation.thy_output_display
        val _ = check_and_mark ctxt cid_decl {strict_checking = not unchecked} 
                                             {inline = inline} pos str
    in  
        (case (define,inline) of
            (true,false) => XML.enclose("\\csname isaDof.label\\endcsname[type={"^cid_decl^"}]   {")"}" 
           |(false,false)=> XML.enclose("\\csname isaDof.ref\\endcsname[type={"^cid_decl^"}]     {")"}"
           |(true,true)  => XML.enclose("\\csname isaDof.macroDef\\endcsname[type={"^cid_decl^"}]{")"}" 
           |(false,true) => XML.enclose("\\csname isaDof.macroExp\\endcsname[type={"^cid_decl^"}]{")"}"
        )
        (Latex.text (Input.source_content src))
    end      


fun docitem_antiquotation bind cid = 
    Document_Output.antiquotation_raw bind  docitem_antiquotation_parser 
                                       (pretty_docitem_antiquotation_generic cid);


fun check_and_mark_term ctxt oid  =
  let val thy = Context.theory_of ctxt;
  in  if DOF_core.is_defined_oid_global oid thy 
      then let val {pos=pos_decl,id,cid,value,...} = the(DOF_core.get_object_global oid thy)
               val markup = docref_markup false oid id pos_decl;
               val _ = Context_Position.report_generic ctxt pos_decl markup;
                       (* this sends a report for a ref application to the PIDE interface ... *) 
               val _ = if cid = DOF_core.default_cid
                       then error("anonymous "^ DOF_core.default_cid ^ " class has no value" )
                       else ()
           in  value end
      else error("undefined document reference:"^oid)
  end
                 
                                         
fun ML_antiquotation_docitem_value (ctxt, toks) = 
    (Scan.lift (Args.cartouche_input) 
     >> (fn inp => (ML_Syntax.atomic o ML_Syntax.print_term) 
                   ((check_and_mark_term ctxt o fst o Input.source_content) inp)))
     (ctxt, toks)

(* Setup for general docitems of the global DOF_core.default_cid - class ("text")*)
val _ = Theory.setup
           (docitem_antiquotation   \<^binding>\<open>docitem\<close>  DOF_core.default_cid #>
            
            ML_Antiquotation.inline \<^binding>\<open>docitem_value\<close> ML_antiquotation_docitem_value)

end (* struct *)
\<close>


ML\<open> 
structure AttributeAccess = 
struct

val basic_entity = Document_Output.antiquotation_pretty_source 
    : binding -> 'a context_parser -> (Proof.context -> 'a -> Pretty.T) -> theory -> theory;

fun compute_trace_ML ctxt oid pos_opt pos' =
    (* grabs attribute, and converts its HOL-term into (textual) ML representation *)
  let val term = ISA_core.compute_attr_access ctxt "trace" oid pos_opt pos'
      fun conv (\<^Const>\<open>Pair \<^typ>\<open>doc_class rexp\<close> \<^typ>\<open>string\<close>\<close>
                  $ (\<^Const>\<open>Atom \<^typ>\<open>doc_class\<close>\<close> $ (\<^Const>\<open>mk\<close> $ s)) $ S) =
        let val s' =  DOF_core.read_cid (Context.proof_of ctxt) (HOLogic.dest_string s)
        in (s', HOLogic.dest_string S) end
  in  map conv (HOLogic.dest_list term) end


val parse_oid  = Scan.lift(Parse.position Args.name) 
val parse_cid  = Scan.lift(Parse.position Args.name) 
val parse_oid' = Term_Style.parse -- parse_oid
val parse_cid' = Term_Style.parse -- parse_cid



val parse_attribute_access = (parse_oid
                              --| (Scan.lift @{keyword "::"}) 
                              -- Scan.lift (Parse.position Args.name))
                              : ((string *Position.T) * (string * Position.T)) context_parser 

val parse_attribute_access' = Term_Style.parse -- parse_attribute_access
                              : ((term -> term) *
                                 ((string * Position.T) * (string * Position.T))) context_parser

fun attr_2_ML ctxt ((attr:string,pos),(oid:string,pos')) = (ML_Syntax.atomic o ML_Syntax.print_term) 
                                                           (ISA_core.compute_attr_access ctxt attr oid (SOME pos) pos') 


val TERM_STORE = let val dummy_term = Bound 0
                 in  Unsynchronized.ref (dummy_term) end

fun get_instance_value_2_ML ctxt (oid:string,pos) =
    let val term = case DOF_core.get_value_global oid (Context.theory_of ctxt) of
                    SOME(t) => t
                  | NONE    => error "not an object id"
        val _ = (TERM_STORE := term)  (* export to the ML Context *)
    in  "! AttributeAccess.TERM_STORE" end


fun trace_attr_2_ML ctxt (oid:string,pos) =
    let val print_string_pair = ML_Syntax.print_pair  ML_Syntax.print_string ML_Syntax.print_string
        val toML = (ML_Syntax.atomic o (ML_Syntax.print_list print_string_pair))
    in  toML (compute_trace_ML ctxt oid NONE pos) end 

fun compute_cid_repr ctxt cid pos = 
      if DOF_core.is_defined_cid_local  cid ctxt then Const(cid,dummyT)
      else ISA_core.err ("Undefined Class Identifier:"^cid) pos

local

fun pretty_attr_access_style ctxt (style, ((attr,pos),(oid,pos'))) = 
           Document_Output.pretty_term ctxt (style (ISA_core.compute_attr_access (Context.Proof ctxt) 
                                                                    attr oid (SOME pos) pos'));
fun pretty_trace_style ctxt (style, (oid,pos)) = 
          Document_Output.pretty_term ctxt (style (ISA_core.compute_attr_access  (Context.Proof ctxt) 
                                                                   "trace" oid NONE pos));
fun pretty_cid_style ctxt (style, (cid,pos)) = 
          Document_Output.pretty_term ctxt (style (compute_cid_repr ctxt cid pos));

(* NEW VERSION: PLEASE INTEGRATE ALL OVER : *)
fun context_position_parser parse_con (ctxt, toks) = 
     let val pos = case toks of 
                    a :: _ => Token.pos_of a 
                  | _ => @{here}             \<comment> \<open>a real hack !\<close>
         val (res, (ctxt', toks')) = parse_con (ctxt, toks)
     in  ((res,pos),(ctxt', toks')) end

val parse_cid = (context_position_parser Args.typ_abbrev)
          >> (fn (Type(ss,_),pos) =>  (pos,ss)
                |( _,pos) => ISA_core.err "Undefined Class Id" pos);


val parse_cid' = Term_Style.parse -- parse_cid

fun pretty_cid_style ctxt (style,(pos,cid)) = 
    (*reconversion to term in order to haave access to term print options like: short_names etc...) *)
          Document_Output.pretty_term ctxt ((compute_cid_repr ctxt cid pos));

in
val _ = Theory.setup 
           (ML_Antiquotation.inline  \<^binding>\<open>docitem\<close> 
               (fn (ctxt,toks) => (parse_oid >> get_instance_value_2_ML ctxt) (ctxt, toks))  #>
            ML_Antiquotation.inline  \<^binding>\<open>docitem_attribute\<close> 
               (fn (ctxt,toks) => (parse_attribute_access >>  attr_2_ML ctxt) (ctxt, toks))  #>
            ML_Antiquotation.inline  \<^binding>\<open>trace_attribute\<close>  
               (fn (ctxt,toks) => (parse_oid >> trace_attr_2_ML ctxt) (ctxt, toks)) #>
            basic_entity  \<^binding>\<open>trace_attribute\<close>  parse_oid'  pretty_trace_style #>
            basic_entity  \<^binding>\<open>doc_class\<close>  parse_cid'  pretty_cid_style #>
            basic_entity  \<^binding>\<open>onto_class\<close> parse_cid'  pretty_cid_style #>
            basic_entity  \<^binding>\<open>docitem_attribute\<close>  parse_attribute_access' pretty_attr_access_style
           )
end
end
\<close>

text\<open> Note that the functions \<^verbatim>\<open>basic_entities\<close> and \<^verbatim>\<open>basic_entity\<close> in 
      @{ML_structure AttributeAccess} are copied from 
      @{file "$ISABELLE_HOME/src/Pure/Thy/document_output.ML"} \<close>


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
      val Ts = Syntax.read_typs ctxt (map (fn ((_, raw_T, _),_) => raw_T) raw_fields);
      val terms = map ((map_option (Syntax.read_term ctxt)) o snd) raw_fields
      fun test t1 t2 = Sign.typ_instance (Proof_Context.theory_of ctxt)
                                         (t1, Value_Command.Docitem_Parser.generalize_typ 0 t2) 
      fun check_default (ty,SOME trm) = 
                  let val ty' = (type_of trm)
                  in if test ty ty' 
                     then ()
                     else error("type mismatch:"^ 
                                (Syntax.string_of_typ ctxt ty')^":"^ 
                                (Syntax.string_of_typ ctxt ty))
                  end
                                                   (* BAD STYLE : better would be catching exn. *) 
         |check_default (_,_) = ()  
      val fields = map2 (fn ((x, _, mx),_) => fn T => (x, T, mx)) raw_fields Ts;
      val _ = map check_default (Ts ~~ terms) (* checking types conform to defaults *) 
      val ctxt' = fold Variable.declare_typ Ts ctxt;
    in (fields, terms, ctxt') end;

val trace_attr = ((\<^binding>\<open>trace\<close>, "(doc_class rexp \<times> string) list",Mixfix.NoSyn),
                  SOME "[]"): ((binding * string * mixfix) * string option)

fun def_cmd (decl, spec, prems, params) lthy =
  let
    val ((lhs as Free (x, T), _), lthy') = Specification.definition decl params prems spec lthy;
    val lhs' = Morphism.term (Local_Theory.target_morphism lthy') lhs;
    val _ =
      Proof_Display.print_consts true (Position.thread_data ()) lthy'
        (Frees.defined (Frees.build (Frees.add_frees lhs'))) [(x, T)]
  in lthy' end

fun mk_meta_eq (t, u) = \<^Const>\<open>Pure.eq \<open>fastype_of t\<close> for t u\<close>;

fun define_cond binding f_sty   cond_suffix read_cond (ctxt:local_theory) = 
       let val bdg = Binding.suffix_name cond_suffix binding
           val eq =  mk_meta_eq(Free(Binding.name_of bdg, f_sty),read_cond)
           val args = (SOME(bdg,NONE,NoSyn), (Binding.empty_atts,eq),[],[])
       in def_cmd args ctxt end

fun define_inv cid_long ((lbl, pos), inv) thy = 
    let val bdg = Binding.make (lbl,pos)
        val inv_term = Syntax.read_term (Proof_Context.init_global thy) inv
        fun update_attribute_type thy class_scheme_ty
            (Const (s, Type (st,[ty, ty'])) $ t) =
              let
                val cid = Long_Name.qualifier s
              in case DOF_core.get_doc_class_global cid thy of
                     NONE => Const (s, Type(st,[ty, ty']))
                             $ (update_attribute_type thy class_scheme_ty t)
                   | SOME _ => Const(s, Type(st,[class_scheme_ty, ty']))
                               $ (update_attribute_type thy class_scheme_ty t)
              end
          | update_attribute_type thy class_scheme_ty (t $ t') =
              (update_attribute_type thy class_scheme_ty t)
              $ (update_attribute_type thy class_scheme_ty t')
          | update_attribute_type thy class_scheme_ty (Abs(s, ty, t)) =
              Abs(s, ty, update_attribute_type thy class_scheme_ty t)
          | update_attribute_type _ class_scheme_ty (Free(s, ty)) = if s = invariantN 
                                                                     then Free (s, class_scheme_ty)
                                                                     else Free (s, ty)
          | update_attribute_type _ _ t = t
        val inv_ty = Syntax.read_typ (Proof_Context.init_global thy)
                                     (Name.aT ^ " " ^ cid_long ^ schemeN)
        (* Update the type of each attribute update function to match the type of the
           current class. *)
        val inv_term' = update_attribute_type thy inv_ty inv_term
        val eq_inv_ty = inv_ty --> HOLogic.boolT
        val abs_term = Term.lambda (Free (invariantN, inv_ty)) inv_term'
    in  thy |> Named_Target.theory_map (define_cond bdg eq_inv_ty invariant_suffixN abs_term) end

fun add_doc_class_cmd overloaded (raw_params, binding)
                      raw_parent raw_fieldsNdefaults reject_Atoms regexps invariants thy =
    let
      val ctxt = Proof_Context.init_global thy;
      val params = map (apsnd (Typedecl.read_constraint ctxt)) raw_params;
      val ctxt1 = fold (Variable.declare_typ o TFree) params ctxt;
      fun cid thy = DOF_core.parse_cid_global thy (Binding.name_of binding)    
      val (parent, ctxt2) = read_parent raw_parent ctxt1;
      val parent_cid_long =  map_optional snd DOF_core.default_cid parent;
      (* takes class synonyms into account *)
      val parent' = map_option (map_snd (K (DOF_core.read_cid_global thy parent_cid_long))) parent
      val parent'_cid_long =  map_optional snd DOF_core.default_cid parent';
      val raw_fieldsNdefaults' = filter (fn((bi,_,_),_) => Binding.name_of bi <> "trace") 
                                        raw_fieldsNdefaults
      val _ = if length raw_fieldsNdefaults' <> length raw_fieldsNdefaults 
              then warning("re-declaration of trace attribute in monitor --- ignored")
              else ()
      val raw_fieldsNdefaults'' = if  null regexps  
                                  then raw_fieldsNdefaults' 
                                  else trace_attr::raw_fieldsNdefaults' 
      val (fields, terms, ctxt3) = read_fields raw_fieldsNdefaults'' ctxt2;
      val fieldsNterms = (map (fn (a,b,_) => (a,b)) fields) ~~ terms
      val fieldsNterms' = map (fn ((x,y),z) => (x,y,z)) fieldsNterms
      val params' = map (Proof_Context.check_tfree ctxt3) params;
      fun check_n_filter thy (bind,ty,mf) = 
                     case DOF_core.get_attribute_info parent'_cid_long (Binding.name_of bind) thy of
                      NONE => SOME(bind,ty,mf)
                      | SOME{def_occurrence,long_name,typ,...}
                          => if ty = typ 
                             then (warning("overriding attribute:"
                                           ^ long_name
                                           ^ " in doc class:"
                                           ^ def_occurrence);
                                   NONE)
                             else error("no overloading allowed.")
      val record_fields = map_filter (check_n_filter thy) fields
              (* adding const symbol representing doc-class for Monitor-RegExps.*)
      val constant_typ = \<^typ>\<open>doc_class rexp\<close>
      val constant_term = \<^Const>\<open>Atom \<^typ>\<open>doc_class\<close>\<close>
                         $ (\<^Const>\<open>mk\<close>
                         $ HOLogic.mk_string (Binding.name_of binding))
      val eq =  mk_meta_eq(Free(Binding.name_of binding, constant_typ), constant_term)
      val args = (SOME(binding,NONE,NoSyn), (Binding.empty_atts,eq),[],[])
    in thy |> Named_Target.theory_map (def_cmd args)
           |> (fn thy =>
                 case parent' of
                     NONE => (Record.add_record
                          overloaded (params', binding) parent' (DOF_core.tag_attr::record_fields)
                             #> DOF_core.define_doc_class_global
                                                    (params', binding) parent fieldsNterms' regexps 
                                                    reject_Atoms invariants {virtual=false}) thy
                   | SOME _  =>
                       if (not o null) record_fields
                       then (Record.add_record overloaded (params', binding) parent' (record_fields)
                            #> DOF_core.define_doc_class_global
                                                    (params', binding) parent fieldsNterms' regexps 
                                                    reject_Atoms invariants {virtual=false}) thy
                       else (Record.add_record
                                        overloaded (params', binding) parent' ([DOF_core.tag_attr])
                             #> DOF_core.define_doc_class_global
                                                    (params', binding) parent fieldsNterms' regexps 
                                                    reject_Atoms invariants {virtual=true}) thy)

           |> (fn thy => OntoLinkParser.docitem_antiquotation binding (cid thy) thy)
              (* defines the ontology-checked text antiquotation to this document class *)
           |> (fn thy => fold(define_inv (cid thy)) (invariants) thy)
           (* The function declare_ISA_class_accessor_and_check_instance uses a prefix
              because the class name is already bound to "doc_class Regular_Exp.rexp" constant
              by add_doc_class_cmd function *)
           |> ISA_core.declare_ISA_class_accessor_and_check_instance binding
           |> (fn thy => (ISA_core.declare_class_instances_annotation thy binding) thy)
    end;
           

(* repackaging argument list *)
fun add_doc_class_cmd' (((overloaded, hdr), (parent, attrs)),((rejects,accept_rex),invars)) =
    (add_doc_class_cmd {overloaded = overloaded} hdr parent attrs rejects accept_rex invars)

val parse_invariants = Parse.and_list (Args.name_position --| Parse.$$$ "::" -- Parse.term)

val parse_doc_class = (Parse_Spec.overloaded 
      -- (Parse.type_args_constrained  -- Parse.binding) 
      -- (\<^keyword>\<open>=\<close>  
         |-- Scan.option (Parse.typ --| \<^keyword>\<open>+\<close>) 
          -- Scan.repeat1 (Parse.const_binding -- Scan.option (\<^keyword>\<open><=\<close> |-- Parse.term))
          )
      -- (   Scan.optional (\<^keyword>\<open>rejects\<close>    |-- Parse.enum1 "," Parse.term) []
          -- Scan.repeat   (\<^keyword>\<open>accepts\<close>    |-- Parse.term)
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



end (* struct *)
\<close>  



section\<open>Shortcuts, Macros, Environments\<close>
text\<open>The features described in this section are actually \<^emph>\<open>not\<close> real ISADOF features, rather a 
slightly more abstract layer over somewhat buried standard features of the Isabelle document 
generator ... (Thanks to Makarius) Conceptually, they are \<^emph>\<open>sub-text-elements\<close>. \<close>

text\<open>This module provides mechanisms to define front-end checked:
\<^enum> \<^emph>\<open>shortcuts\<close>, i.e. machine-checked abbreviations without arguments 
  that were mapped to user-defined LaTeX code (Example: \<^verbatim>\<open>\ie\<close>)
\<^enum> \<^emph>\<open>macros\<close>  with one argument that were mapped to user-defined code. Example: \<^verbatim>\<open>\myurl{bla}\<close>.
  The argument can be potentially checked and reports can be sent to PIDE;
  if no such checking is desired, this can be expressed by setting the
  \<^theory_text>\<open>reportNtest\<close>-parameter to \<^theory_text>\<open>K(K())\<close>.
\<^enum> \<^emph>\<open>macros\<close> with two arguments, potentially independently checked. See above. 
  Example: \<^verbatim>\<open>\myurl[ding]{dong}\<close>,
\<^enum> \<^emph>\<open>boxes\<close> which are more complex sub-text-elements in the line of the \<^verbatim>\<open>verbatim\<close> or 
  \<^verbatim>\<open>theory_text\<close> environments.

Note that we deliberately refrained from a code-template definition mechanism for simplicity,
so the patterns were just described by strings.  No additional ado with quoting/unquoting 
mechanisms ... 
\<close>

ML\<open>
structure DOF_lib =
struct
fun define_shortcut name latexshcut = 
       Document_Output.antiquotation_raw name (Scan.succeed ())
          (fn _ => fn () => Latex.string latexshcut) 

(* This is a generalization of the Isabelle2020 function "control_antiquotation" from 
   document_antiquotations.ML. (Thanks Makarius!) *)
fun define_macro name s1 s2 reportNtest =
      Document_Output.antiquotation_raw_embedded name (Scan.lift Args.cartouche_input)
         (fn ctxt => 
             fn src => let val () = reportNtest ctxt src 
                       in  src |>   XML.enclose s1 s2 
                                  o Document_Output.output_document ctxt {markdown = false}
                       end);

local (* hide away really strange local construction *)
fun enclose_body2 front body1 middle body2 post =
  (if front  = "" then [] else Latex.string front) @ body1 @
  (if middle = "" then [] else Latex.string middle) @ body2 @
  (if post   = "" then [] else Latex.string post);
in
fun define_macro2 name front middle post reportNtest1 reportNtest2 =
      Document_Output.antiquotation_raw_embedded name (Scan.lift (   Args.cartouche_input 
                                                             -- Args.cartouche_input))
         (fn ctxt => 
             fn (src1,src2) => let val () = reportNtest1 ctxt src1 
                                   val () = reportNtest2 ctxt src2 
                                   val T1 = Document_Output.output_document ctxt {markdown = false} src1
                                   val T2 = Document_Output.output_document ctxt {markdown = false} src2
                               in  enclose_body2 front T1 middle T2 post
                               end);
end

fun report_text ctxt text =
    let val pos = Input.pos_of text in
       Context_Position.reports ctxt
         [(pos, Markup.language_text (Input.is_delimited text)),
          (pos, Markup.raw_text)]
    end;

fun report_theory_text ctxt text =
    let val keywords = Thy_Header.get_keywords' ctxt;
        val _ = report_text ctxt text;
        val _ =
          Input.source_explode text
          |> Token.tokenize keywords {strict = true}
          |> maps (Token.reports keywords)
          |> Context_Position.reports_text ctxt;
    in () end

fun prepare_text ctxt =
  Input.source_content #> #1 #> Document_Antiquotation.prepare_lines ctxt;
(* This also produces indent-expansion and changes space to "\_" and the introduction of "\newline",
   I believe. Otherwise its in Thy_Output.output_source, the compiler from string to LaTeX.text. *)

fun string_2_text_antiquotation ctxt text = 
        prepare_text ctxt text
        |> Document_Output.output_source ctxt
        |> Document_Output.isabelle ctxt

fun string_2_theory_text_antiquotation ctxt text =
      let
        val keywords = Thy_Header.get_keywords' ctxt;
      in
        prepare_text ctxt text
        |> Token.explode0 keywords
        |> maps (Document_Output.output_token ctxt)
        |> Document_Output.isabelle ctxt
      end

fun gen_text_antiquotation name reportNcheck compile =
  Document_Output.antiquotation_raw_embedded name (Scan.lift Parse.embedded_input)
    (fn ctxt => fn text:Input.source =>
      let
        val _ = reportNcheck ctxt text;
      in
        compile ctxt text    
      end);

fun std_text_antiquotation name (* redefined in these more abstract terms *) =
    gen_text_antiquotation name report_text string_2_text_antiquotation

(* should be the same as (2020):
fun text_antiquotation name =
  Thy_Output.antiquotation_raw_embedded name (Scan.lift Parse.embedded_input)
    (fn ctxt => fn text =>
      let
        val _ = report_text ctxt text;
      in
        prepare_text ctxt text
        |> Thy_Output.output_source ctxt
        |> Thy_Output.isabelle ctxt
      end);
*)

fun std_theory_text_antiquotation name (* redefined in these more abstract terms *) =
    gen_text_antiquotation name report_theory_text string_2_theory_text_antiquotation

(* should be the same as (2020):
fun theory_text_antiquotation name =
  Thy_Output.antiquotation_raw_embedded name (Scan.lift Parse.embedded_input)
    (fn ctxt => fn text =>
      let
        val keywords = Thy_Header.get_keywords' ctxt;

        val _ = report_text ctxt text;
        val _ =
          Input.source_explode text
          |> Token.tokenize keywords {strict = true}
          |> maps (Token.reports keywords)
          |> Context_Position.reports_text ctxt;
      in
        prepare_text ctxt text
        |> Token.explode0 keywords
        |> maps (Thy_Output.output_token ctxt)
        |> Thy_Output.isabelle ctxt
        |> enclose_env ctxt "isarbox"
      end);
*)


fun environment_delim name =
 ("%\n\\begin{" ^ Latex.output_name name ^ "}\n",
  "\n\\end{" ^ Latex.output_name name ^ "}");

fun environment_block name = environment_delim name |-> XML.enclose;

fun enclose_env verbatim ctxt block_env body =
  if Config.get ctxt Document_Antiquotation.thy_output_display
  then if verbatim 
       then environment_block block_env body
       else Latex.environment block_env body
  else XML.enclose ("\\inline"^block_env ^"{") "}" body;

end
\<close>


ML\<open>
local 
val parse_literal = Parse.alt_string || Parse.cartouche
val parse_define_shortcut = Parse.binding -- ((\<^keyword>\<open>\<rightleftharpoons>\<close> || \<^keyword>\<open>==\<close>) |-- parse_literal)
val define_shortcuts = fold(uncurry DOF_lib.define_shortcut)
in
val _ =  Outer_Syntax.command \<^command_keyword>\<open>define_shortcut*\<close> "define LaTeX shortcut"
            (Scan.repeat1 parse_define_shortcut >> (Toplevel.theory o define_shortcuts));
end
\<close>

ML\<open>
val parse_literal = Parse.alt_string || Parse.cartouche
val parse_define_shortcut =  Parse.binding 
                             -- ((\<^keyword>\<open>\<rightleftharpoons>\<close> || \<^keyword>\<open>==\<close>) |-- parse_literal)
                             --|Parse.underscore
                             -- parse_literal
                             -- (Scan.option (\<^keyword>\<open>(\<close> |-- Parse.ML_source --|\<^keyword>\<open>)\<close>))

fun define_macro (X,NONE) = (uncurry(uncurry(uncurry DOF_lib.define_macro)))(X,K(K()))
   |define_macro (X,SOME(src:Input.source)) = 
       let val check_code = K(K()) (* hack *)
           val _ = warning "Checker code support Not Yet Implemented - use ML"
       in  (uncurry(uncurry(uncurry DOF_lib.define_macro)))(X,check_code)
       end;

val _ =  Outer_Syntax.command \<^command_keyword>\<open>define_macro*\<close> "define LaTeX shortcut"
            (Scan.repeat1 parse_define_shortcut >> (Toplevel.theory o (fold define_macro)));

\<close>


section \<open>Document templates\<close>

ML \<open>
signature DOCUMENT_CONTEXT =
sig
  val template_space: Context.generic -> Name_Space.T
  val ontology_space: Context.generic -> Name_Space.T
  val print_template: Context.generic -> string -> string
  val print_ontology: Context.generic -> string -> string
  val check_template: Context.generic -> xstring * Position.T -> string * string
  val check_ontology: Context.generic -> xstring * Position.T -> string * string
  val define_template: binding * string -> theory -> string * theory
  val define_ontology: binding * string -> theory -> string * theory
  val use_template: Context.generic -> xstring * Position.T -> unit
  val use_ontology: Context.generic -> (xstring * Position.T) list -> unit
end;

structure Document_Context: DOCUMENT_CONTEXT =
struct

(* theory data *)

local

structure Data = Theory_Data
(
  type T = string Name_Space.table * string Name_Space.table;
  val empty : T =
   (Name_Space.empty_table "document_template",
    Name_Space.empty_table "document_ontology");
  fun merge ((templates1, ontologies1), (templates2, ontologies2)) =
   (Name_Space.merge_tables (templates1, templates2),
    Name_Space.merge_tables (ontologies1, ontologies2));
);

fun naming_context thy =
  Proof_Context.init_global thy
  |> Proof_Context.map_naming (Name_Space.root_path #> Name_Space.add_path "Isabelle_DOF")
  |> Context.Proof;

fun get_space which = Name_Space.space_of_table o which o Data.get o Context.theory_of;

fun print which context =
  Name_Space.markup_extern (Context.proof_of context) (get_space which context)
  #> uncurry Markup.markup;

fun check which context arg =
  Name_Space.check context (which (Data.get (Context.theory_of context))) arg;

fun define (get, ap) (binding, arg) thy =
  let
    val (name, table') =
      Data.get thy |> get |> Name_Space.define (naming_context thy) true (binding, arg);
    val thy' = (Data.map o ap) (K table') thy;
  in (name, thy') end;

fun strip prfx sffx (path, pos) =
  (case try (unprefix prfx) (Path.file_name path) of
    NONE => error ("File name needs to have prefix " ^ quote prfx ^ Position.here pos)
  | SOME a =>
      (case try (unsuffix sffx) a of
        NONE => error ("File name needs to have suffix " ^ quote sffx ^ Position.here pos)
      | SOME b => b));

in

val template_space = get_space fst;
val ontology_space = get_space snd;

val print_template = print fst;
val print_ontology = print snd;

val check_template = check fst;
val check_ontology = check snd;

val define_template = define (fst, apfst);
val define_ontology = define (snd, apsnd);

fun use_template context arg =
  let val xml = arg |> check_template context |> snd |> XML.string
  in Export.export (Context.theory_of context) \<^path_binding>\<open>dof/root.tex\<close> xml end;

fun use_ontology context args =
  let
    val xml = args
      |> map (check_ontology context)
      |> let open XML.Encode in list (pair string string) end;
  in Export.export (Context.theory_of context) \<^path_binding>\<open>dof/ontologies\<close> xml end;

val strip_template = strip "root-" ".tex";
val strip_ontology = strip "DOF-" ".sty";

end;


(* Isar commands *)

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>use_template\<close>
    "use DOF document template (as defined within theory context)"
    (Parse.position Parse.name >> (fn arg =>
      Toplevel.theory (fn thy => (use_template (Context.Theory thy) arg; thy))));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>use_ontology\<close>
    "use DOF document ontologies (as defined within theory context)"
    (Parse.and_list1 (Parse.position Parse.name) >> (fn args =>
      Toplevel.theory (fn thy => (use_ontology (Context.Theory thy) args; thy))));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>define_template\<close>
    "define DOF document template (via LaTeX root file)"
    (Parse.position Resources.provide_parse_file >>
      (fn (get_file, pos) => Toplevel.theory (fn thy =>
        let
          val (file, thy') = get_file thy;
          val binding = Binding.make (strip_template (#src_path file, pos), pos);
          val text = cat_lines (#lines file);
        in #2 (define_template (binding, text) thy') end)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>define_ontology\<close>
    "define DOF document ontology (via LaTeX style file)"
    (Parse.position Resources.provide_parse_file >>
      (fn (get_file, pos) => Toplevel.theory (fn thy =>
        let
          val (file, thy') = get_file thy;
          val binding = Binding.make (strip_ontology (#src_path file, pos), pos);
          val text = cat_lines (#lines file);
        in #2 (define_ontology (binding, text) thy') end)));

end;
\<close>

define_template "../document-templates/root-eptcs-UNSUPPORTED.tex"
define_template "../document-templates/root-lipics-v2021-UNSUPPORTED.tex"
define_template "../document-templates/root-lncs.tex"
define_template "../document-templates/root-scrartcl.tex"
define_template "../document-templates/root-scrreprt-modern.tex"
define_template "../document-templates/root-scrreprt.tex"
define_template "../document-templates/root-svjour3-UNSUPPORTED.tex"

(*
ML\<open>
   Pretty.text;
   Pretty.str;
   Pretty.block_enclose;
   theory_text_antiquotation in Document_Antiquotations (not exported)
\<close>

ML\<open>Pretty.text_fold; Pretty.unformatted_string_of\<close>
ML\<open> (String.concatWith ","); Token.content_of\<close>


ML\<open>
 Document.state;
Session.get_keywords();
 Parse.command;
 Parse.tags;
\<close>
ML\<open>
 Outer_Syntax.print_commands @{theory};
 Outer_Syntax.parse_spans;
 Parse.!!!;

\<close>
*)

end
