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
           Assert
           
  keywords "+=" ":=" "accepts" "rejects"

  and      "title*"     "subtitle*"
           "chapter*"  "section*"    "subsection*"   "subsubsection*" 
           "paragraph*"  "subparagraph*" 
           "text*"       
           "figure*"
           "side_by_side_figure*" 
           "Definition*" "Lemma*" "Theorem*" "Conjecture*"
           :: document_body
           
  and      "open_monitor*" "close_monitor*" "declare_reference*" 
           "update_instance*" "doc_class" ::thy_decl

  and      (* "definition*" *) "corrollary*" "proposition*" "schematic_goal*" 
           "lemma*" "theorem*" (* -- intended replacement of Isar std commands.*) 
           "assert*"  ::thy_decl

  and      "print_doc_classes" "print_doc_items" "gen_sty_template"  "check_doc_global" :: diag
           
  
begin


section\<open>Primitive Markup Generators\<close>
ML\<open>

val docrefN   = "docref";    
val docclassN = "doc_class";    

(* derived from: theory_markup *) 
fun docref_markup_gen refN def name id pos =
  if id = 0 then Markup.empty
  else
    Markup.properties (Position.entity_properties_of def id pos)
      (Markup.entity refN name);   (* or better store the thy-name as property ? ? ? *)

val docref_markup = docref_markup_gen docrefN

val docclass_markup = docref_markup_gen docclassN

\<close>


section\<open> A HomeGrown Document Type Management (the ''Model'') \<close>
  
ML\<open>
structure DOF_core = 
struct
   type docclass_struct = {params         : (string * sort) list, (*currently not used *)
                           name           : binding, 
                           thy_name       : string, id : serial, (* for pide *)
                           inherits_from  : (typ list * string) option,      (* imports *)
                           attribute_decl : (binding * typ * term option) list, (* class local *)
                           rejectS        : term list,
                           rex            : term list  } (* monitoring regexps --- product semantics*)


   type docclass_tab = docclass_struct Symtab.table

   val  initial_docclass_tab = Symtab.empty:docclass_tab 

   fun  merge_docclass_tab (otab,otab') = Symtab.merge (op =) (otab,otab') 


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
                     value    : term, 
                     id       : serial, cid : string}

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

   type ISA_transformer_tab = (theory -> term * typ * Position.T -> term option) Symtab.table
   val  initial_ISA_tab:ISA_transformer_tab = Symtab.empty

   type docclass_inv_tab = (string -> {is_monitor:bool} -> Context.generic -> bool) Symtab.table
   val  initial_docclass_inv_tab : docclass_inv_tab = Symtab.empty

   type open_monitor_info = {accepted_cids : string list,
                             rejected_cids : string list,
                             automatas     : RegExpInterface.automaton list }

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
                docclass_inv_tab    : docclass_inv_tab}
  val empty  = {docobj_tab          = initial_docobj_tab,
                docclass_tab        = initial_docclass_tab,
                ISA_transformer_tab = initial_ISA_tab,
                monitor_tab         = initial_monitor_tab,
                docclass_inv_tab    = initial_docclass_inv_tab
               } 
  val extend =  I
  fun merge(   {docobj_tab=d1,docclass_tab = c1,
                 ISA_transformer_tab = e1, monitor_tab=m1,
                 docclass_inv_tab = n1},
               {docobj_tab=d2,docclass_tab = c2,
                 ISA_transformer_tab = e2, monitor_tab=m2,
                 docclass_inv_tab = n2})  = 
               {docobj_tab=merge_docobj_tab   (d1,d2), 
                docclass_tab = merge_docclass_tab (c1,c2),
                ISA_transformer_tab = Symtab.merge (fn (_ , _) => false)(e1,e2),
                monitor_tab =  override(m1,m2), 
                     (* PROVISORY  ... ITS A REAL QUESTION HOW TO DO THIS!*)
                docclass_inv_tab = override(n1,n2)
                     (* PROVISORY  ... ITS A REAL QUESTION HOW TO DO THIS!*)
               }
);


val get_data = Data.get o Context.Proof;
val map_data = Data.map;
val get_data_global = Data.get o Context.Theory;
val map_data_global = Context.theory_map o map_data;


fun upd_docobj_tab f {docobj_tab,docclass_tab,ISA_transformer_tab, monitor_tab,docclass_inv_tab} = 
            {docobj_tab = f docobj_tab, docclass_tab=docclass_tab, 
             ISA_transformer_tab=ISA_transformer_tab, monitor_tab=monitor_tab,
             docclass_inv_tab=docclass_inv_tab};
fun upd_docclass_tab f {docobj_tab=x,docclass_tab = y,ISA_transformer_tab = z, monitor_tab,  docclass_inv_tab} = 
            {docobj_tab=x,docclass_tab = f y,ISA_transformer_tab = z, monitor_tab=monitor_tab,
             docclass_inv_tab=docclass_inv_tab};
fun upd_ISA_transformers f{docobj_tab=x,docclass_tab = y,ISA_transformer_tab = z, monitor_tab, docclass_inv_tab} = 
            {docobj_tab=x,docclass_tab = y,ISA_transformer_tab = f z, monitor_tab=monitor_tab, 
             docclass_inv_tab=docclass_inv_tab};
fun upd_monitor_tabs f {docobj_tab,docclass_tab,ISA_transformer_tab, monitor_tab, docclass_inv_tab} = 
            {docobj_tab = docobj_tab,docclass_tab = docclass_tab,
             ISA_transformer_tab = ISA_transformer_tab, monitor_tab = f monitor_tab, 
             docclass_inv_tab=docclass_inv_tab};
fun upd_docclass_inv_tab f {docobj_tab,docclass_tab,ISA_transformer_tab, monitor_tab, docclass_inv_tab} = 
            {docobj_tab = docobj_tab,docclass_tab = docclass_tab,
             ISA_transformer_tab = ISA_transformer_tab, monitor_tab = monitor_tab, 
             docclass_inv_tab    = f docclass_inv_tab};


fun get_accepted_cids  ({accepted_cids, ... } : open_monitor_info) = accepted_cids
fun get_automatas      ({automatas, ... }     : open_monitor_info) = automatas


(* doc-class-name management: We still use the record-package for internally 
   representing doc-classes. The main motivation is that "links" to entities are
   types over doc-classes, *types* in the Isabelle sense, enriched by additional data.
   This has the advantage that the type-inference can be abused to infer long-names
   for doc-class-names. Note, however, that doc-classes are currently implemented
   by non-polymorphic records only; this means that the extensible "_ext" versions
   of type names must be reduced to qualifier names only. The used Syntax.parse_typ 
   handling the identification does that already. *)
 
fun is_subclass (ctxt) s t = is_subclass0(#docclass_tab(get_data ctxt)) s t
fun is_subclass_global thy s t = is_subclass0(#docclass_tab(get_data_global thy)) s t

fun type_name2doc_class_name thy str =  (*  Long_Name.qualifier *) str

fun typ_to_cid (Type(s,[@{typ "unit"}])) = Long_Name.qualifier s
   |typ_to_cid (Type(_,[T])) = typ_to_cid T
   |typ_to_cid _ = error("type is not an ontological type.")

fun name2doc_class_name thy str =
         case Syntax.parse_typ (Proof_Context.init_global thy) str of
                 Type(tyn, _)  => type_name2doc_class_name thy tyn
                | _ => error "illegal format for doc-class-name."
         handle ERROR _ => ""

fun name2doc_class_name_local ctxt str =
         (case Syntax.parse_typ ctxt str of
                 Type(tyn, _)  => type_name2doc_class_name ctxt tyn
                | _ => error "illegal format for doc-class-name.")
         handle ERROR _ => ""



fun is_defined_cid_global cid thy = let val t = #docclass_tab(get_data_global thy)
                                    in  cid=default_cid orelse 
                                        Symtab.defined t (name2doc_class_name thy cid) 
                                    end

fun is_defined_cid_global' cid_long thy = let val t = #docclass_tab(get_data_global thy)
                                    in  cid_long=default_cid orelse  Symtab.defined t cid_long end



fun is_defined_cid_local cid ctxt  = let val t = #docclass_tab(get_data ctxt)
                                     in  cid=default_cid orelse 
                                         Symtab.defined t (name2doc_class_name_local ctxt cid) 
                                     end

fun is_defined_cid_local' cid_long ctxt  = let val t = #docclass_tab(get_data ctxt)
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

fun get_class_invariant cid_long thy =
    let val  _ = if is_defined_cid_global' cid_long thy then () 
                 else error("undefined class id : " ^cid_long)
        val {docclass_inv_tab, ...} =  get_data_global thy
    in  case Symtab.lookup  docclass_inv_tab cid_long of 
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
        val _ = case term of
                  Const(_ ,Type(@{type_name "rexp"},[_])) => ()
                 | _ => error("current restriction: only atoms allowed here!") 
    in  term end


fun define_doc_class_global (params', binding) parent fields rexp reject_Atoms thy  = 
    let val nn = Context.theory_name thy (* in case that we need the thy-name to identify
                                            the space where it is ... *)
        val cid = (Binding.name_of binding)
        val pos = (Binding.pos_of binding)
    
        val _   = if is_defined_cid_global cid thy
                  then error("redefinition of document class")
                  else ()
    
        val _   = case parent of  (* the doc_class may be root, but must refer
                                     to another doc_class and not just an 
                                     arbitrary type *)
                      NONE => ()
                  |   SOME(_,cid_parent) => 
                               if not (is_defined_cid_global cid_parent thy)
                               then error("document class undefined : " ^ cid_parent)
                               else ()
        val cid_long = name2doc_class_name thy cid
        val id = serial ();
        val _ = Position.report pos (docclass_markup true cid id pos);
    
        val rejectS = map (Syntax.read_term_global thy) reject_Atoms;
        val _ = map (check_reject_atom cid_long)  rejectS; 
        val reg_exps = map (Syntax.read_term_global thy) rexp;
        val _ = map check_regexps reg_exps
        val _ = if not(null rejectS) andalso (null reg_exps) 
                then  error ("reject clause requires accept clause ! ") else ();
        val info = {params=params', 
                    name = binding, 
                    thy_name = nn, 
                    id = id, (* for pide --- really fresh or better reconstruct 
                                from prior record definition ? For the moment: own
                                generation of serials ... *)
                    inherits_from = parent,
                    attribute_decl = fields , 
                    rejectS = rejectS,
                    rex = reg_exps }
    
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
                                       val _ = writeln("Anonymous doc-ref declared: " ^ str)
                                   in  {tab=Symtab.update(str,NONE)tab,maxano= maxano+1} end
    in  map_data_global (upd_docobj_tab declare) (thy)
    end

fun declare_anoobject_local ctxt cid = 
    let fun declare {tab,maxano} = let val str = cid^":"^Int.toString(maxano+1)
                                           val _ = writeln("Anonymous doc-ref declared: " ^str)
                                       in  {tab=Symtab.update(str,NONE)tab, maxano=maxano+1} end
    in map_data (upd_docobj_tab declare) (ctxt) 
    end


fun get_object_global oid thy  = let val {tab,...} = #docobj_tab(get_data_global thy)
                                 in  case Symtab.lookup tab oid of 
                                       NONE => error("undefined reference: "^oid)
                                      |SOME(bbb) => bbb
                                 end

fun get_object_local oid ctxt  = let val {tab,...} = #docobj_tab(get_data ctxt)
                                 in  case Symtab.lookup tab oid of 
                                       NONE => error("undefined reference: "^oid)
                                      |SOME(bbb) => bbb
                                 end

fun get_doc_class_global cid thy = 
    if cid = default_cid then error("default doc class acces") (* TODO *)
    else let val t = #docclass_tab(get_data_global thy)
         in  (Symtab.lookup t cid) end
    

fun get_doc_class_local cid ctxt = 
    if cid = default_cid then error("default doc class acces") (* TODO *)
    else let val t = #docclass_tab(get_data ctxt)
         in  (Symtab.lookup t cid) end


fun is_defined_cid_local cid ctxt  = let val t = #docclass_tab(get_data ctxt)
                                     in  cid=default_cid orelse 
                                         Symtab.defined t (name2doc_class_name_local ctxt cid) 
                                     end


fun get_attributes_local cid ctxt =
    if cid = default_cid then []
    else let val t = #docclass_tab(get_data ctxt)
             val cid_long = name2doc_class_name_local ctxt cid
         in  case Symtab.lookup t cid_long of
               NONE => error("undefined doc class id :"^cid)
             | SOME ({inherits_from=NONE,
                       attribute_decl = X, ...}) => [(cid_long,X)]
             | SOME ({inherits_from=SOME(_,father),
                       attribute_decl = X, ...}) => get_attributes_local father ctxt @ [(cid_long,X)]
         end

fun get_attributes cid thy = get_attributes_local cid (Proof_Context.init_global thy)

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
fun update_value_global oid upd thy  = 
          case get_object_global oid thy of
               SOME{pos,thy_name,value,id,cid} => 
                   let val tab' = Symtab.update(oid,SOME{pos=pos,thy_name=thy_name,
                                                         value=upd value,id=id, cid=cid})
                   in   map_data_global (upd_docobj_tab(fn{tab,maxano}=>{tab=tab' tab,maxano=maxano})) thy end
             | NONE => error("undefined doc object: "^oid)  


val ISA_prefix = "Isa_DOF.ISA_"  (* ISA's must be declared in Isa_DOF.thy  !!! *)

fun get_isa_global isa thy  =  
            case Symtab.lookup (#ISA_transformer_tab(get_data_global thy)) (ISA_prefix^isa) of 
                 NONE      => error("undefined inner syntax antiquotation: "^isa)
               | SOME(bbb) => bbb
                               

fun get_isa_local isa ctxt  = case Symtab.lookup (#ISA_transformer_tab(get_data ctxt)) (ISA_prefix^isa) of 
                                       NONE => error("undefined inner syntax antiquotation: "^isa)
                                      |SOME(bbb) => bbb

fun update_isa_local (isa, trans) ctxt  = 
    map_data (upd_ISA_transformers(Symtab.update(ISA_prefix^isa,trans))) ctxt

fun update_isa_global (isa, trans) thy  = 
    map_data_global (upd_ISA_transformers(Symtab.update(ISA_prefix^isa,trans))) thy


fun transduce_term_global (term,pos) thy = 
    (* pre: term should be fully typed in order to allow type-relqted term-transformations *)
    let val tab = #ISA_transformer_tab(get_data_global thy)
        fun T(Const(s,ty) $ t) = if String.isPrefix ISA_prefix s
                                 then case Symtab.lookup tab s of
                                        NONE => error("undefined inner syntax antiquotation: "^s)
                                      | SOME(trans) => case trans thy (t,ty,pos) of 
                                                         NONE => Const(s,ty) $ t
                                                         (* checking isa, may raise error though. *)        
                                                       | SOME t => Const(s,ty) $ t
                                                         (* transforming isa *)
                                 else (Const(s,ty) $ (T t))
          |T(t1 $ t2) = T(t1) $ T(t2)
          |T(Abs(s,ty,t)) = Abs(s,ty,T t)
          |T t = t
    in   T term end


fun writeln_classrefs ctxt = let  val tab = #docclass_tab(get_data ctxt)
                             in   writeln (String.concatWith "," (Symtab.keys tab)) end


fun writeln_docrefs ctxt = let  val {tab,...} = #docobj_tab(get_data ctxt)
                           in   writeln (String.concatWith "," (Symtab.keys tab)) end

fun print_doc_items b ctxt = 
    let val {docobj_tab={tab = x, ...},...}= get_data ctxt;
        val _ = writeln "=====================================";    
        fun print_item (n, SOME({cid,id,pos,thy_name,value})) =
                 (writeln ("docitem: "^n);
                  writeln ("    type:    "^cid);
                  writeln ("    origine: "^thy_name);
                  writeln ("    value:   "^(Syntax.string_of_term ctxt value))
                 )
          | print_item (n, NONE) = 
                 (writeln ("forward reference for docitem: "^n));
    in  map print_item (Symtab.dest x); 
        writeln "=====================================\n\n\n" end;

fun print_doc_classes b ctxt = 
    let val {docobj_tab={tab = x, ...},docclass_tab, ...} = get_data ctxt;
        val _ = writeln "=====================================";    
        fun print_attr (n, ty, NONE) = (Binding.print n)
          | print_attr (n, ty, SOME t) = (Binding.print n^"("^Syntax.string_of_term ctxt t^")")
        fun print_class (n, {attribute_decl, id, inherits_from, name, params, thy_name, rejectS, rex}) =
           (case inherits_from of 
               NONE => writeln ("docclass: "^n)
             | SOME(_,nn) => writeln ("docclass: "^n^" = "^nn^" + ");
            writeln ("    name:    "^(Binding.print name));
            writeln ("    origin:  "^thy_name);
            writeln ("    attrs:   "^commas (map print_attr attribute_decl))
           );
    in  map print_class (Symtab.dest docclass_tab); 
        writeln "=====================================\n\n\n" 
    end;

fun check_doc_global (strict_checking : bool) ctxt = 
    let val {docobj_tab={tab = x, ...}, monitor_tab, ...} = get_data ctxt;
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
  Outer_Syntax.command @{command_keyword print_doc_classes}
    "print document classes"
    (Parse.opt_bang >> (fn b =>
      Toplevel.keep (print_doc_classes b o Toplevel.context_of)));

val _ =
  Outer_Syntax.command @{command_keyword print_doc_items}
    "print document items"
    (Parse.opt_bang >> (fn b =>
      Toplevel.keep (print_doc_items b o Toplevel.context_of)));

val _ =
  Outer_Syntax.command @{command_keyword check_doc_global}
    "check global document consistency"
    (Parse.opt_bang >> (fn b =>
      Toplevel.keep (check_doc_global b o Toplevel.context_of)));


fun toStringLaTeXNewKeyCommand env long_name =
    "\\expandafter\\newkeycommand\\csname"^" "^"isaDof."^env^"."^long_name^"\\endcsname%\n" 

fun toStringMetaArgs true attr_long_names = 
       enclose "[" "][1]" (commas ("label=,type=%\n" :: attr_long_names))
   |toStringMetaArgs false attr_long_names = 
       enclose "[" "][1]" (commas attr_long_names) 

fun toStringDocItemBody env =
    enclose "{%\n\\isamarkupfalse\\isamarkup" 
            "{#1}\\label{\\commandkey{label}}\\isamarkuptrue%\n}\n"
            env
            
fun toStringDocItemCommand env long_name attr_long_names = 
    toStringLaTeXNewKeyCommand env long_name ^
    toStringMetaArgs true attr_long_names ^
    toStringDocItemBody env ^"\n"

fun toStringDocItemLabel long_name attr_long_names = 
    toStringLaTeXNewKeyCommand "Label" long_name ^
    toStringMetaArgs false attr_long_names ^
    "{%\n\\autoref{#1}\n}\n"

fun toStringDocItemRef long_name label attr_long_namesNvalues = 
    "\\isaDof.Label." ^ long_name ^
    enclose "[" "]" (commas attr_long_namesNvalues) ^
    enclose "{" "}" label

fun write_file thy filename content =
    let 
       val filename = Path.explode filename
       val master_dir = Resources.master_directory thy
       val abs_filename = if (Path.is_absolute filename) 
                          then filename 
                          else Path.append master_dir filename
    in
      File.write (abs_filename) content
      handle (IO.Io{name=name,...}) 
             => warning ("Could not write \""^(name)^"\".")
    end

fun write_ontology_latex_sty_template thy = 
    let 
        (* 
        val raw_name = Context.theory_long_name thy

        val curr_thy_name = if String.isPrefix "Draft." raw_name 
                   then String.substring(raw_name, 6, (String.size raw_name)-6)
                   else error "Not in ontology definition context"
        *)
        val curr_thy_name = Context.theory_name thy
        val {docobj_tab={tab = x, ...},docclass_tab,...}= get_data_global thy;
        fun  write_attr (n, ty, _) = YXML.content_of(Binding.print n)^ "=\n"

        fun write_class (n, {attribute_decl,id,inherits_from,name,params,thy_name,rex,rejectS}) =
            if curr_thy_name = thy_name then
                   toStringDocItemCommand "section" n (map write_attr attribute_decl) ^
                   toStringDocItemCommand "text" n (map write_attr attribute_decl) ^
                   toStringDocItemLabel n (map write_attr attribute_decl)
                   (* or parameterising with "env" ? ? ?*)
            else ""
        val content = String.concat(map write_class (Symtab.dest docclass_tab))
        (* val _ = writeln content  -- for interactive testing only, breaks LaTeX compilation *) 
    in  write_file thy ("Isa-DOF."^curr_thy_name^".template.sty") content
    end;


val _ =
  Outer_Syntax.command @{command_keyword gen_sty_template}
    "generate a template LaTeX style file for this ontology"
    (Parse.opt_bang >> (fn b =>
      Toplevel.keep (write_ontology_latex_sty_template o Toplevel.theory_of)));

val (strict_monitor_checking, strict_monitor_checking_setup) 
     = Attrib.config_bool @{binding strict_monitor_checking} (K false);

end (* struct *)

\<close>

setup\<open>DOF_core.strict_monitor_checking_setup\<close>


section\<open> Syntax for Inner Syntax Antiquotations (ISA) \<close>

subsection\<open> Syntax \<close> 

typedecl "doc_class"
typedecl "typ"
typedecl "term"
typedecl "thm"
typedecl "file"
typedecl "thy"
 
-- \<open> and others in the future : file, http, thy, ... \<close> 

consts ISA_typ          :: "string \<Rightarrow> typ"               ("@{typ _}")
consts ISA_term         :: "string \<Rightarrow> term"              ("@{term _}")
consts ISA_thm          :: "string \<Rightarrow> thm"               ("@{thm _}")
consts ISA_file         :: "string \<Rightarrow> file"              ("@{file _}")
consts ISA_thy          :: "string \<Rightarrow> thy"               ("@{thy _}")
consts ISA_docitem      :: "string \<Rightarrow> 'a"                ("@{docitem _}")
consts ISA_docitem_attr :: "string \<Rightarrow> string \<Rightarrow> 'a"      ("@{docitemattr (_) :: (_)}")

(* tests *)  
term "@{typ  ''int => int''}"  
term "@{term ''Bound 0''}"  
term "@{thm  ''refl''}"  
term "@{docitem  ''<doc_ref>''}"
ML\<open>   @{term "@{docitem  ''<doc_ref>''}"}\<close>


subsection\<open> Semantics \<close>

ML\<open>
structure ISA_core = 
struct

fun err msg pos = error (msg ^ Position.here pos);

fun check_path check_file ctxt dir (name, pos) =
  let
    val _ = Context_Position.report ctxt pos Markup.language_path;

    val path = Path.append dir (Path.explode name) handle ERROR msg => err msg pos;
    val _ = Path.expand path handle ERROR msg => err msg pos;
    val _ = Context_Position.report ctxt pos (Markup.path (Path.smart_implode path));
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


fun ML_isa_check_typ thy (term, _, pos) =
  let fun check thy (name, _) = let val ctxt = (Proof_Context.init_global thy)
                                in (Syntax.check_typ ctxt o Syntax.parse_typ ctxt) name end
  in  ML_isa_check_generic check thy (term, pos) end 


fun ML_isa_check_term thy (term, _, pos) =
  let fun check thy (name, _) = let val ctxt = (Proof_Context.init_global thy)
                                in (Syntax.check_term ctxt o Syntax.parse_term ctxt) name end 
  in  ML_isa_check_generic check thy (term, pos) end 


fun ML_isa_check_thm thy (term, _, pos) =
  (* this works for long-names only *)
  let fun check thy (name, _) = case Proof_Context.lookup_fact (Proof_Context.init_global thy) name of
                                  NONE => err ("No Theorem:" ^name) pos
                                | SOME X => X
  in   ML_isa_check_generic check thy (term, pos) end 


fun ML_isa_check_file thy (term, _, pos) =
  let fun check thy (name, pos) = check_path (SOME File.check_file) 
                                             (Proof_Context.init_global thy) 
                                             (Path.current) 
                                             (name, pos);
  in  ML_isa_check_generic check thy (term, pos) end;


fun ML_isa_id thy (term,pos) = SOME term


fun ML_isa_check_docitem thy (term, req_ty, pos) =
  let fun check thy (name, _) = 
           if DOF_core.is_declared_oid_global name thy 
           then case DOF_core.get_object_global name thy of
                    NONE => warning("oid declared, but not yet defined --- "^
                                    " type-check incomplete")
                 |  SOME {pos=pos_decl,cid,id,...} => 
                         let val ctxt = (Proof_Context.init_global thy)
                             val req_class = case req_ty of 
                                         Type("fun",[_,T]) =>  DOF_core.typ_to_cid T
                                       | _ => error("can not infer type for: "^ name)
                         in if cid <> DOF_core.default_cid 
                               andalso not(DOF_core.is_subclass ctxt cid req_class)
                            then error("reference ontologically inconsistent")
                            else ()
                         end
           else err ("faulty reference to docitem: "^name) pos
  in  ML_isa_check_generic check thy (term, pos) end 

(* utilities *)

fun property_list_dest X = map HOLogic.dest_string 
                                (map (fn Const ("Isa_DOF.ISA_term", _) $ s => s )  
                                     (HOLogic.dest_list X))

end; (* struct *)
                                                            
\<close>
subsection\<open> Isar - Setup\<close>

setup\<open>DOF_core.update_isa_global("typ"    ,ISA_core.ML_isa_check_typ) \<close>     
setup\<open>DOF_core.update_isa_global("term"   ,ISA_core.ML_isa_check_term) \<close>     
setup\<open>DOF_core.update_isa_global("thm"    ,ISA_core.ML_isa_check_thm) \<close>     
setup\<open>DOF_core.update_isa_global("file"   ,ISA_core.ML_isa_check_file) \<close>     
setup\<open>DOF_core.update_isa_global("docitem",ISA_core.ML_isa_check_docitem)\<close>     


section\<open> Syntax for Annotated Documentation Commands (the '' View'' Part I) \<close>
ML\<open>
structure ODL_Command_Parser = 
struct

type meta_args_t = (((string * Position.T) *
                     (string * Position.T) option)
                    * ((string * Position.T) * string) list)

fun meta_args_2_string thy ((((lab, _), cid_opt), attr_list) : meta_args_t) = 
    (* for the moment naive, i.e. without textual normalization of 
       attribute names and adapted term printing *)
    let val l   = "label = "^ (enclose "{" "}" lab)
        val cid_long = case cid_opt of
                                NONE => DOF_core.default_cid
                              | SOME(cid,_) => DOF_core.name2doc_class_name thy cid
        val cid_txt  = "type = " ^ (enclose "{" "}" cid_long);

        (* TODO: temp. hack *)
        fun unquote_string s = if String.isPrefix "''" s then
                                  String.substring(s,2,(String.size s)-4)
                               else s
        fun markup2string s =  unquote_string (String.concat (List.filter (fn c => c <> Symbol.DEL) 
                                             (Symbol.explode (YXML.content_of s)))) 

        fun toLong n =  #long_name(the(DOF_core.get_attribute_info cid_long (markup2string n) thy))
        fun str ((lhs,_),rhs) = (toLong lhs)^" = "^(enclose "{" "}" (markup2string rhs))  
                                (* no normalization on lhs (could be long-name)
                                   no paraphrasing on rhs (could be fully paranthesized
                                   pretty-printed formula in LaTeX notation ... *)
    in  
      enclose "[" "]" (String.concat [ cid_txt, ", args={", (commas ([cid_txt,l] @ (map str  attr_list ))), "}"]) 
      end

val semi = Scan.option (Parse.$$$ ";");
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



fun cid_2_cidType cid_long thy =
    if cid_long = DOF_core.default_cid then @{typ "unit"}
    else let val t = #docclass_tab(DOF_core.get_data_global thy)
             fun ty_name cid = cid^"."^  Long_Name.base_name cid^"_ext"
             fun fathers cid_long = case Symtab.lookup t cid_long of
                       NONE => error("undefined doc class id :"^cid_long)
                     | SOME ({inherits_from=NONE, ...}) => [cid_long]
                     | SOME ({inherits_from=SOME(_,father), ...}) => 
                           cid_long :: (fathers father) 
         in fold (fn x => fn y => Type(ty_name x,[y])) (fathers cid_long) @{typ "unit"}  
         end

fun base_default_term thy cid_long = Const(@{const_name "undefined"},cid_2_cidType thy cid_long) 

fun check_classref is_monitor (SOME(cid,pos')) thy = 
          let val _ = if not (DOF_core.is_defined_cid_global cid thy) 
                      then error("document class undefined") else ()
              val cid_long = DOF_core.name2doc_class_name thy cid 
              val {id, name=bind_target,rex,...} = the(DOF_core.get_doc_class_global cid_long thy)
              val _ = if is_monitor andalso (null rex orelse cid_long= DOF_core.default_cid ) 
                      then error("should be monitor class!")
                      else ()
              val markup = docclass_markup false cid id (Binding.pos_of bind_target);
              val ctxt = Context.Theory thy
              val _ = Context_Position.report_generic ctxt pos' markup;
          in  cid_long 
          end
   | check_classref _ NONE _ = DOF_core.default_cid 


fun generalize_typ n = Term.map_type_tfree (fn (str,sort)=> Term.TVar((str,n),sort));
fun infer_type thy term = hd (Type_Infer_Context.infer_types (Proof_Context.init_global thy) [term])


fun calc_update_term thy cid_long (S:(string * Position.T * string * term)list) term = 
    let val cid_ty = cid_2_cidType cid_long thy 
        val generalize_term =  Term.map_types (generalize_typ 0)
        fun toString t = Syntax.string_of_term (Proof_Context.init_global thy) t  
        fun instantiate_term S t = Term_Subst.map_types_same (Term_Subst.instantiateT S) (t)
        fun read_assn (lhs, pos:Position.T, opr, rhs) term =
            let val info_opt = DOF_core.get_attribute_info cid_long 
                                       (Long_Name.base_name lhs) thy
                val (ln,lnt,lnu,lnut) = case info_opt of 
                                           NONE => error ("unknown attribute >" 
                                                          ^((Long_Name.base_name lhs))
                                                          ^"< in class: "^cid_long)
                                        |  SOME{long_name, typ, ...} => (long_name, typ, 
                                                                         long_name ^"_update",
                                                                         (typ --> typ) 
                                                                          --> cid_ty --> cid_ty)
                val tyenv = Sign.typ_match thy  ((generalize_typ 0)(type_of rhs), lnt) (Vartab.empty)
                            handle Type.TYPE_MATCH => error ("type of attribute: " ^ ln 
                                                             ^ " does not fit to term: " 
                                                             ^ toString rhs);
                val tyenv' = (map (fn (s,(t,u)) => ((s,t),u)) (Vartab.dest tyenv))
                val _ = if Long_Name.base_name lhs = lhs orelse ln = lhs then ()
                        else error("illegal notation for attribute of "^cid_long)
                fun join (ttt as @{typ "int"}) 
                         = Const (@{const_name "Groups.plus"}, ttt --> ttt --> ttt)
                   |join (ttt as @{typ "string"}) 
                         = Const (@{const_name "List.append"}, ttt --> ttt --> ttt)
                   |join (ttt as Type(@{type_name "set"},_)) 
                         = Const (@{const_name "Lattices.sup"}, ttt --> ttt --> ttt)
                   |join (ttt as Type(@{type_name "list"},_)) 
                         = Const (@{const_name "List.append"}, ttt --> ttt --> ttt)
                   |join _ = error("implicit fusion operation not defined for attribute: "^ lhs)
                 (* could be extended to bool, map, multisets, ... *)
                val rhs' = instantiate_term tyenv' (generalize_term rhs)
                val rhs'' = DOF_core.transduce_term_global (rhs',pos) thy                 
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
          fun markup2string x = XML.content_of (YXML.parse_body x)
          fun conv_attrs (((lhs, pos), opn), rhs) = (markup2string lhs,pos,opn, 
                                                     Syntax.read_term_global thy rhs)
          val trace_attr = [((("trace", @{here}), "+="), "[("^cid_long^", ''"^oid^"'')]")]
          val assns' = map conv_attrs trace_attr
          fun cid_of oid = #cid(the(DOF_core.get_object_global oid thy))
          fun def_trans oid = #1 o (calc_update_term thy (cid_of oid) assns')
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
          fun update_trace mon_oid = DOF_core.update_value_global mon_oid (def_trans mon_oid)
          val update_automatons = DOF_core.upd_monitor_tabs(fold update_info delta_autoS)
      in  thy |> (* update traces of all enabled monitors *)
                 fold (update_trace) (enabled_monitors)
              |> (* check class invariants of enabled monitors *)
                 (fn thy => (class_inv_checks (Context.Theory thy); thy))
              |> (* update the automata of enabled monitors *)
                 DOF_core.map_data_global(update_automatons)
      end


fun create_and_check_docitem is_monitor oid pos cid_pos doc_attrs thy = 
      let val id = serial ();
          val _ = Position.report pos (docref_markup true oid id pos);
          (* creates a markup label for this position and reports it to the PIDE framework;
           this label is used as jump-target for point-and-click feature. *)
          val cid_long = check_classref is_monitor cid_pos thy
          val defaults_init = base_default_term  cid_long thy     
          fun conv (na, _(*ty*), term) = (Binding.name_of na, Binding.pos_of na, "=", term);
          val S = map conv (DOF_core.get_attribute_defaults cid_long thy);
          val (defaults, _(*ty*), _) = calc_update_term thy cid_long S defaults_init;
          fun markup2string x = XML.content_of (YXML.parse_body x)
          fun conv_attrs ((lhs, pos), rhs) = (markup2string lhs,pos,"=", Syntax.read_term_global thy rhs)
          val assns' = map conv_attrs doc_attrs
          val (value_term, _(*ty*), _) = calc_update_term thy cid_long assns' defaults 
          val check_inv =   (DOF_core.get_class_invariant cid_long thy oid {is_monitor=is_monitor}) 
                            o Context.Theory 
      in  thy |> DOF_core.define_object_global (oid, {pos      = pos, 
                                                      thy_name = Context.theory_name thy,
                                                      value    = value_term,
                                                      id       = id,   
                                                      cid      = cid_long})
              |> register_oid_cid_in_open_monitors oid pos cid_long
              |> (fn thy => (check_inv thy; thy))
      end



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
                val cid_long = check_classref false cid_pos thy
                val _ = if cid_long = DOF_core.default_cid  orelse cid = cid_long 
                        then () 
                        else error("incompatible classes:"^cid^":"^cid_long)
                fun markup2string x = XML.content_of (YXML.parse_body x)
         
                fun conv_attrs (((lhs, pos), opn), rhs) = (markup2string lhs,pos,opn, 
                                                           Syntax.read_term_global thy rhs)
                val assns' = map conv_attrs doc_attrs
                val def_trans = #1 o (calc_update_term thy cid_long assns')
                fun check_inv thy =((DOF_core.get_class_invariant cid_long thy oid {is_monitor=false} 
                                     o Context.Theory ) thy ; thy)
            in     
                thy |> DOF_core.update_value_global oid (def_trans)
                    |> check_inv
            end


fun gen_enriched_document_command transform 
                               markdown  
                              (((((oid,pos),cid_pos), doc_attrs) : meta_args_t,
                                  xstring_opt:(xstring * Position.T) option),
                                  toks:Input.source) 
                              : theory -> theory =
  let
       (* as side-effect, generates markup *)
       fun check_text thy = (Thy_Output.output_text(Toplevel.theory_toplevel thy) markdown toks; thy)
       (* generating the level-attribute syntax *)
  in   
       (create_and_check_docitem false oid pos cid_pos (transform doc_attrs) #> check_text) 
       (* Thanks Frederic Tuong! ! ! *)
  end;

fun enriched_document_command level =
   let fun transform doc_attrs = case level of 
                  NONE => doc_attrs 
                | SOME(NONE) => (("level",@{here}),"None")::doc_attrs
                | SOME(SOME x) => (("level",@{here}),"Some("^ Int.toString x ^"::int)")::doc_attrs
   in  gen_enriched_document_command transform end; 

fun enriched_formal_statement_command (tag:string) =
   let fun transform doc_attrs = (("tag",@{here}),"''"^tag^"''") :: 
                                 (("properties",@{here}),"([]::thm list)")::doc_attrs
   in  gen_enriched_document_command transform end; 



fun open_monitor_command  ((((oid,pos),cid_pos), doc_attrs) : meta_args_t) =
    let fun o_m_c oid pos cid_pos doc_attrs thy = create_and_check_docitem 
                                                         true oid pos cid_pos doc_attrs thy
        fun compute_enabled_set cid thy = 
                     case DOF_core.get_doc_class_global cid thy of
                       SOME X => let val ralph = RegExpInterface.alphabet (#rejectS X)
                                     val alph = RegExpInterface.ext_alphabet ralph (#rex X)
                                 in  (alph, map (RegExpInterface.rexp_term2da alph)(#rex X)) end 
                     | NONE => error("Internal error: class id undefined. ");
        
        fun create_monitor_entry thy =  
            let val {cid, ...} = the(DOF_core.get_object_global oid thy)
                val (S, aS) = compute_enabled_set cid thy
                val info = {accepted_cids = S, rejected_cids = [], automatas  = aS }
            in  DOF_core.map_data_global(DOF_core.upd_monitor_tabs(Symtab.update(oid, info )))(thy)
            end
    in
        o_m_c oid pos cid_pos doc_attrs  #> create_monitor_entry  
    end;


fun close_monitor_command (args as (((oid:string,pos),cid_pos),
                                    doc_attrs: (((string*Position.T)*string)*string)list)) thy = 
    let val {monitor_tab,...} = DOF_core.get_data_global thy
        fun check_if_final aS = let val i = find_index (not o RegExpInterface.final) aS
                                in  if i >= 0 
                                    then error("monitor number "^Int.toString i^" not in final state.")
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
    in  thy |> update_instance_command args
            |> (fn thy => (check_inv thy; thy))
            |> delete_monitor_entry
    end 

(* *********************************************************************** *)
(* Textual Command Support                                                 *)
(* *********************************************************************** *)

(* {markdown = true} sets the parsing process such that in the text-core markdown elements are
   accepted. *)

val _ =
  Outer_Syntax.command ("Definition*", @{here}) "Textual Definition"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> (Toplevel.theory o (enriched_formal_statement_command "definition" {markdown = true} )));

val _ =
  Outer_Syntax.command ("Lemma*", @{here}) "Textual Lemma Outline"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> (Toplevel.theory o (enriched_formal_statement_command "lemma" {markdown = true} )));

val _ =
  Outer_Syntax.command ("Theorem*", @{here}) "Textual Theorem Outline"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> (Toplevel.theory o (enriched_formal_statement_command "theorem" {markdown = true} )));

val _ =
  Outer_Syntax.command ("Conjecture*", @{here}) "Textual Theorem Outline"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> (Toplevel.theory o (enriched_formal_statement_command "conjecture" {markdown = true} )));


val _ =
  Outer_Syntax.command ("title*", @{here}) "section heading"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> (Toplevel.theory o (enriched_document_command NONE {markdown = false} ))) ;

val _ =
  Outer_Syntax.command ("subtitle*", @{here}) "section heading"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> (Toplevel.theory o (enriched_document_command NONE {markdown = false} )));

val _ =
  Outer_Syntax.command ("chapter*", @{here}) "section heading"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> (Toplevel.theory o (enriched_document_command (SOME(SOME 0)) {markdown = false} )));

val _ =
  Outer_Syntax.command ("section*", @{here}) "section heading"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> (Toplevel.theory o (enriched_document_command (SOME(SOME 1)) {markdown = false} )));


val _ =
  Outer_Syntax.command ("subsection*", @{here}) "subsection heading"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> (Toplevel.theory o (enriched_document_command (SOME(SOME 2)) {markdown = false} )));

val _ =
  Outer_Syntax.command ("subsubsection*", @{here}) "subsubsection heading"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> (Toplevel.theory o (enriched_document_command (SOME(SOME 3)) {markdown = false} )));

val _ =
  Outer_Syntax.command ("paragraph*", @{here}) "paragraph heading"
    (attributes --  Parse.opt_target -- Parse.document_source --| semi
      >> (Toplevel.theory o (enriched_document_command (SOME(SOME 4)) {markdown = false} )));

val _ =
  Outer_Syntax.command ("subparagraph*", @{here}) "subparagraph heading"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> (Toplevel.theory o (enriched_document_command (SOME(SOME 5)) {markdown = false} )));

val _ =
  Outer_Syntax.command ("figure*", @{here}) "figure"
    (attributes --  Parse.opt_target -- Parse.document_source --| semi
      >> (Toplevel.theory o (enriched_document_command NONE {markdown = false} )));

val _ =
  Outer_Syntax.command ("side_by_side_figure*", @{here}) "multiple figures"
    (attributes --  Parse.opt_target -- Parse.document_source --| semi
      >> (Toplevel.theory o (enriched_document_command NONE {markdown = false} )));


val _ =
  Outer_Syntax.command ("text*", @{here}) "formal comment (primary style)"
    (attributes -- Parse.opt_target -- Parse.document_source 
      >> (Toplevel.theory o (enriched_document_command NONE {markdown = true} )));

val _ =
  Outer_Syntax.command @{command_keyword "declare_reference*"} 
                       "declare document reference"
                       (attributes >> (fn (((oid,pos),cid),doc_attrs) =>  
                                      (Toplevel.theory (DOF_core.declare_object_global oid))));

val _ =
  Outer_Syntax.command @{command_keyword "open_monitor*"} 
                       "open a document reference monitor"
                       (attributes >> (Toplevel.theory o open_monitor_command));

val _ =
  Outer_Syntax.command @{command_keyword "close_monitor*"} 
                       "close a document reference monitor"
                       (attributes_upd >> (Toplevel.theory o close_monitor_command)); 


val _ =
  Outer_Syntax.command @{command_keyword "update_instance*"} 
                       "update meta-attributes of an instance of a document class"
                        (attributes_upd >> (Toplevel.theory o update_instance_command)); 


fun assert_cmd'((((((oid,pos),cid_pos),doc_attrs),some_name:string option),modes : string list),
                prop) =
    let fun markup2string x = XML.content_of (YXML.parse_body x)
        fun parse_convert thy = (let val ctxt = (Proof_Context.init_global thy)
                                     val term = Syntax.parse_term ctxt prop
                                     val str = Sledgehammer_Util.hackish_string_of_term ctxt term
                                     fun hpp x = if x = #"\\" then "\\\\" else String.implode [x] 
                                     val str' = map hpp (String.explode str)
                                     val str'' = String.concatWith " " str'
                                 in str''
                                 end)
        val _ = writeln ("XXX" ^ markup2string prop)
        fun conv_attrs thy = (("property",pos),"[@{term ''"^markup2string prop ^"''}]")::doc_attrs  
        (* fun conv_attrs thy = (("property",pos),"[@{term ''"^parse_convert thy ^"''}]")::doc_attrs *)
        fun conv_attrs' thy = map (fn ((lhs,pos),rhs) => (((lhs,pos),"+="),rhs)) (conv_attrs thy)
        fun mks thy = case DOF_core.get_object_global oid thy of
                   SOME _ => (writeln "SOME"; update_instance_command (((oid,pos),cid_pos),conv_attrs' thy) thy)
                 | NONE   => (writeln "NONE"; create_and_check_docitem false oid pos cid_pos (conv_attrs thy) thy)
        val check = (assert_cmd some_name modes prop) o Proof_Context.init_global
    in 
        (* Toplevel.keep (check o Toplevel.context_of) *)
        Toplevel.theory (fn thy => (check thy; 
                                    (* writeln ("YYY" ^  parse_convert thy); *)
                                    mks thy))
    end

val _ =
  Outer_Syntax.command @{command_keyword "assert*"} 
                       "evaluate and print term"
                       (attributes -- opt_evaluator -- opt_modes  -- Parse.term  >> assert_cmd'); 

(* the following 2 lines set parser and converter for LaTeX generation of meta-attributes. 
   Currently of *all* commands, no distinction between text* and text command. 
   This code depends on a MODIFIED Isabelle2017 version resulting fro; applying the files
   under Isabell_DOF/patches. 
 *)
val _ = Thy_Output.set_meta_args_parser 
                       (fn thy => (Scan.optional (attributes >> meta_args_2_string thy) "")) 

end (* struct *)

\<close>
  
ML \<open>
local (* dull and dangerous copy from Pure.thy given that these functions are not
         globally exported. *)

val long_keyword =
  Parse_Spec.includes >> K "" ||
  Parse_Spec.long_statement_keyword;

val long_statement =
  Scan.optional (Parse_Spec.opt_thm_name ":" --| Scan.ahead long_keyword) Binding.empty_atts --
  Scan.optional Parse_Spec.includes [] -- Parse_Spec.long_statement
    >> (fn ((binding, includes), (elems, concl)) => (true, binding, includes, elems, concl));

val short_statement =
  Parse_Spec.statement -- Parse_Spec.if_statement -- Parse.for_fixes
    >> (fn ((shows, assumes), fixes) =>
      (false, Binding.empty_atts, [], [Element.Fixes fixes, Element.Assumes assumes],
        Element.Shows shows));

fun theorem spec schematic descr  =
  Outer_Syntax.local_theory_to_proof' spec ("state " ^ descr)
    ((ODL_Command_Parser.attributes -- (long_statement || short_statement)) 
    >> (fn (_ (* skip *) ,(long, binding, includes, elems, concl)) =>
           ((if schematic then Specification.schematic_theorem_cmd 
                          else Specification.theorem_cmd )
             long Thm.theoremK NONE (K I) binding includes elems concl)));

in

(* Half - fake. activates original Isar commands, but skips meta-arguments for the moment. *)
val _ = theorem @{command_keyword "theorem*"}        false "theorem";
val _ = theorem @{command_keyword "lemma*"}          false "lemma";
val _ = theorem @{command_keyword "corrollary*"}     false "corollary";
val _ = theorem @{command_keyword "proposition*"}    false "proposition";
val _ = theorem @{command_keyword "schematic_goal*"} true  "schematic goal"; 

end\<close>  

 
section\<open> Syntax for Ontological Antiquotations (the '' View'' Part II) \<close>
  
ML\<open>
structure OntoLinkParser = 
struct

fun check_and_mark ctxt cid_decl (str:{strict_checking: bool}) pos name  =
  let
    val thy = Proof_Context.theory_of ctxt;
  in 
    if DOF_core.is_defined_oid_global name thy 
    then let val {pos=pos_decl,id,cid,...} = the(DOF_core.get_object_global name thy)
             val markup = docref_markup false name id pos_decl;
             val _ = Context_Position.report ctxt pos markup;
                     (* this sends a report for a ref application to the PIDE interface ... *) 
             val _ = if cid <> DOF_core.default_cid 
                        andalso not(DOF_core.is_subclass ctxt cid cid_decl)
                     then error("reference ontologically inconsistent")
                     else ()
         in  name end
    else if   DOF_core.is_declared_oid_global name thy 
         then (if #strict_checking str 
               then warning("declared but undefined document reference:"^name)
               else (); name)
         else error("undefined document reference:"^name)
  end


(* generic syntax for doc_class links. *) 

val defineN    = "define"
val uncheckedN = "unchecked" 

val docitem_modes = Scan.optional (Args.parens (Args.$$$ defineN || Args.$$$ uncheckedN) 
                                   >> (fn str => if str = defineN 
                                                 then {unchecked = false, define= true}  
                                                 else {unchecked = true,  define= false})) 
                                   {unchecked = false, define= false} (* default *);


fun docitem_antiquotation_generic enclose name cid_decl = 
    Thy_Output.antiquotation name (Scan.lift (docitem_modes -- Args.cartouche_input))
        (fn {context = ctxt, source = src:Token.src, state} =>
             fn ({unchecked = x, define= y}, source:Input.source) => 
                 (Thy_Output.output_text state {markdown=false} #>
                  check_and_mark ctxt                   
                                 cid_decl 
                                 ({strict_checking = not x})
                                 (Input.pos_of source) #>
                  enclose y) 
                 source)


fun docitem_antiquotation name cid_decl = 
    let fun open_par x = if x then "\\label{" 
                              else "\\autoref{"
        val close = "}"
    in  docitem_antiquotation_generic (fn y => enclose (open_par y) close) name cid_decl end


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


fun ML_antiquotation_docitem_value binding = 
    ML_Antiquotation.inline binding 
         (fn (ctxt, toks) => (Scan.lift (Args.cartouche_input) 
                              >> (fn inp => (ML_Syntax.atomic o ML_Syntax.print_term) 
                                            (check_and_mark_term ctxt (Input.source_content inp)))) 
                             (ctxt, toks))
                                         

(* Setup for general docrefs of the global DOF_core.default_cid - class ("text")*)
val _ = Theory.setup((docitem_antiquotation @{binding docref} DOF_core.default_cid) #>
                     (* deprecated syntax             ^^^^^^*)
                     (docitem_antiquotation @{binding docitem_ref} DOF_core.default_cid) #>
                     (* deprecated syntax             ^^^^^^^^^^*)
                     (docitem_antiquotation @{binding docitem} DOF_core.default_cid) #>

                      ML_antiquotation_docitem_value @{binding docitem_value})

end (* struct *)
\<close>



ML\<open> 
structure AttributeAccess = 
struct

fun symbex_attr_access0 ctxt proj_term term =
    (* term assumed to be ground type, (f term) not necessarily *)
    let val [subterm'] = Type_Infer_Context.infer_types ctxt [proj_term $ term]
        val ty = type_of (subterm')
        (* Debug :
        val _ = writeln ("calculate_attr_access raw term: " 
                         ^ Syntax.string_of_term ctxt subterm')
         *)
        val term' = (Const(@{const_name "HOL.eq"}, ty --> ty --> HOLogic.boolT) 
                              $ subterm' 
                              $ Free("_XXXXXXX", ty))
        val thm = simplify ctxt (Thm.assume(Thm.cterm_of ctxt (HOLogic.mk_Trueprop term')));
    in  case HOLogic.dest_Trueprop (Thm.concl_of thm) of
           Free("_XXXXXXX", @{typ "bool"}) => @{const "True"}
        |  @{const "HOL.Not"} $  Free("_XXXXXXX", @{typ "bool"}) =>  @{const "False"}
        |  Const(@{const_name "HOL.eq"},_) $ lhs $ Free("_XXXXXXX", _ )=> lhs 
        |  Const(@{const_name "HOL.eq"},_) $ Free("_XXXXXXX", _ ) $ rhs => rhs
        |  _ => error ("could not reduce attribute term: " ^
                       Syntax.string_of_term ctxt subterm')
    end

fun compute_attr_access ctxt attr oid pos pos' = (* template *)
    case DOF_core.get_value_global oid (Context.theory_of ctxt) of 
            SOME term => let val ctxt =  (Proof_Context.init_global (Context.theory_of ctxt))
                              val SOME{cid,pos=pos_decl,id,...} = DOF_core.get_object_local oid ctxt
                              val markup = docref_markup false oid id pos_decl;
                              val _ = Context_Position.report ctxt pos' markup;
                              val (* (long_cid, attr_b,ty) = *)
                                  {long_name, typ=ty,...} = 
                                       case DOF_core.get_attribute_info_local cid attr ctxt of
                                            SOME f => f
                                          | NONE => error("attribute undefined for reference: "
                                                          ^ oid ^ Position.here pos)
                              val proj_term = Const(long_name,dummyT --> ty) 
                          in  symbex_attr_access0 ctxt proj_term term end
           | NONE => error("identifier not a docitem reference" ^ Position.here pos)


fun compute_trace_ML ctxt oid pos pos' =
    (* grabs attribute, and converts its HOL-term into (textual) ML representation *)
    let val term = compute_attr_access ctxt "trace" oid pos pos'
        fun conv (Const(@{const_name "Pair"},_) $ Const(s,_) $ S) = (s, HOLogic.dest_string S)
    in  map conv (HOLogic.dest_list term) end

val parse_oid = Scan.lift(Parse.position Args.name) 
val parse_oid' = Term_Style.parse -- parse_oid
val parse_attribute_access = (parse_oid 
                              --| (Scan.lift @{keyword "::"}) 
                              -- Scan.lift (Parse.position Args.name))
                              : ((string *Position.T) * (string * Position.T)) context_parser 

val parse_attribute_access' = Term_Style.parse -- parse_attribute_access
                              : ((term -> term) *
                                 ((string * Position.T) * (string * Position.T))) context_parser

fun attr_2_ML ctxt ((attr:string,pos),(oid:string,pos')) = (ML_Syntax.atomic o ML_Syntax.print_term) 
                                                           (compute_attr_access ctxt attr oid pos pos') 

fun trace_attr_2_ML ctxt (oid:string,pos) =
    let val print_string_pair = ML_Syntax.print_pair  ML_Syntax.print_string ML_Syntax.print_string
        val toML = (ML_Syntax.atomic o (ML_Syntax.print_list print_string_pair))
    in  toML (compute_trace_ML ctxt oid @{here} pos) end

local
(* copied from "$ISABELLE_HOME/src/Pure/Thy/thy_output.ML" *)
fun basic_entities name scan pretty =
  Thy_Output.antiquotation name scan (fn {source, context = ctxt, ...} =>
    Thy_Output.output ctxt o Thy_Output.maybe_pretty_source pretty ctxt source);

fun basic_entity name scan = basic_entities name (scan >> single);

fun pretty_attr_access_style ctxt (style, ((oid,pos),(attr,pos'))) = 
           Thy_Output.pretty_term ctxt (style (compute_attr_access (Context.Proof ctxt) 
                                                                    attr oid pos pos'));
fun pretty_trace_style ctxt (style, (oid,pos)) = 
          Thy_Output.pretty_term ctxt (style (compute_attr_access  (Context.Proof ctxt) 
                                                                   "trace" oid pos pos));
in  
val _ = Theory.setup 
           (ML_Antiquotation.inline @{binding docitem_attribute} 
               (fn (ctxt,toks) => (parse_attribute_access >>  attr_2_ML ctxt) (ctxt, toks))  #>
            ML_Antiquotation.inline @{binding trace_attribute}
               (fn (ctxt,toks) => (parse_oid >> trace_attr_2_ML ctxt) (ctxt, toks)) #>
            basic_entity @{binding trace_attribute} parse_oid'  pretty_trace_style #>
            basic_entity @{binding docitem_attribute} parse_attribute_access' pretty_attr_access_style
           )
end
end
\<close>

text\<open> Note that the functions \<^verbatim>\<open>basic_entities\<close> and \<^verbatim>\<open>basic_entity\<close> in @{ML_structure AttributeAccess}
       are copied from @{file "$ISABELLE_HOME/src/Pure/Thy/thy_output.ML"} \<close>


section\<open> Syntax for Ontologies (the '' View'' Part III) \<close> 
ML\<open>
structure OntoParser = 
struct

fun read_parent NONE ctxt = (NONE, ctxt)
  | read_parent (SOME raw_T) ctxt =
      (case Proof_Context.read_typ_abbrev ctxt raw_T of
        Type (name, Ts) => (SOME (Ts, name), fold Variable.declare_typ Ts ctxt)
      | T => error ("Bad parent record specification: " ^ Syntax.string_of_typ ctxt T));

fun map_option _ NONE = NONE 
   |map_option f (SOME x) = SOME (f x);



fun read_fields raw_fields ctxt =
    let
      val Ts = Syntax.read_typs ctxt (map (fn ((_, raw_T, _),_) => raw_T) raw_fields);
      val terms = map ((map_option (Syntax.read_term ctxt)) o snd) raw_fields
      val count = Unsynchronized.ref (0 - 1);
      fun incr () = Unsynchronized.inc count
      fun test t1 t2 = Sign.typ_instance (Proof_Context.theory_of ctxt)
                                         (t1, ODL_Command_Parser.generalize_typ 0 t2) 
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


val tag_attr = (Binding.make("tag_attribute",@{here}), @{typ "int"},Mixfix.NoSyn)
val trace_attr = ((Binding.make("trace",@{here}), "(doc_class rexp \<times> string) list",Mixfix.NoSyn),
                  SOME "[]"): ((binding * string * mixfix) * string option)

fun add_doc_class_cmd overloaded (raw_params, binding) 
                      raw_parent raw_fieldsNdefaults reject_Atoms regexps thy =
    let
      val ctxt = Proof_Context.init_global thy;
      val params = map (apsnd (Typedecl.read_constraint ctxt)) raw_params;
      val ctxt1 = fold (Variable.declare_typ o TFree) params ctxt;
      fun cid thy = DOF_core.name2doc_class_name thy (Binding.name_of binding)
      val (parent, ctxt2) = read_parent raw_parent ctxt1;
      val parent_cid_long = case parent of
                              NONE => DOF_core.default_cid
                            | SOME(_,str) => str
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
                     case  DOF_core.get_attribute_info parent_cid_long (Binding.name_of bind) thy of
                           NONE => (* no prior declaration *) SOME(bind,ty,mf)
                         | SOME{def_occurrence,long_name,typ,def_pos} => if ty = typ 
                                                   then (warning("overriding attribute:"^long_name^
                                                                 " in doc class:" ^ def_occurrence);
                                                        SOME(bind,ty,mf))
                                                   else error("no overloading allowed.")
      val gen_antiquotation = OntoLinkParser.docitem_antiquotation
      val _ = map_filter (check_n_filter thy) fields


    in thy |> Record.add_record overloaded (params', binding) parent (tag_attr::fields)
           |> (Sign.add_consts_cmd [(binding,  "doc_class Regular_Exp.rexp", Mixfix.NoSyn)])
           |> DOF_core.define_doc_class_global (params', binding) parent fieldsNterms' regexps reject_Atoms
              (* adding const symbol representing doc-class for Monitor-RegExps.*)
           |> (fn thy => gen_antiquotation binding (cid thy) thy)
              (* defines the ontology-checked text antiquotation to this document class *)
           
    end;


val _ =
  Outer_Syntax.command @{command_keyword doc_class} "define document class"
    ((Parse_Spec.overloaded 
     -- (Parse.type_args_constrained  -- Parse.binding) 
     -- (@{keyword "="} 
     |-- Scan.option (Parse.typ --| @{keyword "+"}) 
      -- Scan.repeat1 
             (Parse.const_binding -- Scan.option (@{keyword "<="} |-- Parse.term)))
      -- (   Scan.optional (@{keyword "rejects"} |-- Parse.enum1 "," Parse.term) []
          -- Scan.repeat   (@{keyword "accepts"} |-- Parse.term))) 
    >> (fn (((overloaded, x), (y, z)),(rejectS,accept_rex)) =>
           Toplevel.theory (add_doc_class_cmd {overloaded = overloaded} x y z rejectS accept_rex)));

end (* struct *)
\<close>  


section\<open> Testing and Validation \<close>
  
(* the f ollowing test crashes the LaTeX generation - however, without the latter this output is 
   instructive 
ML\<open>
writeln (DOF_core.toStringDocItemCommand "section" "scholarly_paper.introduction" []);
writeln (DOF_core.toStringDocItemLabel "scholarly_paper.introduction" []);
writeln (DOF_core.toStringDocItemRef "scholarly_paper.introduction" "XX" []);

(DOF_core.write_ontology_latex_sty_template @{theory})
\<close>
*)

lemma X : "True" sorry

end
