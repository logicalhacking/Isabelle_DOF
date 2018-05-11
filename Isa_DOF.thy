chapter \<open>The Document-Type Support Framework for Isabelle\<close>

text{* Offering reflection to ML for class hierarchies, objects and object states. 
       + Isar syntax for these, assuming that classes entities fit to predefined
       Isar keywords.
 *} 
  
text{* In this section, we develop on the basis of a management of references Isar-markups
that provide direct support in the PIDE framework. *}  
  
theory Isa_DOF   (* Isabelle Document Ontology Framework *)
  imports  Main  (* Isa_MOF *)
           RegExp
  keywords "+=" ":="

  and      "section*"    "subsection*"   "subsubsection*" 
           "paragraph*"  "subparagraph*" "text*"  ::thy_decl
           
  and      "open_monitor*" "close_monitor*" "declare_reference*" 
           "update_instance*" "doc_class" ::thy_decl

  and      "lemma*" ::thy_decl
           
  
begin
  
section{*Inner Syntax Antiquotations: Syntax *}

typedecl "typ"
typedecl "term"
typedecl "thm"
typedecl "file"
typedecl "http"
typedecl "thy"
 
-- \<open> and others in the future : file, http, thy, ... \<close> 

consts mk_typ     :: "string \<Rightarrow> typ"     ("@{typ _}")
consts mk_term    :: "string \<Rightarrow> term"    ("@{term _}")
consts mk_thm     :: "string \<Rightarrow> thm"     ("@{thm _}")
consts mk_file    :: "string \<Rightarrow> file"    ("@{file _}")
consts mk_thy     :: "string \<Rightarrow> thy"     ("@{thy _}")
consts mk_docitem :: "string \<Rightarrow> 'a"      ("@{docitem _}")

  
term "@{typ  ''int => int''}"  
term "@{term ''Bound 0''}"  
term "@{thm  ''refl''}"  
term "@{docitem  ''<doc_ref>''}"
  
  
  
section{*Primitive Markup Generators*}
ML{*

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

*}

section{* A HomeGrown Document Type Management (the ''Model'') *}
  
ML{*
structure DOF_core = 
struct
   type docclass_struct = {params : (string * sort) list, (*currently not used *)
                           name   : binding, thy_name : string, id : serial, (* for pide *)
                           inherits_from : (typ list * string) option,
                           attribute_decl : (binding * typ * term option) list
                           (*, rex : term list -- not yet used *)}


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
           (t = default_cid andalso Symtab.defined tab s ) orelse
           father_is_sub s
        end

   type docobj = {pos : Position.T, 
                  thy_name : string,
                  value   : term, 
                  id : serial, cid : string}

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

(* registrating data of the Isa_DOF component *)
structure Data = Generic_Data
(
  type T = docobj_tab * docclass_tab 
  val empty  = (initial_docobj_tab, initial_docclass_tab) 
  val extend = I
  fun merge((d1,c1),(d2,c2))  = (merge_docobj_tab (d1, d2), merge_docclass_tab(c1,c2))
);

val get_data = Data.get o Context.Proof;
val map_data = Data.map;
val get_data_global = Data.get o Context.Theory;
val map_data_global = Context.theory_map o map_data;


(* doc-class-name management: We still use the record-package for internally 
   representing doc-classes. The main motivation is that "links" to entities are
   types over doc-classes, *types* in the Isabelle sense, enriched by additional data.
   This has the advantage that the type-inference can be abused to infer long-names
   for doc-class-names. Note, however, that doc-classes are currently implemented
   by non-polymorphic records only; this means that the extensible "_ext" versions
   of type names must be reduced to qualifier names only. The used Syntax.parse_typ 
   handling the identification does that already. *)
 
fun is_subclass (ctxt) s t = is_subclass0(snd(get_data ctxt)) s t

fun type_name2doc_class_name thy str =  (*  Long_Name.qualifier *) str

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



fun is_defined_cid_global cid thy = let val t = snd(get_data_global thy)
                                    in  cid=default_cid orelse 
                                        Symtab.defined t (name2doc_class_name thy cid) 
                                    end


fun is_defined_cid_local cid ctxt  = let val t = snd(get_data ctxt)
                                     in  cid=default_cid orelse 
                                         Symtab.defined t (name2doc_class_name_local ctxt cid) 
                                     end


fun is_declared_oid_global oid thy = let val {tab,...} = fst(get_data_global thy)
                                     in  Symtab.defined tab oid end

fun is_declared_oid_local oid thy  = let val {tab,...} = fst(get_data thy)
                                     in  Symtab.defined tab oid end

fun is_defined_oid_global oid thy  = let val {tab,...} = fst(get_data_global thy)
                                     in  case Symtab.lookup tab oid of 
                                           NONE => false
                                          |SOME(NONE) => false
                                          |SOME _ => true
                                     end

fun is_defined_oid_local oid thy   = let val {tab,...} = fst(get_data thy)
                                     in  case Symtab.lookup tab oid of 
                                           NONE => false
                                          |SOME(NONE) => false
                                          |SOME _ => true
                                     end


fun declare_object_global oid thy  =  
    let fun decl {tab=t,maxano=x} = {tab=Symtab.update_new(oid,NONE)t, maxano=x}
    in (map_data_global (apfst(decl)) (thy)
       handle Symtab.DUP _ => error("multiple declaration of document reference"))
    end

fun declare_object_local oid ctxt  =
    let fun decl {tab,maxano} = {tab=Symtab.update_new(oid,NONE) tab, maxano=maxano}
    in  (map_data(apfst decl)(ctxt)
        handle Symtab.DUP _ => error("multiple declaration of document reference"))
    end


fun define_doc_class_global (params', binding) parent fields thy  = 
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
    
        val info = {params=params', 
                    name = binding, 
                    thy_name = nn, 
                    id = id, (* for pide --- really fresh or better reconstruct 
                                from prior record definition ? For the moment: own
                                generation of serials ... *)
                    inherits_from = parent,
                    attribute_decl = fields  (*  currently unchecked *)
                    (*, rex : term list -- not yet used *)}
    
    in   map_data_global(apsnd(Symtab.update(cid_long,info)))(thy)
    end


fun define_object_global (oid, bbb) thy  = 
    let val nn = Context.theory_name thy (* in case that we need the thy-name to identify
                                            the space where it is ... *)
    in  if is_defined_oid_global oid thy 
        then error("multiple definition of document reference")
        else map_data_global  (apfst(fn {tab=t,maxano=x} =>            
                                        {tab=Symtab.update(oid,SOME bbb) t,
                                         maxano=x}))
               (thy)
    end
            
fun define_object_local (oid, bbb) ctxt  = 
    map_data (apfst(fn{tab,maxano}=>{tab=Symtab.update(oid,SOME bbb)tab,maxano=maxano})) ctxt


(* declares an anonyme label of a given type and generates a unique reference ...  *)
fun declare_anoobject_global thy cid = 
    let fun declare {tab,maxano} = let val str = cid^":"^Int.toString(maxano+1)
                                       val _ = writeln("Anonymous doc-ref declared: " ^ str)
                                   in  {tab=Symtab.update(str,NONE)tab,maxano= maxano+1} end
    in  map_data_global (apfst declare) (thy)
    end

fun declare_anoobject_local ctxt cid = 
    let fun declare {tab,maxano} = let val str = cid^":"^Int.toString(maxano+1)
                                           val _ = writeln("Anonymous doc-ref declared: " ^str)
                                       in  {tab=Symtab.update(str,NONE)tab, maxano=maxano+1} end
    in map_data (apfst declare) (ctxt) 
    end


fun get_object_global oid thy  = let val {tab,...} = fst(get_data_global thy)
                                 in  case Symtab.lookup tab oid of 
                                       NONE => error("undefined reference: "^oid)
                                      |SOME(bbb) => bbb
                                 end

fun get_object_local oid ctxt  = let val {tab,...} = fst(get_data ctxt)
                                 in  case Symtab.lookup tab oid of 
                                       NONE => error("undefined reference: "^oid)
                                      |SOME(bbb) => bbb
                                 end

fun get_doc_class_global cid thy = 
    if cid = default_cid then error("default doc class acces") (* TODO *)
    else let val t = snd(get_data_global thy)
         in  (Symtab.lookup t cid) end
    

fun get_doc_class_local cid ctxt = 
    if cid = default_cid then error("default doc class acces") (* TODO *)
    else let val t = snd(get_data ctxt)
         in  (Symtab.lookup t cid) end


fun is_defined_cid_local cid ctxt  = let val t = snd(get_data ctxt)
                                     in  cid=default_cid orelse 
                                         Symtab.defined t (name2doc_class_name_local ctxt cid) 
                                     end

fun get_attributes_local cid ctxt =
    if cid = default_cid then []
    else let val t = snd(get_data ctxt)
             val cid_long = name2doc_class_name_local ctxt cid
         in  case Symtab.lookup t cid_long of
               NONE => error("undefined doc class id :"^cid)
             | SOME ({inherits_from=NONE,
                       attribute_decl = X, ...}) => [(cid_long,X)]
             | SOME ({inherits_from=SOME(_,father),
                       attribute_decl = X, ...}) => get_attributes_local father ctxt @ [(cid_long,X)]
         end

fun get_attributes cid thy = get_attributes_local cid (Proof_Context.init_global thy)

fun get_default_local cid attr ctxt =
    let val hierarchy_rev = rev(get_attributes_local cid ctxt)  (* search in reverse order *)
        fun found (_,L) = find_first (fn (bind,_,SOME(term)) => Binding.name_of bind = attr
                                        | _ => false) L                                  
    in  case get_first found hierarchy_rev of
           NONE => NONE
        |  SOME (_,_,X) => X
    end

fun get_default cid attr thy = get_default_local cid attr (Proof_Context.init_global thy)

fun get_attribute_long_name_local cid attr ctxt =
    let val hierarchy = get_attributes_local cid ctxt  (* search in order *)
        fun found (_,L) = find_first (fn (bind,_,_) => Binding.name_of bind = attr) L
    in  case get_first found hierarchy of
           NONE => NONE
         | SOME (bind, ty,_) => SOME(cid,(Binding.name_of bind), ty)
    end

fun get_attribute_long_name cid attr thy = get_attribute_long_name_local cid attr 
                                                 (Proof_Context.init_global thy)


fun get_value_global oid thy  = case get_object_global oid thy of
                                   SOME{value=term,...} => SOME term
                                 | NONE => NONE  

fun get_value_local oid ctxt  = case get_object_local oid ctxt of
                                   SOME{value=term,...} => SOME term
                                 | NONE => NONE  


fun update_value_global oid upd thy  = 
          case get_object_global oid thy of
               SOME{pos,thy_name,value,id,cid} => 
                   let val tab' = Symtab.update(oid,SOME{pos=pos,thy_name=thy_name,
                                                         value=upd value,id=id, cid=cid})
                   in   map_data_global (apfst(fn{tab,maxano}=>{tab=tab' tab,maxano=maxano})) thy end
             | NONE => error("undefined doc object: "^oid)  


fun writeln_classrefs ctxt = let  val tab = snd(get_data ctxt)
                             in   writeln (String.concatWith "," (Symtab.keys tab)) end


fun writeln_docrefs ctxt = let  val {tab,...} = fst(get_data ctxt)
                           in   writeln (String.concatWith "," (Symtab.keys tab)) end
end (* struct *)
*}
  

section{* Syntax for Annotated Documentation Commands (the '' View'' Part I) *}
  
ML{* 
structure AnnoTextelemParser = 
struct

val semi = Scan.option (Parse.$$$ ";");

val attribute =
    Parse.position Parse.const 
    -- Scan.optional (Parse.$$$ "=" |-- Parse.!!! Parse.term) "";

val attribute_upd  : (((string * Position.T) * string) * string) parser =
    Parse.position Parse.const 
    -- (@{keyword "+="} || @{keyword ":="})
    -- Parse.!!! Parse.term;

(* Scan.optional (Args.parens (Args.$$$ defineN || Args.$$$ uncheckedN) *)
val reference =
    Parse.position Parse.name 
    -- Scan.option (Parse.$$$ "::" |-- Parse.!!! (Parse.position Parse.name));


val attributes =  
    (Parse.$$$ "[" 
     |-- (reference -- 
         (Scan.optional(Parse.$$$ "," |-- (Parse.enum "," attribute))) []))
     --| Parse.$$$ "]"

val attributes_upd =  
    (Parse.$$$ "[" 
     |-- (reference -- 
         (Scan.optional(Parse.$$$ "," |-- (Parse.enum "," attribute_upd))) []))
     --| Parse.$$$ "]"

val SPY = Unsynchronized.ref ([]:((term * Position.T) * term) list) 

fun convert((Const(s,ty),_), t) X = Const(s^"_update", dummyT) 
                                    $ Abs("uuu_", type_of t, t) $ X
   |convert _ _ = error("Left-hand side not a doc_class attribute.")

val base = Const(@{const_name "undefined"},dummyT)

fun check_classref (SOME(cid,pos')) thy = 
          let val _ = if not (DOF_core.is_defined_cid_global cid thy) 
                      then error("document class undefined") else ()
              val cid_long = DOF_core.name2doc_class_name thy cid 
              val {id, name=bind_target,...} = the(DOF_core.get_doc_class_global cid_long thy)
              val markup = docclass_markup false cid id (Binding.pos_of bind_target);
              val ctxt = Context.Theory thy
              val _ = Context_Position.report_generic ctxt pos' markup;
          in  cid_long 
          end
   | check_classref  NONE _ = DOF_core.default_cid 


fun generalize_typ n = Term.map_type_tfree (fn (str,sort)=> Term.TVar((str,n),sort));
fun infer_type thy term = hd (Type_Infer_Context.infer_types (Proof_Context.init_global thy) [term])

fun enriched_document_command markdown (((((oid,pos),cid_pos),
                                              doc_attrs: ((string * Position.T) * string) list),
                                        xstring_opt:(xstring * Position.T) option),
                                        toks:Input.source) 
                                        : Toplevel.transition -> Toplevel.transition =
  let
    val id = serial ();
    val _ = Position.report pos (docref_markup true oid id pos);
            (* creates a markup label for this position and reports it to the PIDE framework;
               this label is used as jump-target for point-and-click feature. *)
                          
    fun enrich_trans thy = 
          let val cid_long = check_classref  cid_pos thy
              val count = Unsynchronized.ref (0 - 1);
              fun incr () = Unsynchronized.inc count
              val generalize_term =  let val n = incr () in Term.map_types (generalize_typ n) end
              fun read_assn  ((lhs, pos), rhs) = 
                                 ((Syntax.read_term_global thy lhs |> generalize_term,pos),
                                   Syntax.read_term_global thy rhs |> generalize_term)
              val assns = map read_assn doc_attrs
              val _ = (SPY:=assns)       
              val defaults = base       (* this calculation ignores the defaults *)
              val value_term = (fold convert assns defaults)  |> (infer_type thy) 
              val name = Context.theory_name thy 
          in  thy |> DOF_core.define_object_global (oid, {pos=pos, 
                                                          thy_name=name,
                                                          value = value_term,
                                                          id=id,   
                                                          cid=cid_long})
          end
    fun check_text thy = (Thy_Output.output_text(Toplevel.theory_toplevel thy) markdown toks; thy)
  in   
       Toplevel.theory(enrich_trans #> check_text)
       (* Thanks Frederic Tuong! ! ! *)
  end;

fun update_instance_command  (((oid:string,pos),cid_pos),
                              doc_attrs: (((string*Position.T)*string)*string)list)                                        
                             : Toplevel.transition -> Toplevel.transition = 
     let
         fun upd thy = 
             let val cid = case DOF_core.get_object_global oid thy of 
                                SOME{cid,...} => cid
                              | NONE => error("undefined doc_class.")
                 val cid_long = check_classref cid_pos thy
                 val _ = if cid_long = DOF_core.default_cid  orelse cid = cid_long then () 
                                       else error("incompatible classes:"^cid^":"^cid_long)

                 val count = Unsynchronized.ref (0 - 1);
                 fun incr () = Unsynchronized.inc count
                 val generalize_term =  let val n = incr () in Term.map_types (generalize_typ n) end
                 fun read_assn  (((lhs, pos), opn), rhs) = 
                           let val _ = writeln opn in 
                           ((Syntax.read_term_global thy lhs |> generalize_term ,pos), 
                                                           (* this is problematic, 
                                                              lhs need to be qualified  *)
                             Syntax.read_term_global thy rhs |> generalize_term)
                           end
                 (* Missing: Check that attributes are legal here *)
                 val assns = map read_assn doc_attrs
                 val _ = (SPY:=assns) 
          in  thy |> DOF_core.update_value_global oid ((fold convert assns) #> (infer_type thy))
          end
     in  Toplevel.theory(upd)
     end

val _ =
  Outer_Syntax.command ("section*", @{here}) "section heading"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> enriched_document_command {markdown = false});

val _ =
  Outer_Syntax.command ("subsection*", @{here}) "subsection heading"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> enriched_document_command {markdown = false});

val _ =
  Outer_Syntax.command ("subsubsection*", @{here}) "subsubsection heading"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> enriched_document_command {markdown = false});

val _ =
  Outer_Syntax.command ("paragraph*", @{here}) "paragraph heading"
    (attributes --  Parse.opt_target -- Parse.document_source --| semi
      >> enriched_document_command {markdown = false});

val _ =
  Outer_Syntax.command ("subparagraph*", @{here}) "subparagraph heading"
    (attributes -- Parse.opt_target -- Parse.document_source --| semi
      >> enriched_document_command {markdown = false});

val _ =
  Outer_Syntax.command ("text*", @{here}) "formal comment (primary style)"
    (attributes -- Parse.opt_target -- Parse.document_source 
      >> enriched_document_command {markdown = false});


val _ =
  Outer_Syntax.command @{command_keyword "declare_reference*"} 
                       "declare document reference"
                       (attributes >> (fn (((oid,pos),cid),doc_attrs) =>  
                                      (Toplevel.theory (DOF_core.declare_object_global oid))));

val _ =
  Outer_Syntax.command @{command_keyword "open_monitor*"} 
                       "open a document reference monitor"
                       (attributes >> (fn (((oid,pos),cid),doc_attrs) =>  
                                       (Toplevel.theory (DOF_core.declare_object_global oid))));

val _ =
  Outer_Syntax.command @{command_keyword "close_monitor*"} 
                       "close a document reference monitor"
                       (attributes >> (fn (((oid,pos),cid),doc_attrs) => 
                                          (Toplevel.theory (I)))); (* dummy so far *)

val _ =
  Outer_Syntax.command @{command_keyword "lemma*"} 
                       "close a document reference monitor"
                       (attributes >> (fn (((oid,pos),cid),doc_attrs) => 
                                          (Toplevel.theory (I)))); (* dummy/fake so far *)

val _ =
  Outer_Syntax.command @{command_keyword "update_instance*"} 
                       "update meta-attributes of an instance of a document class"
                        (attributes_upd >> (fn args =>  update_instance_command args)); 

end (* struct *)

*}

lemma murx : "XXX" sorry
  
section{* Syntax for Ontological Antiquotations (the '' View'' Part II) *}
  
ML{*
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

val doc_ref_modes = Scan.optional (Args.parens (Args.$$$ defineN || Args.$$$ uncheckedN) 
                                   >> (fn str => if str = defineN 
                                                 then {unchecked = false, define= true}  
                                                 else {unchecked = true,  define= false})) 
                                   {unchecked = false, define= false} (* default *);


fun docitem_ref_antiquotation name cid_decl = 
    let fun open_par x = if x then "\\label{" 
                              else "\\autoref{"
        val close = "}"
    in
        Thy_Output.antiquotation name (Scan.lift (doc_ref_modes -- Args.cartouche_input))
            (fn {context = ctxt, source = src:Token.src, state} =>
                 fn ({unchecked = x, define= y}, source:Input.source) => 
                     (Thy_Output.output_text state {markdown=false} #>
                      check_and_mark ctxt                   
                                     cid_decl 
                                     ({strict_checking = not x})
                                     (Input.pos_of source) #>
                      enclose (open_par y) close) 
                     source)
     end


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



val X = (Scan.lift Args.cartouche_input : Input.source context_parser) >> (fn inp => "")

fun docitem_value_ML_antiquotation binding = 
    ML_Antiquotation.inline binding 
         (fn (ctxt, toks) => (Scan.lift (Args.cartouche_input) 
                              >> (fn inp => (ML_Syntax.atomic o ML_Syntax.print_term) 
                                            (check_and_mark_term ctxt (Input.source_content inp)))) 
                             (ctxt, toks))
                                         

(* Setup for general docrefs of the global DOF_core.default_cid - class ("text")*)
val _ = Theory.setup((docitem_ref_antiquotation @{binding docref} DOF_core.default_cid) #>
                     (* deprecated syntax                 ^^^^^^*)
                     (docitem_ref_antiquotation @{binding docitem_ref} DOF_core.default_cid) #>
                      docitem_value_ML_antiquotation @{binding docitem_value})

end (* struct *)
*}

  
section{* Syntax for Ontologies (the '' View'' Part III) *} 
ML{* 
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
                                         (t1, AnnoTextelemParser.generalize_typ 0 t2) 
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

fun add_doc_class_cmd overloaded (raw_params, binding) raw_parent raw_fieldsNdefaults rexp thy =
    let
      val ctxt = Proof_Context.init_global thy;
      val _ = map (Syntax.read_term_global thy) rexp;
      val params = map (apsnd (Typedecl.read_constraint ctxt)) raw_params;
      val ctxt1 = fold (Variable.declare_typ o TFree) params ctxt;
      fun cid thy = DOF_core.name2doc_class_name thy (Binding.name_of binding)
      val (parent, ctxt2) = read_parent raw_parent ctxt1;
      val parent_cid_long = case parent of
                              NONE => DOF_core.default_cid
                            | SOME(_,str) => str
      val (fields, terms, ctxt3) = read_fields raw_fieldsNdefaults ctxt2;
      val fieldsNterms = (map (fn (a,b,_) => (a,b)) fields) ~~ terms
      val fieldsNterms' = map (fn ((x,y),z) => (x,y,z)) fieldsNterms
      val params' = map (Proof_Context.check_tfree ctxt3) params;
      fun check_n_filter thy (bind,ty,mf) = 
                     case  DOF_core.get_attribute_long_name parent_cid_long (Binding.name_of bind) thy of
                           NONE => (* no prior declaration *) SOME(bind,ty,mf)
                         | SOME(class,attr,ty') => if ty = ty' 
                                                   then (warning("overriding attribute:"^ attr^
                                                                 " in doc class:" ^ class);
                                                        SOME(bind,ty,mf))
                                                   else error("no overloading allowed.")
      val gen_antiquotation = OntoLinkParser.docitem_ref_antiquotation
      val _ = map_filter (check_n_filter thy) fields
   
    in thy |> Record.add_record overloaded (params', binding) parent (tag_attr::fields) 
           |> DOF_core.define_doc_class_global (params', binding) parent fieldsNterms'
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
     -- Scan.repeat (@{keyword "where"} |-- Parse.term)) 
    >> (fn (((overloaded, x), (y, z)),rex) =>
           Toplevel.theory (add_doc_class_cmd {overloaded = overloaded} x y z rex)));

end (* struct *)

*}  
   
  

section{* Testing and Validation *}

  
  
end
