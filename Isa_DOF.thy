chapter \<open>The Document-Type Support Framework for Isabelle\<close>

text{* Offering reflection to ML for class hierarchies, objects and object states. 
       + Isar syntax for these, assuming that classes entities fit to predefined
       Isar keywords.
 *} 
  
text{* In this section, we develop on the basis of a management of references Isar-markups
that provide direct support in the PIDE framework. *}  
  
theory Isa_DOF   (* Isabelle Document Ontology Framework *)
  imports  Main (* Isa_MOF *)
  keywords "section*"    "subsection*"   "subsubsection*" 
           "paragraph*"  "subparagraph*" "text*" "declare_reference"::thy_decl
           and
           "doc_class" :: thy_decl 
  
begin
  
  
section{* A HomeGrown Document Type Management (the ''Model'') *}

ML{*
curry;
op |>; 
op #>;
op |>> : ('a * 'c) * ('a -> 'b) -> 'b * 'c;
op ||> : ('c * 'a) * ('a -> 'b) -> 'c * 'b;

val docrefN = "docref";    

(* derived from: theory_markup *) 
fun docref_markup def name id pos =
  if id = 0 then Markup.empty
  else
    Markup.properties (Position.entity_properties_of def id pos)
      (Markup.entity docrefN name);   (* or better store the thy-name as property ? ? ? *)

*}
  

  
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
                                  then error "document superclass not defined"
                                  else default_cid
                       |  SOME _ => ""
            fun father_is_sub s = case Symtab.lookup tab s of 
                          NONE => error "document subclass not defined"
                       |  SOME ({inherits_from=NONE, ...}) => s = t
                       |  SOME ({inherits_from=SOME (_,s'), ...}) => 
                                  s' = t orelse father_is_sub s' 
        in s = t orelse 
           (t = default_cid andalso Symtab.defined tab s ) orelse
           father_is_sub s
        end

   type docobj = {pos : Position.T, thy_name : string, id : serial, cid : string}

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


fun is_declared_oid_global oid thy = let val {tab=t,maxano=_} = fst(get_data_global thy)
                                     in  Symtab.defined t oid end

fun is_declared_oid_local oid thy  = let val {tab=t,maxano=_} = fst(get_data thy)
                                     in  Symtab.defined t oid end

fun is_defined_oid_global oid thy  = let val {tab=t,maxano=_} = fst(get_data_global thy)
                                     in  case Symtab.lookup t oid of 
                                           NONE => false
                                          |SOME(NONE) => false
                                          |SOME _ => true
                                     end

fun is_defined_oid_local oid thy    = let val {tab=t,maxano=_} = fst(get_data thy)
                                     in  case Symtab.lookup t oid of 
                                           NONE => false
                                          |SOME(NONE) => false
                                          |SOME _ => true
                                     end


fun declare_object_global oid thy  =  (map_data_global
                                                   (apfst(fn {tab=t,maxano=x} => 
                                                             {tab=Symtab.update_new(oid,NONE)t,
                                                              maxano=x})) 
                                                   (thy)
                                       handle Symtab.DUP _ => 
                                              error("multiple declaration of document reference"))

fun declare_object_local oid ctxt  = (map_data (apfst(fn {tab=t,maxano=x} => 
                                                         {tab=Symtab.update_new(oid,NONE) t,
                                                          maxano=x}))
                                               (ctxt)
                                      handle Symtab.DUP _ => 
                                             error("multiple declaration of document reference"))


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
               val _ = Position.report pos (docref_markup true cid id pos);

               val info = {params=params', 
                           name = binding, 
                           thy_name = nn, 
                           id = id, (* for pide --- really fresh or better reconstruct 
                                             from prior record definition ? *)
                           inherits_from = parent,
                           attribute_decl = fields  (*  currently unchecked *)
                           (*, rex : term list -- not yet used *)}
               val _ = ()  (* XXX *)     

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
           map_data (apfst(fn {tab=t,maxano=x} => 
                              {tab=Symtab.update(oid,SOME bbb) t,maxano=x})) ctxt


(* declares an anonyme label of a given type and generates a unique reference ...  *)
fun declare_anoobject_global thy cid = map_data_global
                                           (apfst(fn {tab=t,maxano=x} =>
                                                     let val str = cid^":"^Int.toString(x+1)
                                                         val _ = writeln("Anonymous doc-ref declared: "
                                                                         ^str)
                                                     in  {tab=Symtab.update(str,NONE)t,maxano=x+1}
                                                     end))         
                                           (thy)

fun declare_anoobject_local ctxt cid = map_data
                                          (apfst(fn {tab=t,maxano=x} => 
                                                     let val str = cid^":"^Int.toString(x+1)
                                                         val _ = writeln("Anonymous doc-ref declared: "
                                                                     ^str)
                                                     in   {tab=Symtab.update(str,NONE)t, maxano=x+1}
                                                     end)) 
                                          (ctxt)


fun get_object_global oid thy  = let val {tab=t,maxano=_} = fst(get_data_global thy)
                                     in  case Symtab.lookup t oid of 
                                           NONE => error"undefined reference"
                                          |SOME(bbb) => bbb
                                     end

fun get_object_local oid ctxt  = let val {tab=t,maxano=_} = fst(get_data ctxt)
                                     in  case Symtab.lookup t oid of 
                                           NONE => error"undefined reference"
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

fun writeln_classrefs ctxt = let  val t = snd(get_data ctxt)
                        in   writeln (String.concatWith "," (Symtab.keys t)) end


fun writeln_docrefs ctxt = let  val {tab=t,maxano=_} = fst(get_data ctxt)
                        in   writeln (String.concatWith "," (Symtab.keys t)) end
end (* struct *)
*}
  

section{* Syntax for Annotated Documentation Commands (the '' View'') *}

  
ML{* 
structure DocAttrParser = 
struct

val semi = Scan.option (Parse.$$$ ";");

val attribute =
  Parse.position Parse.name 
  -- Scan.optional (Parse.$$$ "=" |-- Parse.!!! Parse.name) "";


val reference =
  Parse.position Parse.name 
  -- Scan.option (Parse.$$$ "::" |-- Parse.!!! (Parse.position Parse.name));


val attributes =  (Parse.$$$ "[" |-- (reference -- 
                                     (Scan.optional(Parse.$$$ "," |-- (Parse.enum "," attribute))) []))
                                  --| Parse.$$$ "]"


fun enriched_document_command markdown (((((oid,pos),cid_pos),doc_attrs),
                                        xstring_opt:(xstring * Position.T) option),
                                        toks:Input.source)  =
  let
    val id = serial ();
    val _ = Position.report pos (docref_markup true oid id pos);
            (* creates a markup label for this position and reports it to the PIDE framework;
               this label is used as jump-target for point-and-click feature. *)

    fun enrich_trans  (SOME(cid,pos')) thy = 
                           let val name = Context.theory_name thy 
                               val _ = if not (DOF_core.is_defined_cid_global cid thy) 
                                       then error("document class undefined")
                                       else ()
                               val cid_long =  DOF_core.name2doc_class_name thy cid 
                               val _ = writeln cid_long

(*
 val {pos=pos_decl,id,cid,...} = the(DOF_core.get_object_global name thy)
             val markup = docref_markup false name id pos_decl;
             val _ = Context_Position.report ctxt pos markup;
Context.Theory; 
Context_Position.report_generic;

*)
                               val {id, name=bind_target,...} = 
                                                     the(DOF_core.get_doc_class_global cid_long thy)
                               val markup = docref_markup false cid id (Binding.pos_of bind_target);
                               val ctxt = Context.Theory thy
                               val _ = Context_Position.report_generic ctxt pos' markup;


                           in DOF_core.define_object_global (oid, {pos=pos, thy_name=name,
                                                                   id=id,   cid=cid_long})
                                                             (thy)
                           end
       | enrich_trans  NONE thy = 
                           let val name = Context.theory_name thy 
                           in  DOF_core.define_object_global 
                                  (oid, {pos=pos, thy_name=name,
                                         id=id , cid=DOF_core.default_cid}) 
                               (thy)
                           end
    fun MMM(SOME(s,p)) = SOME(s^"XXX",p)
       |MMM(NONE) = SOME("XXX",Position.id "")
  in     
       (Toplevel.theory(enrich_trans cid_pos))  #>
       (Thy_Output.document_command markdown (MMM xstring_opt,toks)) #>
       (Thy_Output.document_command markdown (SOME("\\label{"^oid^"}", Position.id ""),toks))  #>
       (Thy_Output.document_command markdown (SOME("\\label{"^oid^"}", Position.id ""),toks)) 
  end;


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
  Outer_Syntax.command @{command_keyword "declare_reference"} "declare document reference"
    (attributes >> (fn (((oid,pos),cid),doc_attrs) =>  
                                  (Toplevel.theory (DOF_core.declare_object_global oid))));


(* Proof.context -> Symtab.key * Position.T -> Pretty.T ; dead code: 
fun pretty_docref ctxt (name, pos)  =
  let
    (* val _ = DOF_core.writeln_keys ctxt *)
    val thy = Proof_Context.theory_of ctxt;
    fun pretty_docref str = let val tok = Pretty.enclose "\\autoref{" "}" (Pretty.text (str))
                            (*  val _ = writeln (Pretty.string_of tok) *)
                            in tok end
  in 
    if DOF_core.is_defined_oid_global name thy 
    then let val {pos=pos_decl,id,...} = the(DOF_core.get_object_global name thy)
             val markup = docref_markup false name id pos_decl;
             val _ = Context_Position.report ctxt pos markup;
                     (* this sends a report to the PIDE interface ... *) 
         in pretty_docref name end
    else if   DOF_core.is_declared_oid_global name thy 
         then (warning("declared but undefined document reference:"^name);
               pretty_docref name)
         else error("undefined document reference:"^name)
  end
*)


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
         then (if #strict_checking str then warning("declared but undefined document reference:"^name)
               else (); name)
         else error("undefined document reference:"^name)
  end

(* superfluous :
fun basic_entities_style name scan pretty =
  Thy_Output.antiquotation name scan (fn {source, context = ctxt, ...} => fn (style, xs) =>
     Thy_Output.output ctxt
        (Thy_Output.maybe_pretty_source (fn ctxt => fn x => pretty ctxt (style, x)) ctxt source xs));

fun basic_entities name scan pretty =
  Thy_Output.antiquotation name scan (fn {source, context = ctxt, ...} =>
    Thy_Output.output ctxt o Thy_Output.maybe_pretty_source pretty ctxt source);

fun basic_entity name scan = basic_entities name (scan >> single);
*)

fun control_antiquotation name cid_decl (str:{strict_checking: bool}) s1 s2 = 
             Thy_Output.antiquotation name (Scan.lift (Args.cartouche_input))
                 (fn {context =ctxt, source = src:Token.src, state} =>
                      fn source:Input.source => 
                          (Thy_Output.output_text state {markdown=false} #>
                           check_and_mark ctxt cid_decl (str:{strict_checking: bool})(Input.pos_of source) #>
                           enclose s1 s2) 
                          source);


(* Setup for general docrefs of the global DOF_core.default_cid - class ("text")*)
val _ = Theory.setup
        ((control_antiquotation @{binding docref} DOF_core.default_cid {strict_checking=true}  "\\autoref{" "}" ) #>
         (control_antiquotation @{binding docref_unchecked} DOF_core.default_cid {strict_checking=false} "\\autoref{" "}")#>
         (control_antiquotation @{binding docref_define} DOF_core.default_cid {strict_checking=false}   "\\label{" "}"))

end (* struct *)
*}
  
ML{* 

fun read_parent NONE ctxt = (NONE, ctxt)
  | read_parent (SOME raw_T) ctxt =
      (case Proof_Context.read_typ_abbrev ctxt raw_T of
        Type (name, Ts) => (SOME (Ts, name), fold Variable.declare_typ Ts ctxt)
      | T => error ("Bad parent record specification: " ^ Syntax.string_of_typ ctxt T));


fun map_option _ NONE = NONE 
   |map_option f (SOME x) = SOME (f x)

fun read_fields raw_fields ctxt =
  let
    val Ts = Syntax.read_typs ctxt (map (fn ((_, raw_T, _),_) => raw_T) raw_fields);
    val terms = map ((map_option (Syntax.read_term ctxt)) o snd) raw_fields
    val fields = map2 (fn ((x, _, mx),_) => fn T => (x, T, mx)) raw_fields Ts;
    val ctxt' = fold Variable.declare_typ Ts ctxt;
  in (fields, terms, ctxt') end;

fun add_record_cmd overloaded (raw_params, binding) raw_parent raw_fieldsNdefaults _ thy =
  let
    val ctxt = Proof_Context.init_global thy;
    val params = map (apsnd (Typedecl.read_constraint ctxt)) raw_params;
    val ctxt1 = fold (Variable.declare_typ o TFree) params ctxt;
    val (parent, ctxt2) = read_parent raw_parent ctxt1;
    val (fields, terms, ctxt3) = read_fields raw_fieldsNdefaults ctxt2;
    val fieldsNterms = (map (fn (a,b,_) => (a,b)) fields) ~~ terms
    val fieldsNterms' = map (fn ((x,y),z) => (x,y,z)) fieldsNterms
    val params' = map (Proof_Context.check_tfree ctxt3) params;
  in thy |> Record.add_record overloaded (params', binding) parent fields 
         |> DOF_core.define_doc_class_global (params', binding) parent fieldsNterms'
  end;


val _ =
  Outer_Syntax.command @{command_keyword doc_class} "define document class"
    (Parse_Spec.overloaded 
        -- (Parse.type_args_constrained  -- Parse.binding) 
        -- (@{keyword "="} |-- Scan.option (Parse.typ --| @{keyword "+"}) 
            -- Scan.repeat1 (Parse.const_binding -- Scan.option (@{keyword "<="} |-- Parse.term)))
            -- Scan.repeat (@{keyword "where"} |-- Parse.term) 
    >> (fn (((overloaded, x), (y, z)),rex) =>
        Toplevel.theory (add_record_cmd {overloaded = overloaded} x y z rex)));

*}  



section{* Testing and Validation *}

ML{* 
Binding.print;
Syntax.read_term;
Syntax.pretty_typ;
try;

*}  
  
  
(* Look at this thingi ... *)  
ML \<open>
fun document_command markdown (loc, txt) =
  Toplevel.keep 
    (fn state => (case loc of
                   NONE => ignore (Thy_Output.output_text state markdown txt)
                 | SOME (_, pos) => error ("Illegal target specification -- not a theory context" 
                                    ^ Position.here pos))) 
  o Toplevel.present_local_theory loc 
      (fn state => ignore (Thy_Output.output_text state markdown txt));

\<close>  

text{* @{theory "Nat"}*}
ML\<open>
open Markup;
Markup.binding;
TFree;
open Position;
Position.line;
Context.Theory; 
Context_Position.report_generic;
Context_Position.report;
\<close>
  
end