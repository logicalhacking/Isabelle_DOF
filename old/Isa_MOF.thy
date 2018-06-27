chapter \<open>The Document Meta-Class Framework for Isabelle \<close>

text{* A kind of ".dtd" for Isabelle documents modeled inside Isabelle for Isabelle, including
       general reg-exps for specifying the syntactic structure of sub-entities as well as
       sub-typing between document classes. *}  
  
theory Isa_MOF
  imports RegExp
          "~~/src/HOL/Library/Code_Target_Numeral"
          "~~/src/HOL/Library/String"
begin
  
type_synonym string = String.literal
type_synonym cid = string (*class identifier *)
type_synonym aid = string (*attribute identifier *)
type_synonym xstring = string  
type_synonym oid = string
  
  
  
datatype attribute_types =  file\<^sub>T       (file_name: string)
                          | image_file\<^sub>T (image_file_name : string)
                          | thms\<^sub>T       (thm_names : "string list") 
                          | int\<^sub>T        (int_of : int)
                          | bool\<^sub>T       (bool_of : bool)
                          | string\<^sub>T     (string_of : string)
                          | text\<^sub>T       (text_of : xstring) 
                          | range\<^sub>T      (start : int) (end_opt : "int option")
                          | enum\<^sub>T       (enum_ids : "string list")

(*  
datatype ('\<sigma>\<^sub>s\<^sub>y\<^sub>s)base_types = int\<^sub>T         (default1:"int")                    
                          | string\<^sub>T      (default2:"string")            
                          | int_list\<^sub>T    (default3:"int list")          
                          | string\<^sub>_list\<^sub>T (default4:"string list")     
                          | method\<^sub>T      (action:"'\<sigma>\<^sub>s\<^sub>y\<^sub>s \<Rightarrow> '\<sigma>\<^sub>s\<^sub>y\<^sub>s")
(* Options ?*)
*)
  
                            
type_synonym attribute_env = "(string \<times> attribute_types)list"    
  
type_synonym entity_env =    "(string \<times> (oid \<times> cid)rexp) list"
  (* entities have a regular structure, i.e. their syntactic structure is described by
     a regular grammar involving in object-conformance checks a grammar check. *)
  
datatype  class_hierarchy = class\<^sub>T  (class_name : cid)                               
                                    (subclasses : "class_hierarchy list" )    
                                    (attributes : "attribute_env")
                                    (entities   : "entity_env")
(* The conceptual distinction between attributes and entities is pragmatic - attributes
   are basic values, components sub-OBJECTS having an class-typed syntactical 
   structure. *)

(* Note: we may have override in attributes and entities,
   and their name-spaces are disjoint. Obviously, the syntactic entity structure may be
   inexistent ([]) or having empty entities ("bla", <>). The semantics of the list concatenation
   of two entities is textual sequencing. *)          
                                        
text{* in the reflection part, @{typ 'oid} will be instantiated with 
       @{ML_type "bstring * Binding.binding"} pairs allowing native Isabelle/jedit support for
       document editing. *}  (* quatsch *)
                                                  
                                     
definition mt :: "class_hierarchy"
  where   "mt == class\<^sub>T  (String.implode ''/'') [] [] [] "
                                     
fun      classes :: "class_hierarchy \<Rightarrow> string list" 
  where "classes (class\<^sub>T name sub_classes attr comps) =  name # concat(map classes sub_classes)"

fun      all_attributes ::  "class_hierarchy \<Rightarrow> attribute_env list" 
  where "all_attributes (class\<^sub>T name sub_classes attr comps) =  attr # (map attributes sub_classes)"
  
fun      all_entities :: "class_hierarchy \<Rightarrow> entity_env list" 
  where "all_entities (class\<^sub>T name sub_classes attr comps) =  comps # (map entities sub_classes)"  

fun      atoms_of :: "'a rexp \<Rightarrow> 'a list" 
  where "atoms_of <>      = []" 
       |"atoms_of (\<lfloor>x\<rfloor>)   = [x]"
       |"atoms_of(a | b)  = atoms_of a @ atoms_of b"
       |"atoms_of(a : b)  = atoms_of a @ atoms_of b"
       |"atoms_of(Star a) = atoms_of a"

         
text{* Elementary consistency definitions ... *}
definition wff ::  "class_hierarchy \<Rightarrow> bool"
  where   "wff H = (distinct(classes H) \<and> 
                    (\<forall> (_,cid) \<in> set(concat(map(atoms_of o snd)
                                               (concat(all_entities H)))). cid \<in> set(classes H)) \<and> 
                    (\<forall> attribute_list \<in> set(all_attributes H). distinct(map fst attribute_list)) \<and>
                    (\<forall> entity_list    \<in> set(all_entities H).   distinct(map fst entity_list)) 
                   )"

lemma wff_mt [simp]: "wff mt"
  unfolding mt_def wff_def by auto
    
lemma class_names_distinct : "wff H \<Longrightarrow> distinct(classes H)"  unfolding wff_def by(auto)  
    
lemma class_names_declared_in_component_decl : 
      "wff H \<Longrightarrow> (\<forall> (_,cid) \<in> set(concat(map(atoms_of o snd)
                                               (concat(all_entities H)))). cid \<in> set(classes H))"  
      unfolding wff_def by(auto)  
    
lemma attribute_names_unique_in_attr_decl : 
      "wff H \<Longrightarrow> (\<forall> attribute_list \<in> set(all_attributes H). distinct(map fst attribute_list))"  
      unfolding wff_def by(auto)  

lemma component_names_unique_in_attr_decl : 
      "wff H \<Longrightarrow> (\<forall> entity_list \<in> set(all_attributes H). distinct(map fst entity_list))"  
      unfolding wff_def by(auto)  
        
        
fun get_subclass :: "class_hierarchy \<Rightarrow>  nat list \<Rightarrow> class_hierarchy option"
  where "get_subclass H [] = Some H"
       |"get_subclass (class\<^sub>T cid subs attrs ents) (n#S) = 
                              (if n < length subs 
                               then case get_subclass (subs ! n) S of
                                       Some H' \<Rightarrow> Some (class\<^sub>T cid (subs[n := H']) attrs ents)
                                     | None \<Rightarrow> None
                               else None)"

(* I don't know if this is general enough. It does not allow the introduction
   of classes which are mutually dependant. 
 *)  
fun extend_class_hierarchy :: "((class_hierarchy \<Rightarrow> class_hierarchy) \<times> class_hierarchy) \<Rightarrow>
                                (cid \<times> attribute_env \<times> entity_env) \<Rightarrow> 
                                class_hierarchy" (infixl "\<uplus>" 70)
  where  "(C,H) \<uplus> (cid,attrs,ents) = 
                (if cid \<notin> set(classes (C H))  (* cid fresh in context and subhierarchy *)
                 then if distinct(map fst attrs) 
                      then if distinct(map fst ents)
                           then case H of 
                                  class\<^sub>T cid' subs attrs' ents' \<Rightarrow> 
                                           C(class\<^sub>T cid' (( class\<^sub>T cid [] attrs' ents') # subs) attrs ents) 
                           else mt
                      else mt
                 else mt)"

(* Todo : Lemmas that establish wff of extended trees *)

lemma wff_preserved :
  assumes "wff (C H)"
  shows   "wff((C,H) \<uplus> (cid,attrs,ents))"
        apply(insert assms)
  sorry
    
    (* well, this does not hold. this can only be true for standard contexts C, but
       how do we model this ? ? ? *)
    (* sigh, then try Dewey notation and classical grafting. *)
    
    
section{* Subclass properties *}
  
fun dir_sub_class :: "string \<Rightarrow> class_hierarchy \<Rightarrow> string \<Rightarrow> bool" 
                      ("(_)\<sqsubset>\<^bsub>(_)\<^esub> (_)"[60,80,60]80) 
  where "(s \<sqsubset>\<^bsub>(class\<^sub>T  n subs _ _)\<^esub> t) =  ((s=n \<and> t \<in> set (map class_name subs) \<or>
                                          (\<exists> sub\<in>set subs. s \<sqsubset>\<^bsub>sub\<^esub> t)))"

definition sub_class :: "string \<Rightarrow> class_hierarchy \<Rightarrow> string  \<Rightarrow> bool" 
                         ("(_)\<sqsubseteq>\<^bsub>(_)\<^esub> (_)"[60,80,60]80) 
  where "(s \<sqsubseteq>\<^bsub>(H)\<^esub> t) =  ((s,t) \<in> {(x,y). x \<sqsubset>\<^bsub>(H)\<^esub> y}\<^sup>*) "    
  
lemma  sub_class_refl : "(s \<sqsubseteq>\<^bsub>(H)\<^esub> s)" 
  unfolding sub_class_def
  by simp
    
text{* A manner to compute the subclass relationship effectively gives the following lemma: *}    
lemma  sub_class_trans_comp : 
    "(s \<sqsubseteq>\<^bsub>(H)\<^esub> t) = (if class_name H = s 
                      then \<exists> s'\<in> set(map class_name (subclasses H)). (s' \<sqsubseteq>\<^bsub>(H)\<^esub> t) 
                      else \<exists> H'\<in> set(subclasses H). (s \<sqsubseteq>\<^bsub>(H')\<^esub> t) )"    
proof(induct H) print_cases
  case (class\<^sub>T n subs attrs)
  then show ?case (* using class\<^sub>T.hyps *)  apply auto
    sorry
qed

    
subsection{* Fundamental search and replacement operations in a hierarchy *}    
    
fun replace_class_hierarchy :: "((class_hierarchy \<Rightarrow> class_hierarchy) \<times> class_hierarchy) \<Rightarrow>
                                 cid \<Rightarrow> 
                                 class_hierarchy \<Rightarrow> 
                                 class_hierarchy" ("(_)[_\\_]" [80,80,80]80)
  where "(C,class\<^sub>T cid' subs attrs ents) [cid \\ H'] = (if cid = cid' 
                                                        then C H'
                                                        else C(class\<^sub>T cid' 
                                                                      (map (\<lambda>X. (\<lambda>x. x, X) [cid \\ H']) subs)                                                                     attrs ents))"
 
    
fun get_class :: "cid \<Rightarrow> class_hierarchy \<Rightarrow> (attribute_env \<times> entity_env \<times> class_hierarchy)option" 
  where "get_class cid (class\<^sub>T c_name subc attrs comps)  = 
              (if cid = c_name then Some([],[],(class\<^sub>T c_name subc attrs comps))
               else (case filter (\<lambda>X. X \<noteq> None) (map (get_class cid) subc) of
                       [] \<Rightarrow> None 
                      | (Some(x,y,H) # _) \<Rightarrow> Some(attrs@x,comps@y,H)))"
     

subsection{* Objects  and States *}    
type_synonym  object = "cid \<times> attribute_env \<times> (oid \<times> cid) list"
type_synonym  state = "oid \<rightharpoonup> object"

fun remove_overrides :: "('\<alpha> \<Rightarrow> '\<beta>) \<Rightarrow> '\<alpha> list \<Rightarrow> '\<alpha> list" 
  where "remove_overrides f [] = []"
       |"remove_overrides f (a#R) = (if f a \<in> set(map f R) then remove_overrides f R
                                                           else a # (remove_overrides f R))" 


subsection{* Code-Generation *}    

code_printing
    type_constructor prod \<rightharpoonup> (SML) infix 2 "*"
  | constant         Pair \<rightharpoonup> (SML) "!((_),/ (_))"
     

code_printing 
    type_constructor  bool       \<rightharpoonup> (SML)    "bool"
  | constant          True       \<rightharpoonup> (SML)    "true"
  | constant          False      \<rightharpoonup> (SML)    "false"
  | constant         "HOL.conj"  \<rightharpoonup> (SML)    infix 1 "_ andalso _"


(* todo: checker for "validity" of an object wrt to its class description *)
  
    
export_code  mt  classes all_attributes all_entities remove_overrides
             (* replace_class_hierarchy get_class   extend_class_hierarchy *) in SML    
module_name MOF file "MOF.sml"                  
         

(* Hhm, a slightly more pragmatic approach to document types ... *)

   
    
end
  