theory Attributes
  imports "../../ontologies/Conceptual"
begin


text*[dfgdfg::B, B.x = "''f''", y = "[''s'']"]\<open> sdfsdfs sdfsdf sdfsdf @{thm refl} \<close> 

(*
text*[dfgdfg2::C, C.z = "None"]\<open> sdfsdfs sdfsdf sdfsdf @{thm refl} \<close> 
*)

text\<open> @{docitem_ref \<open>dfgdfg\<close>} \<close>

print_doc_classes

print_doc_items

ML\<open>  

val ({tab = x, ...},y)= DOF_core.get_data @{context};
Symtab.dest x;
Symtab.dest y;
\<close>
term "A.x (undefined\<lparr>A.x := 3\<rparr>)"
term "B.x ((undefined::C)\<lparr>B.y := [''sdf'']\<rparr>)"
term "C.z ((undefined::C)\<lparr>B.y := [''sdf'']\<rparr>)"

ML\<open>
val SOME {def_occurrence = "Conceptual.A", long_name = "Conceptual.A.x", typ = t, def_pos} 
    = DOF_core.get_attribute_info  "Conceptual.A" "x" @{theory};
DOF_core.get_attribute_info  "Conceptual.B" "x" @{theory};
DOF_core.get_attribute_info  "Conceptual.B" "y" @{theory};
DOF_core.get_attribute_info  "Conceptual.C" "x" @{theory};
val SOME {def_occurrence = "Conceptual.C", long_name = "Conceptual.B.y", typ = t', def_pos}
    = DOF_core.get_attribute_info  "Conceptual.C" "y" @{theory};
    (* this is the situation where an attribute is defined in C, but due to inheritance
       from B, where it is firstly declared which results in a different long_name. *)
DOF_core.get_attribute_info  "Conceptual.C" "z" @{theory};
\<close>




ML\<open>
DOF_core.get_value_local "sdf" @{context};
DOF_core.get_value_local "sdfg" @{context};
DOF_core.get_value_local "xxxy" @{context};
DOF_core.get_value_local "dfgdfg" @{context};
\<close>

ML\<open>val s =  map HOLogic.dest_string (HOLogic.dest_list @{docitem_attr y::dfgdfg}) \<close>

(* separate checking and term construction ?*)

ML\<open>val Type(s,t) = @{typ "'a list"}; 
   val tt = @{term "(undefined::B)\<lparr>B.x := '''' , B.y := []\<rparr>"};
   val tt' =  AnnoTextelemParser.infer_type  @{theory} tt;
   val tt'' = Sign.certify_term @{theory} tt;
  \<close>

ML\<open>Variable.names_of @{context};
Name.is_bound\<close>

ML\<open>
fun calc_update_term thy cid_long (S:(string * Position.T * string * term)list) term = 
    let val cid_ty = AnnoTextelemParser.cid_2_cidType cid_long 
        val count = Unsynchronized.ref (0);
        fun incr () = Unsynchronized.inc count
        val generalize_term =  let val n = incr () 
                               in Term.map_types (AnnoTextelemParser.generalize_typ n) end
        fun read_assn (lhs, pos, opr, rhs) term =
            let val info_opt = DOF_core.get_attribute_info cid_long 
                                       (Long_Name.base_name lhs) thy
                val (ln,lnt,lnu,lnut) = case info_opt of 
                                           NONE => error ("unknown attribute: " ^Long_Name.base_name lhs^
                                                          " in class: "^cid_long)
                                        |  SOME{long_name, typ, ...} => (long_name, typ, 
                                                                         long_name ^"_update",
                                                                         (typ --> typ) --> cid_ty --> cid_ty)
                val _ = if Long_Name.base_name lhs = lhs orelse ln = lhs then ()
                        else error("illegal notation for attribute of "^cid_long)
                fun join (ttt as @{typ "int"}) 
                         = Const (@{const_name "plus"}, ttt --> ttt --> ttt)
                   |join (ttt as @{typ "string"}) 
                         = Const (@{const_name "append"}, ttt --> ttt --> ttt)
                   |join (ttt as Type(@{type_name "set"},_)) 
                         = Const (@{const_name "sup"}, ttt --> ttt --> ttt)
                   |join (ttt as Type(@{type_name "list"},_)) 
                         = Const (@{const_name "append"}, ttt --> ttt --> ttt)
                   |join _ = error("implicit fusion operation not defined for attribute: "^ lhs)
                 (* could be extended to bool, map, multisets, ... *)
             in case opr of 
                  "=" => Const(lnu,lnut) 
                         $ Abs ("uu_", lnt,   generalize_term    rhs) 
                         $ term
                | "+=" => Const(lnu,lnut) 
                         $ Abs ("uu_", lnt, join lnt $ (Bound 0) $ (* generalize_term *) rhs) 
                         $ term
                | _ => error "corrupted syntax - oops - this should not occur" 
             end   
     in (* AnnoTextelemParser.infer_type thy*) (fold read_assn S term) end
\<close>
ML\<open>val t = @{term "Conceptual.B.y_update"}\<close>
declare [[ML_print_depth=30]]

ML\<open>;
@{theory};
open Sign;
Sign.typ_match;

\<close>


ML\<open>
val Type("List.list",[S]) = @{typ "('a) list"};
val ttt = Type("List.list",[TVar(("'a",0),@{sort "type"})]);
(* hint : the antiquotation 'typ' throws an exception for scheatic variables.... *)
 
Type.could_unify;
val tyenv = Type.typ_match (Sign.tsig_of @{theory}) 
               (ttt, @{typ "int list"})
               (Vartab.empty);
val tyenv = Sign.typ_match ( @{theory}) 
               (ttt, @{typ "int list"})
               (Vartab.empty);            
Vartab.dest tyenv;\<close>
ML\<open>

fun get_attribute_defaults (* long*)cid thy = 
    let val attrS = flat(map snd (DOF_core.get_attributes cid thy))
        fun trans (_,_,NONE) = NONE
           |trans (na,ty,SOME def) =SOME(na,ty, def)
    in  map_filter trans attrS end

val cid_long = "Conceptual.B"
val attr_name = "dfgdfg"
val thy = @{theory};
Thm.generalize;
Term_Subst.generalize;

val XXX = DOF_core.get_value_global attr_name thy

val S = get_attribute_defaults cid_long thy;
fun conv (na, _ (* ty *), term) = (Binding.name_of na, Binding.pos_of na, "=", term);
val tt = calc_update_term @{theory} cid_long (map conv S) 
            (the(DOF_core.get_value_global attr_name thy));
\<close>
ML\<open>
AnnoTextelemParser.infer_type @{theory}  tt;
\<close>

ML\<open> val t = @{term "None"} 
    val Const(s,tt) = t
    val Type(m,[TFree(d,s)]) = tt
  \<close>

end