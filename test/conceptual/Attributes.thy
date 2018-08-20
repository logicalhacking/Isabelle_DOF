theory Attributes
  imports "../../ontologies/Conceptual"
begin


text*[dfgdfg::B, y = "[''sdf'']"]\<open> sdfsdfs sdfsdf sdfsdf @{thm refl}}\<close>

text\<open> @{docitem_ref \<open>dfgdfg\<close>} }\<close>

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
val SOME {def_occurrence = "Conceptual.A", long_name = "Conceptual.A.x", typ = t} 
    = DOF_core.get_attribute_info  "Conceptual.A" "x" @{theory};
DOF_core.get_attribute_info  "Conceptual.B" "x" @{theory};
DOF_core.get_attribute_info  "Conceptual.B" "y" @{theory};
DOF_core.get_attribute_info  "Conceptual.C" "x" @{theory};
val SOME {def_occurrence = "Conceptual.C", long_name = "Conceptual.B.y", typ = t'}
    = DOF_core.get_attribute_info  "Conceptual.C" "y" @{theory};
    (* this is the situation where an attribute is defined in C, but due to inheritance
       from B, where it is firstly declared which results in a different long_name. *)
DOF_core.get_attribute_info  "Conceptual.C" "z" @{theory};
\<close>


ML\<open>
DOF_core.get_default_local "Conceptual.A" "x" @{context};

DOF_core.get_default_local "Conceptual.B" "x" @{context};
DOF_core.get_default_local "Conceptual.B" "y" @{context};

DOF_core.get_default_local "Conceptual.C" "x" @{context};
DOF_core.get_default_local "Conceptual.C" "y" @{context};
DOF_core.get_default_local "Conceptual.C" "z" @{context};
\<close>

ML\<open>
DOF_core.get_value_local "sdf" @{context};
DOF_core.get_value_local "sdfg" @{context};
DOF_core.get_value_local "xxxy" @{context};
DOF_core.get_value_local "dfgdfg" @{context};
\<close>

ML\<open>val s =  map HOLogic.dest_string (HOLogic.dest_list @{docitem_attr y::dfgdfg}) \<close>

(* separate checking and term construction ?*)

ML\<open>val Type(s,t) = @{typ "'a list"}; fold\<close>

ML\<open>
fun calc_update_term thy cid_long (S:(((string * Position.T) * string) * string)list) term = 
    let val count = Unsynchronized.ref (0 - 1);
        fun incr () = Unsynchronized.inc count
        val generalize_term =  let val n = incr () 
                               in Term.map_types (AnnoTextelemParser.generalize_typ n) end
        fun read_assn (((lhs, pos), opr), rhs) tt =
            let val info_opt = DOF_core.get_attribute_info cid_long 
                                       (Long_Name.base_name lhs) thy
                val (ln,lnt,lnu,lnut) = case info_opt of 
                                           NONE => error ("unknown attribute in class: "^cid_long)
                                        |  SOME{long_name, typ, ...} => (long_name, typ, 
                                                                         long_name ^"_update",
                                                                         typ --> dummyT --> dummyT)
                val _ = if Long_Name.base_name lhs = lhs orelse ln = lhs then ()
                        else error("illegal notation for attribute of "^cid_long)
                val rhs' = Syntax.read_term_global thy rhs |> generalize_term
                fun join (ttt as @{typ "int"}) 
                         = Const ("Groups.plus_class.plus", ttt --> ttt --> ttt)
                   |join (ttt as @{typ "string"}) 
                         = Const ("List.append", ttt --> ttt --> ttt)
                   |join (ttt as Type("Set.set",_)) 
                         = Const ("Lattices.sup_class.sup", ttt --> ttt --> ttt)
                   |join (ttt as Type("List.list",_)) 
                         = Const ("List.append", ttt --> ttt --> ttt)
                   |join _ = error("implicit fusion operation not defined on attribute: "^ lhs)
                 (* could be extended to bool, map, multisets, ... *)
             in case opr of 
                  "=" => Const(lnu,lnut) 
                         $ Abs ("uu_", lnt, rhs') 
                         $ tt
                | "+=" => Const(lnu,lnut) 
                         $ Abs ("uu_", lnt, join lnt $ (Bound 0) $ rhs') 
                         $ tt 
             end   
     in fold read_assn S term end
\<close>

end