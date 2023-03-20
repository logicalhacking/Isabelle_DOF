theory Very_Deep_Interpretation
  imports "Isabelle_DOF.Isa_COL"
          Metalogic_ProofChecker.ProofTerm

begin

subsection\<open> Syntax \<close>

\<comment> \<open>and others in the future : file, http, thy, ...\<close> 

(* Delete shallow interpretation notations (mixfixes) of the term anti-quotations,
  so we can use them for the deep interpretation *)
no_notation "Isabelle_DOF_typ" ("@{typ _}")
no_notation "Isabelle_DOF_term" ("@{term _}")
no_notation "Isabelle_DOF_thm" ("@{thm _}")
no_notation "Isabelle_DOF_file" ("@{file _}")
no_notation "Isabelle_DOF_thy" ("@{thy _}")
no_notation "Isabelle_DOF_docitem" ("@{docitem _}")
no_notation "Isabelle_DOF_docitem_attr" ("@{docitemattr (_) :: (_)}")
no_notation "Isabelle_DOF_trace_attribute" ("@{trace-attribute _}")

consts Isabelle_DOF_typ :: "string \<Rightarrow> typ" ("@{typ _}")
consts Isabelle_DOF_term :: "string \<Rightarrow> term" ("@{term _}")
datatype "thm" = Isabelle_DOF_thm string ("@{thm _}") | Thm_content ("proof":proofterm)
datatype "thms_of" = Isabelle_DOF_thms_of string ("@{thms-of _}")
datatype "file" = Isabelle_DOF_file string  ("@{file _}")
datatype "thy" = Isabelle_DOF_thy string  ("@{thy _}")
consts Isabelle_DOF_docitem      :: "string \<Rightarrow> 'a"                ("@{docitem _}")
datatype "docitem_attr" = Isabelle_DOF_docitem_attr string  string ("@{docitemattr (_) :: (_)}")
consts Isabelle_DOF_trace_attribute :: "string \<Rightarrow> (string * string) list" ("@{trace-attribute _}")

subsection\<open> Semantics \<close>

ML\<open>
structure ISA_core = 
struct

fun check_path check_file ctxt dir (name, pos) =
  let
    val _ = Context_Position.report ctxt pos (Markup.language_path true); (* TODO: pos should be 
                                                                                   "lifted" to 
                                                                                   type source *)

    val path = Path.append dir (Path.explode name) handle ERROR msg => ISA_core.err msg pos;
    val _ = Path.expand path handle ERROR msg => ISA_core.err msg pos;
    val _ = Context_Position.report ctxt pos (Markup.path (Path.implode_symbolic path));
    val _ =
      (case check_file of
        NONE => path
      | SOME check => (check path handle ERROR msg => ISA_core.err msg pos));
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
                                  NONE => ISA_core.err ("No Theorem:" ^name) pos
                                | SOME X => X
  in   ML_isa_check_generic check thy (term, pos) end


fun ML_isa_check_file thy (term, _, pos) _ =
  let fun check thy (name, pos) = check_path (SOME File.check_file) 
                                             (Proof_Context.init_global thy) 
                                             (Path.current) 
                                             (name, pos);
  in  ML_isa_check_generic check thy (term, pos) end;

fun ML_isa_id thy (term,pos) = SOME term


fun ML_isa_check_docitem thy (term, req_ty, pos) _ =
  let fun check thy (name, _) s =
            let val DOF_core.Instance {cid,...} =
                                              DOF_core.get_instance_global name thy
                val ns = DOF_core.get_instances (Proof_Context.init_global thy)
                               |> Name_Space.space_of_table 
                val {pos=pos', ...} = Name_Space.the_entry ns name
                val ctxt = (Proof_Context.init_global thy)
                val req_class = case req_ty of 
                                    \<^Type>\<open>fun _ T\<close> => DOF_core.typ_to_cid T
                                  | _ => error("can not infer type for: "^ name)
            in if cid <> DOF_core.default_cid 
                  andalso not(DOF_core.is_subclass ctxt cid req_class)
               then error("reference ontologically inconsistent: "
                          ^cid^" vs. "^req_class^ Position.here pos')
               else ()
            end
  in  ML_isa_check_generic check thy (term, pos) end


fun ML_isa_check_trace_attribute thy (term, _, pos) s =
  let
    val oid = (HOLogic.dest_string term
                  handle TERM(_,[t]) => error ("wrong term format: must be string constant: " 
                                               ^ Syntax.string_of_term_global thy t ))
    val _ = DOF_core.get_instance_global oid thy
  in SOME term end

fun ML_isa_elaborate_generic (_:theory) isa_name ty term_option _ =
  case term_option of
      NONE => error("Wrong term option. You must use a defined term")
    | SOME term => Const (isa_name, ty) $ term

fun reify_typ (Type (s, typ_list)) =
      \<^Const>\<open>Ty\<close> $ HOLogic.mk_literal s $ HOLogic.mk_list \<^Type>\<open>typ\<close> (map reify_typ typ_list)
  | reify_typ (TFree (name, sort)) =
      \<^Const>\<open>Tv\<close> $(\<^Const>\<open>Free\<close> $ HOLogic.mk_literal name)
      $ (HOLogic.mk_set \<^typ>\<open>class\<close> (map HOLogic.mk_literal sort))
  | reify_typ (TVar (indexname, sort)) =
      let val (name, index_value) = indexname
      in  \<^Const>\<open>Tv\<close>
          $ (\<^Const>\<open>Var\<close>
             $ HOLogic.mk_prod (HOLogic.mk_literal name, HOLogic.mk_number \<^Type>\<open>int\<close> index_value))
          $ (HOLogic.mk_set \<^typ>\<open>class\<close> (map HOLogic.mk_literal sort)) end

fun ML_isa_elaborate_typ (thy:theory) _ _ term_option _ =
  case term_option of
      NONE => error("Wrong term option. You must use a defined term")
    | SOME term => let 
                     val typ_name = HOLogic.dest_string term
                     val typ = Syntax.read_typ_global thy typ_name
                   in reify_typ typ end

fun reify_term (Const (name, typ)) =\<^Const>\<open>Ct\<close> $ HOLogic.mk_literal name $ reify_typ typ
  | reify_term (Free (name, typ)) =
      \<^Const>\<open>Fv\<close> $ (\<^Const>\<open>Free\<close> $ HOLogic.mk_literal name) $ reify_typ typ
  | reify_term (Var (indexname, typ)) =
      let val (name, index_value) = indexname
      in  \<^Const>\<open>Fv\<close>
          $ (\<^Const>\<open>Var\<close>
             $ HOLogic.mk_prod (HOLogic.mk_literal name, HOLogic.mk_number \<^Type>\<open>int\<close> index_value))
          $ reify_typ typ end
  | reify_term (Bound i) = \<^Const>\<open>Bv\<close> $ HOLogic.mk_nat i
  | reify_term (Abs (_, typ, term)) = \<^Const>\<open>Abs\<close> $ reify_typ typ $ reify_term term
  | reify_term (Term.$ (t1, t2)) = \<^Const>\<open>App\<close> $ reify_term t1 $ reify_term t2

fun ML_isa_elaborate_term (thy:theory) _ _ term_option _ =
  case term_option of
      NONE => error("Wrong term option. You must use a defined term")
    | SOME term => let 
                     val term_name = HOLogic.dest_string term
                     val term = Syntax.read_term_global thy term_name
                   in reify_term term end

fun reify_proofterm (PBound i) =\<^Const>\<open>PBound\<close> $ (HOLogic.mk_nat i)
  | reify_proofterm (Abst (_, typ_option, proof)) =
      \<^Const>\<open>Abst\<close> $ reify_typ (the typ_option) $ reify_proofterm proof
  | reify_proofterm (AbsP (_, term_option, proof)) =
      \<^Const>\<open>AbsP\<close> $ reify_term (the term_option) $ reify_proofterm proof
  | reify_proofterm (op % (proof, term_option)) =
      \<^Const>\<open>Appt\<close> $ reify_proofterm proof $ reify_term (the term_option)
  | reify_proofterm (op %% (proof1, proof2)) =
      \<^Const>\<open>AppP\<close> $ reify_proofterm proof1 $ reify_proofterm proof2
  | reify_proofterm (Hyp term) = \<^Const>\<open>Hyp\<close> $ (reify_term term)
  | reify_proofterm (PAxm (_, term, typ_list_option)) =
      let 
          val tvars = rev (Term.add_tvars term [])
          val meta_tvars = map (fn ((name, index_value), sort) =>
                HOLogic.mk_prod
                  (\<^Const>\<open>Var\<close>                    
                   $ HOLogic.mk_prod
                      (HOLogic.mk_literal name, HOLogic.mk_number \<^Type>\<open>int\<close> index_value)
                       , HOLogic.mk_set \<^typ>\<open>class\<close> (map HOLogic.mk_literal sort))) tvars
          val meta_typ_list = 
            HOLogic.mk_list @{typ "tyinst"} (map2 (fn x => fn y => HOLogic.mk_prod (x, y))
                                              meta_tvars (map reify_typ (the typ_list_option)))
      in \<^Const>\<open>PAxm\<close> $ reify_term term $ meta_typ_list end
  | reify_proofterm (PClass (typ, class)) =
      \<^Const>\<open>OfClass\<close> $ reify_typ typ $ HOLogic.mk_literal class
  | reify_proofterm (PThm ({prop = prop, types = types, ...}, _)) =
      let
        val tvars = rev (Term.add_tvars prop [])
        val meta_tvars = map (fn ((name, index_value), sort) =>
                HOLogic.mk_prod
                  (\<^Const>\<open>Var\<close>                    
                  $ HOLogic.mk_prod
                      (HOLogic.mk_literal name, HOLogic.mk_number \<^Type>\<open>int\<close> index_value)
                  , HOLogic.mk_set \<^typ>\<open>class\<close> (map HOLogic.mk_literal sort))) tvars
        val meta_typ_list = 
            HOLogic.mk_list \<^typ>\<open>tyinst\<close> (map2 (fn x => fn y => HOLogic.mk_prod (x, y))
                                          meta_tvars (map reify_typ (the types)))
      in \<^Const>\<open>PAxm\<close> $ reify_term prop $ meta_typ_list end

fun ML_isa_elaborate_thm (thy:theory) _ _ term_option pos =
  case term_option of
      NONE => ISA_core.err ("Malformed term annotation") pos
    | SOME term =>
        let
          val thm_name = HOLogic.dest_string term
          val _ = writeln ("In ML_isa_elaborate_thm thm_name: " ^ \<^make_string> thm_name)
          val thm = Proof_Context.get_thm (Proof_Context.init_global thy) thm_name
          val _ = writeln ("In ML_isa_elaborate_thm thm: " ^ \<^make_string> thm)
          val body = Proofterm.strip_thm_body (Thm.proof_body_of thm);
          val prf = Proofterm.proof_of body;
          (* Proof_Syntax.standard_proof_of reconstructs the proof and seems to rewrite
             the option arguments (with a value NONE) of the proof datatype constructors,
             at least for PAxm, with "SOME (typ/term)",
             allowing us the use the projection function "the".
             Maybe the function can deal with
             all the option types of the proof datatype constructors *)
          val proof = Proof_Syntax.standard_proof_of
                                   {full = true, expand_name = Thm.expand_name thm} thm
          val _ = writeln ("In ML_isa_elaborate_thm proof: " ^ \<^make_string> proof)
          (* After a small discussion with Simon Roßkopf, It seems preferable to use
             Thm.reconstruct_proof_of instead of Proof_Syntax.standard_proof_of
             whose operation is not well known.
             Thm.reconstruct_proof_of seems sufficient to have a reifiable PAxm
             in the metalogic. *)
          val proof' = Thm.reconstruct_proof_of thm 
        (*in \<^Const>\<open>Thm_content\<close> $ reify_proofterm prf end*)        
        (*in \<^Const>\<open>Thm_content\<close> $ reify_proofterm proof end*)
        in \<^Const>\<open>Thm_content\<close> $ reify_proofterm proof end


fun ML_isa_elaborate_thms_of (thy:theory) _ _ term_option pos =
  case term_option of
      NONE => ISA_core.err ("Malformed term annotation") pos
    | SOME term =>
        let
          val thm_name = HOLogic.dest_string term
          val thm = Proof_Context.get_thm (Proof_Context.init_global thy) thm_name
          val body = Proofterm.strip_thm_body (Thm.proof_body_of thm)
          val all_thms_name = Proofterm.fold_body_thms (fn {name, ...} => insert (op =) name) [body] []
          (*val all_thms = map (Proof_Context.get_thm (Proof_Context.init_global thy)) all_thms_name*)
          (*val all_proofs = map (Proof_Syntax.standard_proof_of
                                   {full = true, expand_name = Thm.expand_name thm}) all_thms*)
        (*in HOLogic.mk_list \<^Type>\<open>thm\<close> (map (fn proof => \<^Const>\<open>Thm_content\<close> $ reify_proofterm proof) all_proofs) end*)
        in HOLogic.mk_list \<^typ>\<open>string\<close> (map HOLogic.mk_string all_thms_name) end

fun ML_isa_elaborate_trace_attribute (thy:theory) _ _ term_option pos =
case term_option of
    NONE => ISA_core.err ("Malformed term annotation") pos
  | SOME term => 
      let
        val oid = HOLogic.dest_string term
        val traces = ISA_core.compute_attr_access (Context.Theory thy) "trace" oid NONE pos
        fun conv (\<^Const>\<open>Pair \<^typ>\<open>doc_class rexp\<close> \<^typ>\<open>string\<close>\<close>
                    $ (\<^Const>\<open>Atom \<^typ>\<open>doc_class\<close>\<close> $ (\<^Const>\<open>mk\<close> $ s)) $ S) =
          let val s' =  DOF_core.get_onto_class_name_global (HOLogic.dest_string s) thy 
          in \<^Const>\<open>Pair \<^typ>\<open>string\<close> \<^typ>\<open>string\<close>\<close> $ HOLogic.mk_string s' $ S end
        val traces' = map conv (HOLogic.dest_list traces)
      in HOLogic.mk_list \<^Type>\<open>prod \<^typ>\<open>string\<close> \<^typ>\<open>string\<close>\<close> traces' end

end; (* struct *)

\<close>

ML\<open>
val ty1 = ISA_core.reify_typ @{typ "int"}
val ty2 = ISA_core.reify_typ @{typ "int \<Rightarrow> bool"}
val ty3 = ISA_core.reify_typ @{typ "prop"}
val ty4 = ISA_core.reify_typ @{typ "'a list"}
\<close>

ML\<open>
val t1 = ISA_core.reify_term @{term "1::int"}
val t2 = ISA_core.reify_term @{term "\<lambda>x. x = 1"}
val t3 = ISA_core.reify_term @{term "[2, 3::int]"}
\<close>

subsection\<open> Isar - Setup\<close>
(* Isa_transformers declaration for Isabelle_DOF term anti-quotations (typ, term, thm, etc.).
   They must be declared in the same theory file as the one of the declaration
   of Isabelle_DOF term anti-quotations !!! *)
setup\<open>
[(\<^type_name>\<open>thm\<close>, ISA_core.ML_isa_check_thm, ISA_core.ML_isa_elaborate_thm)
 , (\<^type_name>\<open>thms_of\<close>, ISA_core.ML_isa_check_thm, ISA_core.ML_isa_elaborate_thms_of)
 , (\<^type_name>\<open>file\<close>, ISA_core.ML_isa_check_file, ISA_core.ML_isa_elaborate_generic)]
|> fold (fn (n, check, elaborate) => fn thy =>
let val ns = Sign.tsig_of thy |> Type.type_space
    val name = n
    val {pos, ...} = Name_Space.the_entry ns name
    val bname = Long_Name.base_name name
    val binding = Binding.make (bname, pos)
                   |> Binding.prefix_name DOF_core.ISA_prefix
                   |> Binding.prefix false bname
in  DOF_core.add_isa_transformer binding ((check, elaborate) |> DOF_core.make_isa_transformer) thy
end)
#>
([(\<^const_name>\<open>Isabelle_DOF_typ\<close>, ISA_core.ML_isa_check_typ, ISA_core.ML_isa_elaborate_typ)
  ,(\<^const_name>\<open>Isabelle_DOF_term\<close>, ISA_core.ML_isa_check_term, ISA_core.ML_isa_elaborate_term)
  ,(\<^const_name>\<open>Isabelle_DOF_docitem\<close>,
      ISA_core.ML_isa_check_docitem, ISA_core.ML_isa_elaborate_generic)
  ,(\<^const_name>\<open>Isabelle_DOF_trace_attribute\<close>,
      ISA_core.ML_isa_check_trace_attribute, ISA_core.ML_isa_elaborate_trace_attribute)]
|> fold (fn (n, check, elaborate) => fn thy =>
let val ns = Sign.consts_of thy |> Consts.space_of
    val name = n
    val {pos, ...} = Name_Space.the_entry ns name
    val bname =  Long_Name.base_name name
    val binding = Binding.make (bname, pos)
in  DOF_core.add_isa_transformer binding ((check, elaborate) |> DOF_core.make_isa_transformer) thy
end))
\<close>
end