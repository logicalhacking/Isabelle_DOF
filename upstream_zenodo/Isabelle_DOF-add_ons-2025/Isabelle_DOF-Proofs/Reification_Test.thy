theory Reification_Test
  imports "Isabelle_DOF-Proofs.Very_Deep_DOF"

begin

ML\<open>
val ty1 = Meta_ISA_core.reify_typ @{typ "int"}
val ty2 = Meta_ISA_core.reify_typ @{typ "int \<Rightarrow> bool"}
val ty3 = Meta_ISA_core.reify_typ @{typ "prop"}
val ty4 = Meta_ISA_core.reify_typ @{typ "'a list"}
\<close>

term*\<open>@{typ \<open>int\<close>}\<close>
value*\<open>@{typ \<open>int\<close>}\<close>
value*\<open>@{typ \<open>int \<Rightarrow> bool\<close>}\<close>
term*\<open>@{typ \<open>prop\<close>}\<close>
value*\<open>@{typ \<open>prop\<close>}\<close>
term*\<open>@{typ \<open>'a list\<close>}\<close>
value*\<open>@{typ \<open>'a list\<close>}\<close>

ML\<open>
val t1 = Meta_ISA_core.reify_term @{term "1::int"}
val t2 = Meta_ISA_core.reify_term @{term "\<lambda>x. x = 1"}
val t3 = Meta_ISA_core.reify_term @{term "[2, 3::int]"}
\<close>
term*\<open>@{term \<open>1::int\<close>}\<close>
value*\<open>@{term \<open>1::int\<close>}\<close>
term*\<open>@{term \<open>\<lambda>x. x = 1\<close>}\<close>
value*\<open>@{term \<open>\<lambda>x. x = 1\<close>}\<close>
term*\<open>@{term \<open>[2, 3::int]\<close>}\<close>
value*\<open>@{term \<open>[2, 3::int]\<close>}\<close>

prf refl
full_prf refl

term*\<open>@{thm \<open>HOL.refl\<close>}\<close>
value*\<open>proof @{thm \<open>HOL.refl\<close>}\<close>
value*\<open>proof @{thm \<open>HOL.refl\<close>}\<close>
value*\<open>depth (proof @{thm \<open>HOL.refl\<close>})\<close>
value*\<open>size (proof @{thm \<open>HOL.refl\<close>})\<close>
value*\<open>fv_Proof (proof @{thm \<open>HOL.refl\<close>})\<close>
term*\<open>@{thms-of \<open>HOL.refl\<close>}\<close>
value*\<open>@{thms-of \<open>HOL.refl\<close>}\<close>

ML\<open>
val t_schematic = TVar(("'a",0), [])
val t = @{term "Tv (Var (STR '''a'', 0)) {}"}
val rt_schematic = Meta_ISA_core.reify_typ t_schematic
val true = rt_schematic = t
\<close>

lemma test : "A \<and> B \<longrightarrow> B \<and> A"
  by auto

lemma test2 : "A \<and> B \<Longrightarrow> B \<and> A"
  by auto

lemma test3: "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume "A \<and> B"
  then obtain B and A ..
  then show "B \<and> A" ..
qed

lemma test4:
  assumes "(A \<and> B)"
  shows "B \<and> A"
  apply (insert assms)
  by auto

lemma test_subst : "\<lbrakk>x = f x; odd(f x)\<rbrakk> \<Longrightarrow> odd x"
  by (erule ssubst)

inductive_set even' :: "nat set" where
    "0 \<in> even'"
  | "n \<in> even' \<Longrightarrow> (Suc (Suc n)) \<in> even'"

find_theorems name:"even'.induct"


(*lemma even_dvd : "n \<in> even' \<Longrightarrow> 2 dvd n"
proof(induct n)
  case 0 then show ?case by simp
next 
  case (Suc n) then show ?case
    apply (simp add: dvd_def)
    apply (rule_tac x ="Suc k" in exI)
    apply clarify*)

theorem "((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A"
proof
  assume "(A \<longrightarrow> B) \<longrightarrow> A"
  show A
  proof (rule classical)
    assume "\<not> A"
    have "A \<longrightarrow> B"
    proof
      assume A
      with \<open>\<not> A\<close> show B by contradiction
    qed
    with \<open>(A \<longrightarrow> B) \<longrightarrow> A\<close> show A ..
  qed
qed

(*lemma even_dvd : "n \<in> even' \<Longrightarrow> 2 dvd n"
using [[simp_trace]]
  apply (induct n)
   apply (subst even_zero)
  apply(rule TrueI)

  apply(simp)*)

lemma even_dvd : "n \<in> even' \<Longrightarrow> 2 dvd n"
  apply (erule even'.induct)
   apply (simp_all add: dvd_def)
  using [[simp_trace]]
  apply clarify
  find_theorems name:"_ = 2 * _"
  apply (rule_tac x ="Suc k" in exI)
using [[simp_trace]]
  apply simp
  done

(*
lemma even_dvd : "n \<in> even' \<Longrightarrow> 2 dvd n"
apply (induct_tac rule:even'.induct)*)

inductive ev :: " nat \<Rightarrow> bool " where
  ev0: " ev 0 " |
  evSS: " ev n \<Longrightarrow> ev (n + 2) "

fun evn :: " nat \<Rightarrow> bool " where
  " evn 0 = True " |
  " evn (Suc 0) = False " |
  " evn (Suc (Suc n)) = evn n "

(*lemma assumes a: " ev (Suc(Suc m)) " shows" ev m "
proof(induction  "Suc (Suc m)" arbitrary: " m " rule: ev.induct)*)

(*lemma " ev (Suc (Suc m)) \<Longrightarrow> ev m " 
proof(induction " Suc (Suc m) " arbitrary: " m " rule: ev.induct)
  case ev0
  then show ?case sorry
next
  case (evSS n)
  then show ?case sorry
qed*)

(* And neither of these can apply the induction *)
(*
lemma assumes a1: " ev n " and a2: " n = (Suc (Suc m)) " shows " ev m "
proof (induction " n " arbitrary: " m " rule: ev.induct)

lemma assumes a1: " n = (Suc (Suc m)) " and a2: "ev n " shows " ev m "
proof (induction " n " arbitrary: " m " rule: ev.induct)
*)

(* But this one can ?! *)
(*
lemma assumes a1: " ev n " and a2: " n = (Suc (Suc m)) " shows " ev m "
proof -
  from a1 and a2 show " ev m "
  proof (induction " n " arbitrary: " m " rule: ev.induct)
    case ev0
    then show ?case by simp
  next
    case (evSS n) thus ?case by simp
  qed
qed
*)

inductive_set even :: "int set" where
zero[intro!]: "0 \<in> even" |
plus[intro!]: "n \<in> even \<Longrightarrow> n+2 \<in> even " |
min[intro!]: "n \<in> even \<Longrightarrow> n-2 \<in> even "

lemma a : "2+2=4" by simp

lemma b : "(0::int)+2=2" by simp

lemma test_subst_2 : "4 \<in> even"
  apply (subst a[symmetric])
  apply (rule plus)
  apply (subst b[symmetric])
  apply (rule plus)
  apply (rule zero)
  done


(*lemma "\<lbrakk>P x y z; Suc x < y\<rbrakk> \<Longrightarrow> f z = x * y"
  (*using [[simp_trace]]*)
  (*apply (simp add: mult.commute)*)
  apply (subst mult.commute)
  apply (rule mult.commute [THEN ssubst])*)

datatype 'a seq = Empty | Seq 'a "'a seq"
find_consts name:"Reification_Test*seq*"
fun conc :: "'a seq \<Rightarrow> 'a seq \<Rightarrow> 'a seq"
where
  c1 :  "conc Empty ys = ys"
| c2 : "conc (Seq x xs) ys = Seq x (conc xs ys)"

lemma seq_not_eq : "Seq x xs \<noteq> xs"
using [[simp_trace]]
proof (induct xs arbitrary: x)
  case Empty
  show "Seq x Empty \<noteq> Empty" by simp
next
  case (Seq y ys)
  show "Seq x (Seq y ys) \<noteq> Seq y ys"
    using \<open>Seq y ys \<noteq> ys\<close> by simp
qed

lemma identity_conc : "conc xs Empty = xs"
  using [[simp_trace]]
  using[[simp_trace_depth_limit=8]]
  using [[unify_trace_simp]]
  using[[unify_trace_types]]
  using [[unify_trace_bound=0]]
  (* using [[simp_trace_new depth=10]] *)
  apply (induct xs)
   apply (subst c1)
   apply (rule refl)
  apply (subst c2)
  apply (rule_tac s="xs" and P="\<lambda>X. Seq x1 X = Seq x1 xs" in subst)
   apply (rule sym)
   apply assumption
  apply (rule refl)
  done

lemma imp_ex : "(\<exists>x. \<forall>y. P x y) \<longrightarrow> (\<forall>y. \<exists>x. P x y)"
  using [[simp_trace]]
  using[[simp_trace_depth_limit=8]]
  apply (auto)
done

lemma length_0_conv' [iff]: "(length [] = 0)"
  apply (subst List.list.size(3))
  apply (rule refl)
  done

lemma cons_list : "a#xs = [a]@xs"
  using [[simp_trace]]
  apply (subst List.append.append_Cons)
  apply (subst List.append.append_Nil)
  apply (rule refl)
  done
lemma replacement: "\<lbrakk> a = b; c = d \<rbrakk> \<Longrightarrow> f a c = f b d"
apply (erule ssubst)+
apply (rule refl )
 done
lemma assoc_append : "k @ (l @ m) = (k @ l ) @ m"
apply (induct_tac k )
apply (subst append_Nil )+
apply (rule refl )
apply (subst append_Cons)
apply (subst append_Cons)
apply (subst append_Cons)
apply (rule_tac f ="Cons" in replacement)
apply (rule refl)
apply assumption
  done

lemma length_cons : "length (xs @ ys) = length xs + length ys"
  using [[simp_trace]]
  apply (subst List.length_append)
  apply (rule refl)
  done
lemma length_plus : "(length [a] + length xs = 0) = ([a] @ xs = [])"
  using [[simp_trace]]
  apply (subst List.list.size(4))
  apply (subst List.list.size(3))
  apply (subst Nat.add_Suc_right)
  apply (subst Groups.monoid_add_class.add.right_neutral)
  apply (subst Nat.plus_nat.add_Suc)
  apply (subst Groups.monoid_add_class.add.left_neutral)
apply (subst Nat.old.nat.distinct(2))
  by simp
lemma empty_list : "(length [] = 0) = ([] = []) = True"
  using [[simp_trace]]
  by simp
lemma TrueI: True
using [[simp_trace]]
  unfolding True_def
  by (rule refl)

lemma length_0_conv [iff]: "(length xs = 0) = (xs = [])"
  using [[simp_trace]]
  apply (induct xs)
   apply (subst List.list.size(3))
   apply(subst HOL.simp_thms(6))
   apply(subst HOL.simp_thms(6))
   apply(rule refl)

  apply (subst cons_list)
  apply (subst(2) cons_list)
  apply (subst length_cons)
  apply (subst length_plus)
  apply (subst HOL.simp_thms(6))
  apply (rule TrueI)
  done
(*by (induct xs) auto*)

find_theorems (50) name:"HOL.simp_thms"
find_theorems (50) name:"List.list*size"
find_theorems (50) name:"List.list*length"
find_theorems "_ @ _"
find_theorems (500) "List.length [] = 0"
find_theorems (550) "length _ = length _ + length _"


lemma identity_list : "xs @ [] = xs"
  using [[simp_trace]]
  using[[simp_trace_depth_limit=8]]
  using [[unify_trace_simp]]
  using[[unify_trace_types]]
  using [[unify_trace_bound=0]]
  apply (induct xs)
  apply (subst List.append_Nil2)
   apply (subst HOL.simp_thms(6))
  apply(rule TrueI)
  apply (subst List.append_Nil2)
  apply (subst HOL.simp_thms(6))
  apply(rule TrueI)
  done

lemma identity_list' : "xs @ [] = xs"
  using [[simp_trace]]
  using[[simp_trace_depth_limit=8]]
  using [[unify_trace_simp]]
  using[[unify_trace_types]]
  using [[unify_trace_bound=0]]
  (* using [[simp_trace_new depth=10]] *)
  apply (induct "length xs")
  apply (subst (asm) zero_reorient)
  apply(subst(asm) length_0_conv)
   apply (subst List.append_Nil2)
   apply (subst HOL.simp_thms(6))
  apply (rule TrueI)
     apply (subst List.append_Nil2)
  apply (subst HOL.simp_thms(6))
  apply (rule TrueI)
  done

lemma conj_test : "A \<and> B \<and> C \<longrightarrow> B \<and> A"
  apply (rule impI)
  apply (rule conjI)
  apply (drule conjunct2)
   apply (drule conjunct1)
   apply assumption
    apply (drule conjunct1)
  apply assumption
  done

declare[[show_sorts]]
declare[[ML_print_depth = 20]]

ML\<open>
val full = true
val thm = @{thm "test"}
val hyps = Thm.hyps_of thm
val prems = Thm.prems_of thm
val reconstruct_proof = Thm.reconstruct_proof_of thm
val standard_proof = Proof_Syntax.standard_proof_of
          {full = full, expand_name = Thm.expand_name thm} thm
val term_of_proof = Proof_Syntax.term_of_proof standard_proof
\<close>

lemma identity_conc' : "conc xs Empty = xs"
  using [[simp_trace]]
  using[[simp_trace_depth_limit=8]]
  using [[unify_trace_simp]]
  using[[unify_trace_types]]
  using [[unify_trace_bound=0]]
  (* using [[simp_trace_new depth=10]] *)
  apply (induct xs)
   apply (subst c1)
   apply (rule refl)
  apply (subst c2)
  apply (rule_tac s="xs" and P="\<lambda>X. Seq x1 X = Seq x1 xs" in subst)
   apply (rule sym)
   apply assumption
  apply (rule refl)
  done

declare[[show_sorts = false]]

ML\<open> (*See: *) \<^file>\<open>~~/src/HOL/Proofs/ex/Proof_Terms.thy\<close>\<close>
ML\<open>
  val thm = @{thm "identity_conc'"};

  (*proof body with digest*)
  val body = Proofterm.strip_thm_body (Thm.proof_body_of thm);

  (*proof term only*)
  val prf = Proofterm.proof_of body;

  (*clean output*)
  Pretty.writeln (Proof_Syntax.pretty_proof \<^context> prf);
  Pretty.writeln (Proof_Syntax.pretty_standard_proof_of \<^context> false thm);
  Pretty.writeln (Proof_Syntax.pretty_standard_proof_of \<^context> true thm);

  (*all theorems used in the graph of nested proofs*)
  val all_thms =
    Proofterm.fold_body_thms
      (fn {thm_name, ...} => insert (op =) thm_name) [body] [];
\<close>

term*\<open>@{thm \<open>Reification_Test.identity_conc\<close>}\<close>
value*\<open>proof @{thm \<open>Reification_Test.identity_conc\<close>}\<close>

lemma cons_list' : "a#xs = [a]@xs"
  using [[simp_trace]]
  apply (subst List.append.append_Cons)
  apply (subst List.append.append_Nil)
  apply (rule refl)
  done

ML\<open> (*See: *) \<^file>\<open>~~/src/HOL/Proofs/ex/Proof_Terms.thy\<close>\<close>
ML\<open>
  val thm = @{thm "cons_list'"};

  (*proof body with digest*)
  val body = Proofterm.strip_thm_body (Thm.proof_body_of thm);

  (*proof term only*)
  val prf = Proofterm.proof_of body;

  (*clean output*)
  Pretty.writeln (Proof_Syntax.pretty_proof \<^context> prf);
  Pretty.writeln (Proof_Syntax.pretty_standard_proof_of \<^context> false thm);
  Pretty.writeln (Proof_Syntax.pretty_standard_proof_of \<^context> true thm);

  (*all theorems used in the graph of nested proofs*)
  val all_thms =
    Proofterm.fold_body_thms
      (fn {thm_name, ...} => insert (op =) thm_name) [body] [];
\<close>

declare[[show_sorts = false]]
declare[[ML_print_depth = 20]]

ML\<open> (*See: *) \<^file>\<open>~~/src/HOL/Proofs/ex/Proof_Terms.thy\<close>\<close>
ML\<open>
  val thm = @{thm "test"};

  (*proof body with digest*)
  val body = Proofterm.strip_thm_body (Thm.proof_body_of thm);

  (*proof term only*)
  val prf = Proofterm.proof_of body;

  (*clean output*)
  Pretty.writeln (Proof_Syntax.pretty_proof \<^context> prf);
  Pretty.writeln (Proof_Syntax.pretty_standard_proof_of \<^context> false thm);
  Pretty.writeln (Proof_Syntax.pretty_standard_proof_of \<^context> true thm);

  (*all theorems used in the graph of nested proofs*)
  val all_thms =
    Proofterm.fold_body_thms
      (fn {thm_name, ...} => insert (op =) thm_name) [body] [];
\<close>

prf test
full_prf test
term*\<open>@{thm \<open>Reification_Test.test\<close>}\<close>
value*\<open>proof @{thm \<open>Reification_Test.test\<close>}\<close>
term*\<open>@{thms-of \<open>Reification_Test.test\<close>}\<close>
value*\<open>@{thms-of \<open>Reification_Test.test\<close>}\<close>

ML\<open> (*See: *) \<^file>\<open>~~/src/HOL/Proofs/ex/Proof_Terms.thy\<close>\<close>
ML\<open>
  val thm = @{thm test2};

  (*proof body with digest*)
  val body = Proofterm.strip_thm_body (Thm.proof_body_of thm);

  (*proof term only*)
  val prf = Proofterm.proof_of body;

  (*clean output*)
  Pretty.writeln (Proof_Syntax.pretty_standard_proof_of \<^context> false thm);
  Pretty.writeln (Proof_Syntax.pretty_standard_proof_of \<^context> true thm);

  (*all theorems used in the graph of nested proofs*)
  val all_thms =
    Proofterm.fold_body_thms
      (fn {thm_name, ...} => insert (op =) thm_name) [body] [];
\<close>

prf test2
full_prf test2
term*\<open>@{thm \<open>Reification_Test.test2\<close>}\<close>
value*\<open>proof @{thm \<open>Reification_Test.test2\<close>}\<close>

ML\<open> (*See: *) \<^file>\<open>~~/src/HOL/Proofs/ex/Proof_Terms.thy\<close>\<close>
ML\<open>
  val thm = @{thm test3};

  (*proof body with digest*)
  val body = Proofterm.strip_thm_body (Thm.proof_body_of thm);

  (*proof term only*)
  val prf = Proofterm.proof_of body;

  (*clean output*)
  Pretty.writeln (Proof_Syntax.pretty_standard_proof_of \<^context> false thm);
  Pretty.writeln (Proof_Syntax.pretty_standard_proof_of \<^context> true thm);

  (*all theorems used in the graph of nested proofs*)
  val all_thms =
    Proofterm.fold_body_thms
      (fn {thm_name, ...} => insert (op =) thm_name) [body] [];
\<close>

prf test3
full_prf test3
term*\<open>@{thm \<open>Reification_Test.test3\<close>}\<close>
value*\<open>@{thm \<open>Reification_Test.test3\<close>}\<close>

ML\<open> (*See: *) \<^file>\<open>~~/src/HOL/Proofs/ex/Proof_Terms.thy\<close>\<close>
ML\<open>
  val thm = @{thm test4};

  (*proof body with digest*)
  val body = Proofterm.strip_thm_body (Thm.proof_body_of thm);

  (*proof term only*)
  val prf = Proofterm.proof_of body;

  (*clean output*)
  Pretty.writeln (Proof_Syntax.pretty_standard_proof_of \<^context> false thm);
  Pretty.writeln (Proof_Syntax.pretty_standard_proof_of \<^context> true thm);

  (*all theorems used in the graph of nested proofs*)
  val all_thms =
    Proofterm.fold_body_thms
      (fn {thm_name, ...} => insert (op =) thm_name) [body] [];
\<close>

prf test4
full_prf test4
term*\<open>@{thm \<open>Reification_Test.test4\<close>}\<close>
value*\<open>@{thm \<open>Reification_Test.test4\<close>}\<close>

ML\<open> (*See: *) \<^file>\<open>~~/src/HOL/Proofs/ex/Proof_Terms.thy\<close>\<close>
ML\<open>
  val thm = @{thm Pure.symmetric};

  (*proof body with digest*)
  val body = Proofterm.strip_thm_body (Thm.proof_body_of thm);

  (*proof term only*)
  val prf = Proofterm.proof_of body;

  (*clean output*)
  Pretty.writeln (Proof_Syntax.pretty_standard_proof_of \<^context> false thm);
  Pretty.writeln (Proof_Syntax.pretty_standard_proof_of \<^context> true thm);

  (*all theorems used in the graph of nested proofs*)
  val all_thms =
    Proofterm.fold_body_thms
      (fn {thm_name, ...} => insert (op =) thm_name) [body] [];
\<close>

prf symmetric
full_prf symmetric
term*\<open>@{thm \<open>Pure.symmetric\<close>}\<close>
value*\<open>proof @{thm \<open>Pure.symmetric\<close>}\<close>

ML\<open>
val full = true
val thm = @{thm "Groups.minus_class.super"}
val standard_proof = Proof_Syntax.standard_proof_of
          {full = full, expand_name = Thm.expand_name thm} thm
val term_of_proof = Proof_Syntax.term_of_proof standard_proof
\<close>

ML\<open>
val thm = Proof_Context.get_thm \<^context> "Groups.minus_class.super"
val prop = Thm.prop_of thm
val proof = Thm.proof_of thm
\<close>

prf Groups.minus_class.super
full_prf Groups.minus_class.super
term*\<open>@{thm \<open>Groups.minus_class.super\<close>}\<close>
value*\<open>@{thm \<open>Groups.minus_class.super\<close>}\<close>

(*ML\<open>
val full = true
val thm = @{thm "Homotopy.starlike_imp_contractible"}
val standard_proof = Proof_Syntax.standard_proof_of
          {full = full, expand_name = Thm.expand_name thm} thm
val term_of_proof = Proof_Syntax.term_of_proof standard_proof
\<close>

ML\<open>
val thm = Proof_Context.get_thm \<^context> "Homotopy.starlike_imp_contractible"
val prop = Thm.prop_of thm
val proof = Thm.proof_of thm
\<close>

prf Homotopy.starlike_imp_contractible
full_prf Homotopy.starlike_imp_contractible
term*\<open>@{thm \<open>Homotopy.starlike_imp_contractible\<close>}\<close>
value*\<open>@{thm \<open>Homotopy.starlike_imp_contractible\<close>}\<close>*)

(* stefan bergofer phd thesis example proof construction 2.3.2 *)

lemma stefan_example : "(\<exists>x. \<forall>y. P x y) \<longrightarrow> (\<forall>y. \<exists>x. P x y)"
  apply (rule impI)
  apply(rule allI)
  apply (erule exE)
   apply(rule exI)
  apply(erule allE)
  apply (assumption)
  done

ML\<open> (*See: *) \<^file>\<open>~~/src/HOL/Proofs/ex/Proof_Terms.thy\<close>\<close>
ML\<open>
  val thm = @{thm stefan_example};

  (*proof body with digest*)
  val body = Proofterm.strip_thm_body (Thm.proof_body_of thm);

  (*proof term only*)
  val prf = Proofterm.proof_of body;

  (*clean output*)
  Pretty.writeln (Proof_Syntax.pretty_proof \<^context> prf);
  Pretty.writeln (Proof_Syntax.pretty_standard_proof_of \<^context> false thm);
  Pretty.writeln (Proof_Syntax.pretty_standard_proof_of \<^context> true thm);

  (*all theorems used in the graph of nested proofs*)
  val all_thms =
    Proofterm.fold_body_thms
      (fn {thm_name, ...} => insert (op =) thm_name) [body] [];
\<close>
ML\<open>
val thy = \<^theory>;
  val prf =
    Proof_Syntax.read_proof thy true false
      "mp \<cdot> _ \<cdot> _ \<bullet> (impI \<cdot> _ \<cdot> _ \<bullet> (conjI \<cdot> _ \<cdot> _ ))";
      (*"conjI \<cdot> _ \<cdot> _ ";*)
      (*"(\<^bold>\<lambda>(H: _) Ha: _. conjI \<cdot> _ \<cdot> _ \<bullet> Ha \<bullet> H)";*)
(*val t = Proofterm.reconstruct_proof thy \<^prop>\<open>(A \<longrightarrow> B) \<Longrightarrow> A \<Longrightarrow> B\<close> prf*)
(*  val thm =  
    Proofterm.reconstruct_proof thy \<^prop>\<open>A \<Longrightarrow> B\<close> prf
    |> Proof_Checker.thm_of_proof thy
    |> Drule.export_without_context
val pretty =  Pretty.writeln (Proof_Syntax.pretty_standard_proof_of \<^context> true thm);*)
\<close>

extract_type
  "typeof (Trueprop P) \<equiv> typeof P"

realizers
  impI (P, Q): "\<lambda>pq. pq"
    "\<^bold>\<lambda>(c: _) (d: _) P Q pq (h: _). allI \<cdot> _ \<bullet> c \<bullet> (\<^bold>\<lambda>x. impI \<cdot> _ \<cdot> _ \<bullet> (h \<cdot> x))"
find_consts name:"MinProof"

ML_val \<open>
  val thy = \<^theory>;
  val prf =
    Proof_Syntax.read_proof thy true false
      "impI \<cdot> _ \<cdot> _ \<bullet> \
      \   (\<^bold>\<lambda>H: _. \
      \     conjE \<cdot> _ \<cdot> _ \<cdot> _ \<bullet> H \<bullet> \
      \       (\<^bold>\<lambda>(H: _) Ha: _. conjI \<cdot> _ \<cdot> _ \<bullet> Ha \<bullet> H))";
  val thm =
    Proofterm.reconstruct_proof thy \<^prop>\<open>A \<and> B \<longrightarrow> B \<and> A\<close> prf
    |> Proof_Checker.thm_of_proof thy
    |> Drule.export_without_context;
val pretty =  Pretty.writeln (Proof_Syntax.pretty_standard_proof_of \<^context> true thm);
\<close>
ML_file "~~/src/Provers/classical.ML"
lemma testtest : "A \<and> B \<longrightarrow> B \<and> A"
  apply (rule impI)
  apply (erule conjE)
  apply(erule conjI)
  apply assumption
  done

ML\<open> (*See: *) \<^file>\<open>~~/src/HOL/Proofs/ex/Proof_Terms.thy\<close>\<close>
ML\<open>
  val thm = @{thm testtest};

  (*proof body with digest*)
  val body = Proofterm.strip_thm_body (Thm.proof_body_of thm);

  (*proof term only*)
  val prf = Proofterm.proof_of body;

  (*clean output*)
  Pretty.writeln (Proof_Syntax.pretty_proof \<^context> prf);
  Pretty.writeln (Proof_Syntax.pretty_standard_proof_of \<^context> false thm);
  Pretty.writeln (Proof_Syntax.pretty_standard_proof_of \<^context> true thm);

  (*all theorems used in the graph of nested proofs*)
  val all_thms =
    Proofterm.fold_body_thms
      (fn {thm_name, ...} => insert (op =) thm_name) [body] [];
\<close>

ML\<open>
val thy = \<^theory>
val prf =
    Proof_Syntax.read_proof thy true false
      "impI \<cdot> _ \<cdot> _ \<bullet> \
      \   (\<^bold>\<lambda>H: _. \
      \     conjE \<cdot> _ \<cdot> _ \<cdot> _ \<bullet> H \<bullet> \
      \       (\<^bold>\<lambda>(H: _) Ha: _. conjI \<cdot> _ \<cdot> _ \<bullet> Ha \<bullet> H))";
\<close>

ML\<open>
val thy = \<^theory>
val prf =
    Proof_Syntax.read_proof thy true false
      "\<^bold>\<lambda>(H: A \<and> B). conjE \<cdot> A \<cdot> B \<cdot> A \<and> B \<bullet> H";
(*  val thm =
    Proofterm.reconstruct_proof thy \<^prop>\<open>A \<Longrightarrow> B \<Longrightarrow> B \<and> A\<close> prf
    |> Proof_Checker.thm_of_proof thy
    |> Drule.export_without_context;
val pretty =  Pretty.writeln (Proof_Syntax.pretty_standard_proof_of \<^context> true thm);*)
\<close>
ML\<open>
val thy = \<^theory>
val prf =
    Proof_Syntax.read_proof thy true false
      "\<^bold>\<lambda>(H: _) Ha: _. conjI \<cdot> _ \<cdot> _ \<bullet> Ha \<bullet> H";
  val thm =
    Proofterm.reconstruct_proof thy \<^prop>\<open>A \<Longrightarrow> B \<Longrightarrow> B \<and> A\<close> prf
    |> Proof_Checker.thm_of_proof thy
    |> Drule.export_without_context;
val pretty =  Pretty.writeln (Proof_Syntax.pretty_standard_proof_of \<^context> true thm);
\<close>
 
end