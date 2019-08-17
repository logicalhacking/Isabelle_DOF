(*************************************************************************
 * Copyright (C) 
 *               2019      The University of Exeter 
 *               2018-2019 The University of Paris-Saclay
 *               2018      The University of Sheffield
 *
 * License:
 *   This program can be redistributed and/or modified under the terms
 *   of the 2-clause BSD-style license.
 *
 *   SPDX-License-Identifier: BSD-2-Clause
 *************************************************************************)

structure RegExpChecker : sig
  type 'a equal
  type num
  type int
  datatype nat = Zero_nat | Suc of nat
  type 'a set
  datatype 'a rexp = Zero | Onea | Atom of 'a | Plus of 'a rexp * 'a rexp |
    Times of 'a rexp * 'a rexp | Star of 'a rexp
  val nat : int -> nat
  val accepts : 'a * (('b -> 'a -> 'a) * ('a -> bool)) -> 'b list -> bool
  val acceptsa :
    'a equal -> 'a * (('b -> 'a -> 'a set) * ('a -> bool)) -> 'b list -> bool
  val na2da :
    'a equal ->
      'a * (('b -> 'a -> 'a set) * ('a -> bool)) ->
        'a set * (('b -> 'a set -> 'a set) * ('a set -> bool))
  val rexp2na :
    'a equal ->
      'a rexp ->
        bool list * (('a -> bool list -> (bool list) set) * (bool list -> bool))
  val one : nat
  val zero : nat
  val enabled :
    'a set * (('b -> 'a set -> 'a set) * ('a set -> bool)) ->
      'a set -> 'b list -> 'b list
  val example_expression : nat rexp
  val nat_of_integer : IntInf.int -> nat
  val int_of_integer : IntInf.int -> int
end = struct

fun equal_boola p true = p
  | equal_boola p false = not p
  | equal_boola true p = p
  | equal_boola false p = not p;

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

val equal_bool = {equal = equal_boola} : bool equal;

fun eq A_ a b = equal A_ a b;

fun equal_lista A_ [] (x21 :: x22) = false
  | equal_lista A_ (x21 :: x22) [] = false
  | equal_lista A_ (x21 :: x22) (y21 :: y22) =
    eq A_ x21 y21 andalso equal_lista A_ x22 y22
  | equal_lista A_ [] [] = true;

fun equal_list A_ = {equal = equal_lista A_} : ('a list) equal;

datatype num = One | Bit0 of num | Bit1 of num;

datatype int = Zero_int | Pos of num | Neg of num;

datatype nat = Zero_nat | Suc of nat;

datatype 'a set = Set of 'a list | Coset of 'a list;

datatype 'a rexp = Zero | Onea | Atom of 'a | Plus of 'a rexp * 'a rexp |
  Times of 'a rexp * 'a rexp | Star of 'a rexp;

fun dup (Neg n) = Neg (Bit0 n)
  | dup (Pos n) = Pos (Bit0 n)
  | dup Zero_int = Zero_int;

fun plus_nat (Suc m) n = plus_nat m (Suc n)
  | plus_nat Zero_nat n = n;

val one_nat : nat = Suc Zero_nat;

fun nat_of_num (Bit1 n) = let
                            val m = nat_of_num n;
                          in
                            Suc (plus_nat m m)
                          end
  | nat_of_num (Bit0 n) = let
                            val m = nat_of_num n;
                          in
                            plus_nat m m
                          end
  | nat_of_num One = one_nat;

fun nat (Pos k) = nat_of_num k
  | nat Zero_int = Zero_nat
  | nat (Neg k) = Zero_nat;

fun uminus_int (Neg m) = Pos m
  | uminus_int (Pos m) = Neg m
  | uminus_int Zero_int = Zero_int;

fun plus_num (Bit1 m) (Bit1 n) = Bit0 (plus_num (plus_num m n) One)
  | plus_num (Bit1 m) (Bit0 n) = Bit1 (plus_num m n)
  | plus_num (Bit1 m) One = Bit0 (plus_num m One)
  | plus_num (Bit0 m) (Bit1 n) = Bit1 (plus_num m n)
  | plus_num (Bit0 m) (Bit0 n) = Bit0 (plus_num m n)
  | plus_num (Bit0 m) One = Bit1 m
  | plus_num One (Bit1 n) = Bit0 (plus_num n One)
  | plus_num One (Bit0 n) = Bit1 n
  | plus_num One One = Bit0 One;

val one_int : int = Pos One;

fun bitM One = One
  | bitM (Bit0 n) = Bit1 (bitM n)
  | bitM (Bit1 n) = Bit1 (Bit0 n);

fun sub (Bit0 m) (Bit1 n) = minus_int (dup (sub m n)) one_int
  | sub (Bit1 m) (Bit0 n) = plus_int (dup (sub m n)) one_int
  | sub (Bit1 m) (Bit1 n) = dup (sub m n)
  | sub (Bit0 m) (Bit0 n) = dup (sub m n)
  | sub One (Bit1 n) = Neg (Bit0 n)
  | sub One (Bit0 n) = Neg (bitM n)
  | sub (Bit1 m) One = Pos (Bit0 m)
  | sub (Bit0 m) One = Pos (bitM m)
  | sub One One = Zero_int
and plus_int (Neg m) (Neg n) = Neg (plus_num m n)
  | plus_int (Neg m) (Pos n) = sub n m
  | plus_int (Pos m) (Neg n) = sub m n
  | plus_int (Pos m) (Pos n) = Pos (plus_num m n)
  | plus_int Zero_int l = l
  | plus_int k Zero_int = k
and minus_int (Neg m) (Neg n) = sub n m
  | minus_int (Neg m) (Pos n) = Neg (plus_num m n)
  | minus_int (Pos m) (Neg n) = Pos (plus_num m n)
  | minus_int (Pos m) (Pos n) = sub m n
  | minus_int Zero_int l = uminus_int l
  | minus_int k Zero_int = k;

fun list_ex p [] = false
  | list_ex p (x :: xs) = p x orelse list_ex p xs;

fun bex (Set xs) p = list_ex p xs;

fun snd (x1, x2) = x2;

fun fst (x1, x2) = x1;

fun next a = fst (snd a);

fun foldl f a [] = a
  | foldl f a (x :: xs) = foldl f (f a x) xs;

fun foldl2 f xs a = foldl (fn aa => fn b => f b aa) a xs;

fun delta a = foldl2 (next a);

fun filter p [] = []
  | filter p (x :: xs) = (if p x then x :: filter p xs else filter p xs);

fun membera A_ [] y = false
  | membera A_ (x :: xs) y = eq A_ x y orelse membera A_ xs y;

fun member A_ x (Coset xs) = not (membera A_ xs x)
  | member A_ x (Set xs) = membera A_ xs x;

fun removeAll A_ x [] = []
  | removeAll A_ x (y :: xs) =
    (if eq A_ x y then removeAll A_ x xs else y :: removeAll A_ x xs);

fun inserta A_ x xs = (if membera A_ xs x then xs else x :: xs);

fun insert A_ x (Coset xs) = Coset (removeAll A_ x xs)
  | insert A_ x (Set xs) = Set (inserta A_ x xs);

fun fold f (x :: xs) s = fold f xs (f x s)
  | fold f [] s = s;

fun sup_set A_ (Coset xs) a = Coset (filter (fn x => not (member A_ x a)) xs)
  | sup_set A_ (Set xs) a = fold (insert A_) xs a;

val bot_set : 'a set = Set [];

fun sup_seta A_ (Set xs) = fold (sup_set A_) xs bot_set;

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun image f (Set xs) = Set (map f xs);

fun deltaa A_ a [] p = insert A_ p bot_set
  | deltaa A_ aa (a :: w) p =
    sup_seta A_ (image (deltaa A_ aa w) (next aa a p));

fun null [] = true
  | null (x :: xs) = false;

fun start a = fst a;

fun fin a = snd (snd a);

fun accepts a = (fn w => fin a (delta a w (start a)));

fun acceptsa A_ a w = bex (deltaa A_ a w (start a)) (fin a);

fun or x =
  (fn (ql, (dl, fl)) => fn (qr, (dr, fr)) =>
    ([], ((fn a => fn b =>
            (case b
              of [] =>
                sup_set (equal_list equal_bool)
                  (image (fn aa => true :: aa) (dl a ql))
                  (image (fn aa => false :: aa) (dr a qr))
              | true :: s => image (fn aa => true :: aa) (dl a s)
              | false :: s => image (fn aa => false :: aa) (dr a s))),
           (fn a =>
             (case a of [] => fl ql orelse fr qr | true :: s => fl s
               | false :: s => fr s)))))
    x;

fun is_empty (Set xs) = null xs;

fun na2da A_ a =
  (insert A_ (start a) bot_set,
    ((fn aa => fn q => sup_seta A_ (image (next a aa) q)),
      (fn q => bex q (fin a))));

fun atom A_ a =
  ([true],
    ((fn b => fn s =>
       (if equal_lista equal_bool s [true] andalso eq A_ b a
         then insert (equal_list equal_bool) [false] bot_set else bot_set)),
      (fn s => equal_lista equal_bool s [false])));

fun conc x =
  (fn (ql, (dl, fl)) => fn (qr, (dr, fr)) =>
    (true :: ql,
      ((fn a => fn b =>
         (case b of [] => bot_set
           | true :: s =>
             sup_set (equal_list equal_bool)
               (image (fn aa => true :: aa) (dl a s))
               (if fl s then image (fn aa => false :: aa) (dr a qr)
                 else bot_set)
           | false :: s => image (fn aa => false :: aa) (dr a s))),
        (fn a =>
          (case a of [] => false
            | left :: s =>
              left andalso (fl s andalso fr qr) orelse
                not left andalso fr s)))))
    x;

fun plus x =
  (fn (q, (d, f)) =>
    (q, ((fn a => fn s =>
           sup_set (equal_list equal_bool) (d a s)
             (if f s then d a q else bot_set)),
          f)))
    x;

val epsilon :
  bool list * (('a -> bool list -> (bool list) set) * (bool list -> bool))
  = ([], ((fn _ => fn _ => bot_set), null));

fun star a = or epsilon (plus a);

fun rexp2na A_ Zero = ([], ((fn _ => fn _ => bot_set), (fn _ => false)))
  | rexp2na A_ Onea = epsilon
  | rexp2na A_ (Atom a) = atom A_ a
  | rexp2na A_ (Plus (r, s)) = or (rexp2na A_ r) (rexp2na A_ s)
  | rexp2na A_ (Times (r, s)) = conc (rexp2na A_ r) (rexp2na A_ s)
  | rexp2na A_ (Star r) = star (rexp2na A_ r);

fun apsnd f (x, y) = (x, f y);

val one : nat = one_nat;

val zero : nat = Zero_nat;

fun enabled a sigma = filter (fn x => not (is_empty (next a x sigma)));

val example_expression : nat rexp =
  let
    val r0 = Atom Zero_nat;
    val r1 = Atom one_nat;
  in
    Times (Star (Plus (Times (r1, r1), r0)), Star (Plus (Times (r0, r0), r1)))
  end;

fun divmod_integer k l =
  (if ((k : IntInf.int) = (0 : IntInf.int))
    then ((0 : IntInf.int), (0 : IntInf.int))
    else (if IntInf.< ((0 : IntInf.int), l)
           then (if IntInf.< ((0 : IntInf.int), k)
                  then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                  else let
                         val (r, s) =
                           IntInf.divMod (IntInf.abs k, IntInf.abs l);
                       in
                         (if ((s : IntInf.int) = (0 : IntInf.int))
                           then (IntInf.~ r, (0 : IntInf.int))
                           else (IntInf.- (IntInf.~ r, (1 : IntInf.int)),
                                  IntInf.- (l, s)))
                       end)
           else (if ((l : IntInf.int) = (0 : IntInf.int))
                  then ((0 : IntInf.int), k)
                  else apsnd IntInf.~
                         (if IntInf.< (k, (0 : IntInf.int))
                           then IntInf.divMod (IntInf.abs k, IntInf.abs l)
                           else let
                                  val (r, s) =
                                    IntInf.divMod (IntInf.abs k, IntInf.abs l);
                                in
                                  (if ((s : IntInf.int) = (0 : IntInf.int))
                                    then (IntInf.~ r, (0 : IntInf.int))
                                    else (IntInf.- (IntInf.~
              r, (1 : IntInf.int)),
   IntInf.- (IntInf.~ l, s)))
                                end))));

fun nat_of_integer k =
  (if IntInf.<= (k, (0 : IntInf.int)) then Zero_nat
    else let
           val (l, j) = divmod_integer k (2 : IntInf.int);
           val la = nat_of_integer l;
           val lb = plus_nat la la;
         in
           (if ((j : IntInf.int) = (0 : IntInf.int)) then lb
             else plus_nat lb one_nat)
         end);

fun times_num (Bit1 m) (Bit1 n) =
  Bit1 (plus_num (plus_num m n) (Bit0 (times_num m n)))
  | times_num (Bit1 m) (Bit0 n) = Bit0 (times_num (Bit1 m) n)
  | times_num (Bit0 m) (Bit1 n) = Bit0 (times_num m (Bit1 n))
  | times_num (Bit0 m) (Bit0 n) = Bit0 (Bit0 (times_num m n))
  | times_num One n = n
  | times_num m One = m;

fun times_int (Neg m) (Neg n) = Pos (times_num m n)
  | times_int (Neg m) (Pos n) = Neg (times_num m n)
  | times_int (Pos m) (Neg n) = Neg (times_num m n)
  | times_int (Pos m) (Pos n) = Pos (times_num m n)
  | times_int Zero_int l = Zero_int
  | times_int k Zero_int = Zero_int;

fun int_of_integer k =
  (if IntInf.< (k, (0 : IntInf.int))
    then uminus_int (int_of_integer (IntInf.~ k))
    else (if ((k : IntInf.int) = (0 : IntInf.int)) then Zero_int
           else let
                  val (l, j) = divmod_integer k (2 : IntInf.int);
                  val la = times_int (Pos (Bit0 One)) (int_of_integer l);
                in
                  (if ((j : IntInf.int) = (0 : IntInf.int)) then la
                    else plus_int la one_int)
                end));

end; (*struct RegExpChecker*)
