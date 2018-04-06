structure MOF : sig
  type 'a equal
  type num
  type 'a rexp
  type char
  type attribute_types
  type class_hierarchy
  val mt : class_hierarchy
  val classes : class_hierarchy -> string list
  val all_entities :
    class_hierarchy -> ((string * (string * string) rexp) list) list
  val all_attributes : class_hierarchy -> ((string * attribute_types) list) list
  val remove_overrides : 'b equal -> ('a -> 'b) -> 'a list -> 'a list
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

datatype int = Int_of_integer of IntInf.int;

datatype num = One | Bit0 of num | Bit1 of num;

datatype 'a rexp = Empty | Atom of 'a | Alt of 'a rexp * 'a rexp |
  Conc of 'a rexp * 'a rexp | Star of 'a rexp;

datatype char = Zero_char | Char of num;

datatype attribute_types = File_T of string | Image_file_T of string |
  Thms_T of string list | Int_T of int | Bool_T of bool | String_T of string |
  Text_T of string | Range_T of int * int option | Enum_T of string list;

datatype class_hierarchy =
  Class_T of
    string * class_hierarchy list * (string * attribute_types) list *
      (string * (string * string) rexp) list;

fun eq A_ a b = equal A_ a b;

fun maps f [] = []
  | maps f (x :: xs) = f x @ maps f xs;

fun implode _ = raise Fail "String.implode";

val mt : class_hierarchy =
  Class_T (implode [Char (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One)))))], [], [], []);

fun member A_ [] y = false
  | member A_ (x :: xs) y = eq A_ x y orelse member A_ xs y;

fun map f [] = []
  | map f (x21 :: x22) = f x21 :: map f x22;

fun classes (Class_T (name, sub_classes, attr, comps)) =
  name :: maps classes sub_classes;

fun entities (Class_T (x1, x2, x3, x4)) = x4;

fun all_entities (Class_T (name, sub_classes, attr, comps)) =
  comps :: map entities sub_classes;

fun attributes (Class_T (x1, x2, x3, x4)) = x3;

fun all_attributes (Class_T (name, sub_classes, attr, comps)) =
  attr :: map attributes sub_classes;

fun remove_overrides B_ f [] = []
  | remove_overrides B_ f (a :: r) =
    (if member B_ (map f r) (f a) then remove_overrides B_ f r
      else a :: remove_overrides B_ f r);

end; (*struct MOF*)
