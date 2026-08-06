module Implicits
open FStar.All
open FStar.IO

(* Custard never looks at the implicit/explicit qualifier of a binder: what
   decides whether a binder survives is whether it holds a runtime value.  So
   an implicit *value* binder is a perfectly ordinary parameter and has to be
   passed at every call site. *)
let addn (#n:int) (x:int) : int = n + x

(* ... whereas an implicit *type* binder holds no value, under the uniform
   compilation of types of section 5.0, and disappears. *)
let idi (#a:Type) (x:a) : a = x

(* An explicit type binder is treated exactly the same way. *)
let ide (a:Type) (x:a) : a = x

(* A proof binder is non-informative (section 3.1, rule 1) and disappears too,
   whether it is written implicitly or explicitly. *)
let pred (x:int) : prop = x >= 0
let clamp (x:int) (_:squash (pred x)) : int = x
let clampi (x:int) (#_:squash (pred x)) : int = x

(* Constructors mix all three kinds of field. *)
noeq
type tagged (a:Type) =
  | Tagged : #b:Type -> label:string -> value:a -> proof:squash (pred 0) -> tagged a

let label_of (#a:Type) (t : tagged a) : string =
  match t with
  | Tagged l _ _ -> l

let main () : ML unit =
  print_string (string_of_int (addn #10 5));
  print_string "\n";
  print_string (idi "implicit");
  print_string "\n";
  print_string (ide string "explicit");
  print_string "\n";
  print_string (string_of_int (clamp 3 ()));
  print_string (string_of_int (clampi 4 #()));
  print_string "\n";
  print_string (label_of (Tagged #int #bool "tag" 1 ()));
  print_string "\n"
