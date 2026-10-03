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
   whether it is written implicitly or explicitly.  The bodies are not bare
   binders, so that section 27.4's forwarder rule leaves them alone and this
   test goes on testing erasure. *)
let pred (x:int) : prop = x >= 0
let clamp (x:int) (_:squash (pred x)) : int = if x > 100 then 100 else x
let clampi (x:int) (#_:squash (pred x)) : int = if x > 100 then 100 else x

(* Two cases where the proof binder has to stay, because from the type alone it
   is indistinguishable from something that matters.  [only_proof] would become
   a value, so its body would run at module initialization rather than when it
   is called.  [thunk]'s trailing binder is unit-shaped in front of an impure
   codomain, which is exactly how F* writes a thunk -- [squash p -> ML int] and
   [unit -> ML int] are the same arrow. *)
let only_proof (#p:prop) (_:squash p) : int = 7
let thunk (x:int) (_:squash (pred x)) : ML int = print_string "thunk\n"; x

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
  print_string (string_of_int (only_proof #(pred 0) ()));
  let delayed = thunk 5 in
  print_string (string_of_int (delayed ()));
  print_string "\n";
  print_string (label_of (Tagged #int #bool "tag" 1 ()));
  print_string "\n"
