module Typeclass
open FStar.All
open FStar.IO
open FStar.Tactics.Typeclasses

(* The worked example of doc/ref/custard.md section 3: the class, the
   dictionary and the projector must all disappear, leaving three specialized
   first-order functions. *)

class foo (a: Type) = { frobnicate: a -> string }

instance foo_string : foo string = { frobnicate = fun x -> x }

let bar (#a:Type) {| foo a |} (x:a) : string = frobnicate x

let baz (#a:Type) (x:a) {| foo a |} : string = bar x

let main () : ML unit =
  print_string (baz "frob");
  print_string "\n"
