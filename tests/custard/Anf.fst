module Anf
open FStar.All
open FStar.IO
open FStar.ExtractAs

(* Section 6, pass 1.

   [cmp] is the shape Pulse's [stt] has: a type constructor carrying
   [@@extract_as_impure_effect] whose first argument is the representation
   (section 7.2).  So an arrow into [cmp a] is an *impure* arrow returning [a],
   even though F* classifies it as Tot -- and because F* classifies it as Tot,
   F* does not put its call sites in monadic normal form.  That is the one
   thing the frontends do not hand us already normalized, and it is what makes
   this pass more than a formality: the two calls below are siblings in a
   single application node, and their order is Custard's to fix.

   [extract_as] supplies the impure implementation, exactly as Pulse does for
   an [fn]: the F* definition is a specification, the attribute carries the
   term that is actually compiled. *)
[@@FStar.Attributes.extract_as_impure_effect]
let cmp (a:Type) : Type = a

[@@extract_as (`(fun (s:string) (n:int) -> (FStar.IO.print_string s; n)))]
let tick (s:string) (n:int) : cmp int = n

let add (a:int) (b:int) : int = a + b

(* To F* this is a Tot application of Tot arguments, so it arrives at Custard
   with both calls nested in place. *)
let sum () : int = add (tick "a" 1) (tick "b" 2)

let main () : ML unit =
  print_string (" " ^ string_of_int (sum ()) ^ "\n")
