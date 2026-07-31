module IfaceCopiedLet

(* Definitions written directly in an interface are copied verbatim into the
   implementation, without being rechecked. *)
let twice (x:int) : int = x + x

val quad (x:int) : int

(* A typeclass instance resolved in the interface must not be resolved again
   when the implementation is checked. *)
class showable (a:Type) = { show_ : a -> string }

instance showable_int : showable int = { show_ = (fun _ -> "int") }

val describe (#a:Type) {| showable a |} (x:a) : string
