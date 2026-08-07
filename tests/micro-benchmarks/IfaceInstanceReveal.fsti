module IfaceInstanceReveal

class showable (a:Type) = { show_ : a -> string }

val f (x:int) : int

(* A typeclass instance *defined* by the interface, in between two [val]s: it
   is hidden until [f] is implemented, and must be available afterwards. *)
instance showable_int : showable int = { show_ = (fun _ -> "int") }

val g (x:int) : string
