module IfaceInstanceReveal

(* Registering an instance here, while the interface's [showable_int] is still
   hidden, must not evict [showable_int] from the attribute table: the table is
   a mutable cache, so filtering it on the way *out* is fine, but filtering it
   on the way *in* would drop the hidden instance permanently. *)
instance showable_bool : showable bool = { show_ = (fun _ -> "bool") }

let f (x:int) : int = x

(* [showable_int] is revealed now that [f] is implemented. *)
let g (x:int) : string = show_ (f x)

let _ = assert (g 0 == "int")
let _ = assert (show_ true == "bool")
