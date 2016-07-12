module Bug274

val fix_F : #aa:Type -> #p:(aa -> Type) -> unit -> Tot unit
let fix_F (#aa:Type) #p () = ()
(* Unexpected error; please file a bug report, ideally with a
   minimized version of the source program that triggered the error. *)
(* Failure("Bound type variable not found: aa") *)

(* on the other hand this works fine: *)
val fix_F' : #aa:Type -> #p:(aa -> Type) -> unit -> Tot unit
let fix_F' #aa #p () = ()

(* and so does this: *)
val fix_F'' : #aa:Type -> #p:(aa -> Type) -> unit -> Tot unit
let fix_F'' (#aa:Type) (#p:(aa -> Type)) () = ()
