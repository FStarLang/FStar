module Bug275

val fix_F : #aa:Type -> Tot unit
let rec fix_F (#aa:Type) = ()

(* Unexpected error; please file a bug report, ideally with a
minimized version of the source program that triggered the error. *)
(* Failure("Impossible") *)
