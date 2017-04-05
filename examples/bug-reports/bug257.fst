module Bug257

val sizeof : Type -> int
let sizeof (a:Type) =
  match a with
  | int -> 99
  | _ -> 0
