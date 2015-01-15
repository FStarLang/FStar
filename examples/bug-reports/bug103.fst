module Bug103


val map: ('a -> 'b) -> 'a -> 'b
let map f x = f x

val ok: list int -> list int
let ok = map Cons 3

val ok2: list int
let ok2 = map (fun l -> Cons 3 l) [17]

val bug: list int
let bug = map (Cons 3) [17]
(*
bug103.fst(14,14-14,22) : Error
Expected type "(_:U374 -> U375)";
got type "(list U376)"
 *)
