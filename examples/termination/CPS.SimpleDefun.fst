(** It is easy to defunctionalize it **)
module CPS.SimpleDefun
open FStar.List.Tot

type cont =
  | C0 : cont
  | C1 : cont -> int -> cont

val apply : cont -> int -> Tot int
let rec apply k r = match k with
  | C0 -> r
  | C1 k hd -> apply k (hd + r)

val add_cps : list int -> cont -> Tot int
let rec add_cps l k = match l with
  | [] -> apply k 0
  | hd::tl -> add_cps tl (C1 k hd)

val add : list int -> Tot int
let add l = add_cps l C0
