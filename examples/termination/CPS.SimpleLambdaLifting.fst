(** Second implementation with λ-lifting **)
module CPS.SimpleLambdaLifting
open FStar.List.Tot

val add_cps_intern : (int -> Tot 'a) -> int -> int -> Tot 'a
let add_cps_intern k x y = k (x + y)

val add_cps : list int -> (int -> Tot 'a) -> Tot 'a
let rec add_cps l k = match l with
  | [] -> k 0
  | hd::tl -> add_cps tl (add_cps_intern k hd)

val add : list int -> Tot int
let add l = add_cps l (fun x -> x)
