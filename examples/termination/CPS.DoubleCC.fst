(** Nik's suggestion for closure conversion

    Update Jan 23rd, 2017: 
      This approach is not likely to work with universes.
      In particular, see the universe inconsistency below
**)
module CPS.DoubleCC

open CPS.Expr

noeq type closure =
  | Clos : env:Type0 -> env -> (env -> int -> Tot int) -> closure

val apply : closure -> int -> Tot int
let apply c n =
  match c with
    | Clos 'env e k -> k e n

val clos2 : (closure * int) -> int -> Tot int
let clos2 (k,n) m = apply k (n + m)

val eval : e:expr -> closure -> Tot int (decreases %[e;1])
val clos1 : e:expr -> ((a:expr{a << e}) * closure) -> int -> Tot int (decreases %[e;0])
let rec eval e k =
  match e with
    | Const n -> apply k n
    | Plus t u -> eval t (Clos ((a:expr{a << e}) * closure) (u,k) (clos1 e))  //NS: universe inconsistency at the application of Clos

and clos1 _ (u,k) n = eval u (Clos (closure * int) (k,n) clos2)
