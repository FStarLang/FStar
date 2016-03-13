(** Nik's suggestion for closure conversion **)
module CPS.DoubleCC

open CPS.Expr

type closure =
  | Clos : env:Type -> env -> (env -> int -> Tot int) -> closure

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
    | Plus t u -> eval t (Clos #((a:expr{a << e}) * closure) (u,k) (clos1 e))

and clos1 _ (u,k) n = eval u (Clos #(closure * int) (k,n) clos2)
