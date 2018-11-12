(** With λ-lifting **)
module CPS.DoubleLambdaLifting
open CPS.Expr

val eval_cps1 : (int -> Tot 'a) -> int -> int -> Tot 'a
let eval_cps1 k r1 r2 = k (r1 + r2)

val eval_cps : e:expr -> (int -> Tot 'a) -> Tot 'a (decreases %[e;0])
val eval_cps2 : e:expr -> (int -> Tot 'a) -> int -> Tot 'a (decreases %[e;1])

let rec eval_cps e k =
  match e with
    | Const n -> k n
    | Plus e1 e2 -> eval_cps e1 (eval_cps2 e2 k)

and eval_cps2 e2 k r1 = eval_cps e2 (eval_cps1 k r1)
