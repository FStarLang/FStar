(** With greadier λ-lifting that removes mutual recursion **)
module CPS.DoubleLambdaLifting2
open CPS.Expr

val eval_cps1 : (int -> Tot 'a) -> int -> int -> Tot 'a
let eval_cps1 k r1 r2 = k (r1 + r2)

val eval_cps2 : (int -> Tot 'a) -> ((int -> Tot 'a) -> Tot 'a) -> int -> Tot 'a
let eval_cps2 k eval_cps r1 = eval_cps (eval_cps1 k r1)

val eval_cps : expr -> (int -> Tot 'a) -> Tot 'a
let rec eval_cps e k =
  match e with
    | Const n -> k n
    | Plus e1 e2 -> eval_cps e1 (eval_cps2 k (eval_cps e2))

val eval : expr -> Tot int
let eval e = eval_cps e (fun x -> x)
