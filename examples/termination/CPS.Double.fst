(** Standard implementation **)
module CPS.Double
open CPS.Expr

val eval_cps : expr -> (int -> Tot 'a) -> Tot 'a
let rec eval_cps e k =
  match e with
    | Const n -> k n
    | Plus e1 e2 -> eval_cps e1 (fun r1 -> eval_cps e2 (fun r2 -> k (r1 + r2)))
