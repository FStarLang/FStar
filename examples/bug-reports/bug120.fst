module Bug120

type var = nat

type exp =
  | EVar : var -> exp
  | EAbs : exp -> exp

type sub = var -> Tot exp

(* CH: How on earth can F* show this terminating with this decreases clause? *)
val subst : e:exp -> sub -> Tot exp (decreases e)
let rec subst e s =
  match e with
  | EVar x -> s x
  | EAbs e1 -> EAbs (subst e1 (fun y -> if y = 0 then EVar y
                                 else subst (s (y-1)) (fun y' -> EVar (y'+1))))
