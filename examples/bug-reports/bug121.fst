module Bug121FunctionNotEqualToItsDefinition

type var = nat

type exp =
  | EVar   : var -> exp
  | EAbs   : exp -> exp

type sub = var -> Tot exp

(* Parallel substitution operation `subst` *)

val inc_var : var -> Tot exp
let inc_var y = EVar (y+1)

val subst_eabs : (e:exp -> sub -> Tot exp) -> sub -> Tot sub
let subst_eabs subst_f s =
  fun y -> if y = 0 then EVar y
           else subst_f (s (y-1)) inc_var

(* F* can't prove this terminating, but that's _not_ the problem *) 
val subst : e:exp -> sub -> Tot exp
let rec subst e s =
  match e with
  | EVar x -> s x
  | EAbs e1 -> EAbs (subst e1 (subst_eabs subst s))

(* F* not being able to prove this is the problem: *)
val should_be_trivial : e:exp -> s:sub -> Lemma
  (ensures (subst (EAbs e) s = EAbs (subst e (subst_eabs subst s))))
let should_be_trivial e s = ()
