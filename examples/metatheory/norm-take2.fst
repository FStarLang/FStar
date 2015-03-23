module NormTake2

open StlcStrongDbParSubst
open Classical

type multi (a:Type) (r:(a -> a -> Type)) : a -> a -> Type =
  | Multi_refl : x:a -> multi a r x x
  | Multi_step : x:a -> y:a -> z:a -> r x y -> multi a r y z -> multi a r x z

type steps : exp -> exp -> Type = multi exp step

type halts (e:exp) : Type = (exists (e':exp). (steps e e' /\ is_value e'))

val red : t:typ -> exp -> Tot bool (decreases t)
let rec red t e =
  match t with
  | TArr t1 t2 ->
     excluded_middle (typing empty e (TArr t1 t2) /\
                      halts e /\
                      (forall e'. red t1 e' ==> red t2 (EApp e e')))
