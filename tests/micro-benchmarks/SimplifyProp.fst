module SimplifyProp

assume
val pure (p:prop) : unit


(* All the common logical connectives can be proven to be props by simplification, without an SMT call *)
#push-options "--no_smt"
let t0 (x:int) = pure (x == 0)
let t1 (x:int) = pure (x == 0 /\ 0 == x)
let t2 (x:int) = pure (x == 0 ==> 0 == x)
let t3 (x:int) = pure (x == 0 <==> 0 == x)
let t4 (x:int) = pure (x == 0 \/ 0 == x)
let t5 (x:int) = pure (~(x == 0))
let t6 = pure (forall (x:int). x == 0 \/ x =!= 0)
let t7 = pure (exists (x:int). x == 0 \/ x =!= 0)
let t8 = pure unit
let t9 = pure True
let t10 = pure False
let t11 (a:Type) = pure (squash a)
let t12 (b:bool) = pure b
let t12_1 (b:bool) = pure (b2t b)
let t13 (a:Type) = pure (hasEq a)
let t14 (a:Type) (x y:a) = pure (x << y)

#pop-options
