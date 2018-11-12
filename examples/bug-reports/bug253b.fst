module Bug253b

type cmp (a:Type{hasEq a}) = f:(a -> a -> Tot bool){forall a1 a2. (f a1 a2 /\ f a2 a1)  ==> a1 = a2}

val p_cmp: #k:Type{hasEq k} -> #v:Type -> cmp k -> Tot unit
let p_cmp 'k 'v f =
  let g:(cmp ('k * 'v)) = fun p1 p2 -> f (fst p1) (fst p2) in
  ()
