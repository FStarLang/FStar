module Bug540


let test (t:eqtype) (a b:t) : Lemma (requires t == (Type u#a)) (ensures True) =
  let _ =  a <> b in ()
