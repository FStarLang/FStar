module Bug540


let test (a:Type) (b:Type) : Lemma (True) =
  let _ =  a = b in ()
