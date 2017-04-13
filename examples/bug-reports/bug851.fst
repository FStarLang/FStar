module Bug851

let h () : Tot unit =
  let rec f (x:int) : GTot int = 5 in
  let g () : Lemma (requires True) (ensures (f 3 == f 5)) = () in
  ()
