module Bug739

let h () : Tot unit =
  let rec f (x:int) : GTot int = 5 in
  let rec g () : Lemma (requires True) (ensures (f 3 == f 5)) = () in
  ()
