module Bug15

assume type ilist
assume val length: ilist -> Tot int

val foo2 : m : int -> z : ilist -> 
            Lemma (ensures (length z = m))
let rec foo2 m =
  match m with
  | _ -> (fun l -> foo2 m l)
