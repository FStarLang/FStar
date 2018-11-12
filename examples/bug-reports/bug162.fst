module Bug162

type heap = int -> Tot int
type good (h:heap) = forall x. h x > x
val eval: h:heap{good h} -> nat -> Tot nat
let rec eval h n = match n with
  | 0 -> 0
  | _ -> eval (fun x -> h x + 1) (n - 1)
