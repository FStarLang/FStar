module FStar.PropositionalExtensionality

let compatible_at (p1 p2:prop) (p3:prop) =
    (forall (x:p1). has_type x p3) /\
    (forall (y:p2). has_type y p3)


let compatible (p1 p2:prop) = exists (p3:prop). compatible_at p1 p2 p3

assume val axiom :
    unit
  -> Lemma (forall (p1:prop) (p2:prop {compatible p1 p2}).{:pattern (compatible p1 p2)}
                (p1 <==> p2) <==> (p1 == p2))

let apply (p1 p2:prop)
  : Lemma (requires (compatible p1 p2))
          (ensures  ((p1 <==> p2) <==> (p1 == p2)))
  = axiom ()
