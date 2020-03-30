module Bug1966b

open FStar.Tactics

assume val t : int -> Type
assume val lem : x:int -> y:(t x) -> Lemma (y == y)
assume val mk : x:int -> y:(t x) -> int

let f (xxxx:int) (y : t xxxx) =
  assert (y == y)
      by (let xXX = nth_binder (-2) in
          let zZZ = rename_to xXX "zzzz" in
          apply_lemma (`lem))

let syn (xxxx:int) (y : t xxxx) : int =
    _ by (let xXX = nth_binder (-2) in
          let zZZ = rename_to xXX "zzzz" in
          let y = nth_binder (-1) in
          apply (`mk _ (`#y)))
