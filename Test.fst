module Test

let a n :nat = 1
let f (ls:list nat) :nat =
  let rec aux (xs:list nat) :nat = a 0
  in
  0

assume type t (n:nat) :Type0
assume val foo: #n:nat{n > 0} -> t n -> Tot unit

let bar (k:nat) (x:t k) = if k > 0 then foo x else ()
