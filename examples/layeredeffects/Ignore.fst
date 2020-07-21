module Ignore

open FStar.Universe

(* otherwise it's eqtype and strict checking fails *)
let int : Type u#0 = int

(* An effect which does not use its type *)

let repr (a:Type u#aa) (i:int) : Type u#aa =
  raise_t (x:int{x==i})

let return (a:Type u#aa) (x:a) : repr a 0 =
  raise_val 0

let bind (a:Type u#aa) (b : Type u#bb) (i1 i2 : int)
    (f : repr a i1)
    (g : (x:a -> repr b i2))
    : Tot (repr b (i1+i2)) =
    raise_val (i1+i2)

layered_effect {
  Alg : a:Type -> int -> Effect
  with
  repr         = repr;
  bind         = bind;
  return       = return
}
