module TWal1107
type refined (a:Type) (pred:a -> bool) = x:a{pred x}

class bytes_like (bytes:Type0) = {
  meh: unit;
}

unfold
type toto = refined nat (fun x0 -> x0 = (1 <: nat) || x0 = (0 <: nat))

unfold
let tata (x1:toto): Type0 =
  match x1 with
  | 0 -> unit
  | 1 -> unit

type test_sum (bytes:Type0) {|bytes_like bytes|} =
  | Ctor_1: unit -> test_sum bytes
  | Ctor_2: unit -> test_sum bytes

val arrow_to_forall: #a:Type -> p:(a -> Type0) -> squash (forall (x:a). p x) -> (x:a -> squash (p x))
let arrow_to_forall #a p _ x =
  ()

assume val foo:
  bytes:Type0 -> {|bytes_like bytes|} ->
  f:(dtuple2 toto tata -> test_sum bytes) -> g:(test_sum bytes -> dtuple2 toto tata) ->
  (x:dtuple2 toto tata -> squash (g (f x) == x)) ->
  unit
open FStar.Tactics

let bla (bytes:Type0) {|bytes_like bytes|} =
  foo bytes
    (fun x ->
      match x with
      | (|0, _0|) -> Ctor_1 _0
      | (|1, _0|) -> Ctor_2 _0
    )
    (fun x ->
      match x with
      | Ctor_1 _0 -> (|0, _0|)
      | Ctor_2 _0 -> (|1, _0|)
    )
    (_ by (
      apply (`arrow_to_forall);
      tadmit()
    ))
