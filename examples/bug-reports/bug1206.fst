module Bug1206

open FStar.Tactics
open FStar.HyperStack.ST

#reset-options "--max_fuel 1 --max_ifuel 1"

type bslice =
| BSlice : len:nat -> bslice

let serializer_ty  = buf:bslice -> Stack (option (off:nat{off <= buf.len}))
  (requires (fun h0 -> True))
  (ensures (fun h0 r h1 -> True))

let ser_id (s1: serializer_ty) : serializer_ty =
  fun buf -> match s1 buf with
  | Some off -> Some off
  | None -> None

assume val ser : serializer_ty

let normalize (#t:Type) (x:t) : Tac unit =
  dup ();
  exact (quote x);
  norm [delta];
  trefl ()

let ser' : serializer_ty =
  synth_by_tactic (fun () -> normalize (ser_id ser))
