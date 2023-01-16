module Wasm11

open FStar.SizeT
open FStar.PtrdiffT
open FStar.UInt64
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Array

let test () : SteelT bool emp (fun _ -> emp) =
  let r = malloc 0uL 8sz in
  ghost_split r 4sz;
  let r1 = split_l r 4sz in
  let r2 = split_r r 4sz in
  change_equal_slprop (varray (split_l r 4sz)) (varray r1);
  change_equal_slprop (varray (split_r r 4sz)) (varray r2);
  let _ = mk 4s in
  let b = ptrdiff r2 r1 in
  ghost_join r1 r2 ();
  change_equal_slprop
    (varray (merge r1 r2))
    (varray r);
  free r;
  return (b = mk 4s)

let main () : SteelT Int32.t emp (fun _ -> emp) =
  let res = test () in
  if res then 0l else 1l
