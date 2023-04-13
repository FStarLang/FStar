module SizeTArray

open FStar.SizeT
open FStar.PtrdiffT
open FStar.UInt32
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Array

let aux (x:SizeT.t) : Lemma (Seq.index (Seq.create 3 x) 0 == x) = ()

let test_sizet_alloc () : Steel SizeT.t emp (fun _ -> emp)
  (requires fun _ -> True)
  (ensures fun _ x _ -> SizeT.v x == 2)
  =
  let arr = malloc 2sz 3sz in
  let x = index arr 0sz in
  aux 2sz;
  free arr;
  x

let test2 () : SteelT bool emp (fun _ -> emp) =
  let r = malloc 0ul 3sz in
  ghost_split r 1sz;
  let r1 = split_r r 1sz in
  let r1l = split_l r 1sz in
  change_equal_slprop (varray (split_l r 1sz)) (varray r1l);
  change_equal_slprop (varray (split_r r 1sz)) (varray r1);
  ghost_split r1 1sz;
  let r2 = split_r r1 1sz in
  let r2l = split_l r1 1sz in
  change_equal_slprop (varray (split_l r1 1sz)) (varray r2l);
  change_equal_slprop (varray (split_r r1 1sz)) (varray r2);
  let _ = mk 3s in
  let b = ptrdiff r2 r1l in
  ghost_join r2l r2 ();
  change_equal_slprop
    (varray (merge r2l r2))
    (varray r1);
  ghost_join r1l r1 ();
  change_equal_slprop
    (varray (merge r1l r1))
    (varray r);
  free r;
  return (b = FStar.PtrdiffT.mk 2s)

let main () : SteelT Int32.t emp (fun _ -> emp) =
  let init = test_sizet_alloc () in
  let arr = malloc 2ul init in
  upd arr 0sz 4ul;
  let x = index arr 0sz in
  let b = test2 () in
  if x >^ 2ul && b then (
    free arr;
    0l
  ) else (
    free arr;
    1l
  )
