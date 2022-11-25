module SizeTArray

open FStar.SizeT
open FStar.UInt32
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
  assert (SizeT.v 2sz == 2);
  free arr;
  x

let main () : SteelT Int32.t emp (fun _ -> emp) =
  let init = test_sizet_alloc () in
  let arr = malloc 2ul init in
  upd arr 0sz 4ul;
  let x = index arr 0sz in
  if x >^ 2ul then (
    free arr;
    0l
  ) else (
    free arr;
    1l
  )
