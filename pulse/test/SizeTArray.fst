module SizeTArray

open FStar.SizeT
open FStar.UInt32
open Steel.Effect
open Steel.Array

let main () : SteelT Int32.t emp (fun _ -> emp) =
  let arr = malloc 2ul 3sz in
  upd arr 0sz 4ul;
  let x = index arr 0sz in
  if x >^ 2ul then (
    free arr;
    1l
  ) else (
    free arr;
    0l
  )
