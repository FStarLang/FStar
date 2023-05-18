module Arrays

open FStar.Ghost
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Array
module US = FStar.SizeT

/// Some examples using Steel arrays

let access ()
  : SteelT unit emp (fun _ -> emp)
  = let r = malloc 0sz 2sz in
    let x = index r 0sz in
    upd r 0sz x;
    free r
