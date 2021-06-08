module Arrays

open FStar.Ghost
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Array
module U32 = FStar.UInt32

/// Some examples using Steel arrays

let access ()
  : SteelT unit emp (fun _ -> emp)
  = let r = alloc 0ul 2ul in
    let x = index r 0ul in
    upd r 0ul x;
    free r
