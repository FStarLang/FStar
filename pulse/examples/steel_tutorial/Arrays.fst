module Arrays

open FStar.Ghost
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Array
module U32 = FStar.UInt32

/// Some examples using Steel arrays

let access (#a:Type) (r:array a)
  : Steel a (varray r) (fun _ -> varray r)
          (requires fun h -> length (asel r h) > 1)
          (ensures fun _ _ _ -> True)
  = let x = index r 0ul in
    x
