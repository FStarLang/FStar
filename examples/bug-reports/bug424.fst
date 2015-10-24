(*--build-config
    options:--admit_fsi FStar.Seq --admit_fsi FStar.Set --verify_module Bug;
    other-files:classical.fst ext.fst set.fsi seq.fsi seqproperties.fst heap.fst st.fst all.fst arr.fst ghost.fst
  --*)

module Bug

open FStar.Heap
open FStar.ST
open FStar.Array

// opaque;;making this opaque lets the program check
  type lint (n:nat) = x:nat{ x < n }

type box2 = | B: size:pos -> v:FStar.Heap.ref (lint size) -> box2

val get_size: box2 -> Tot pos
let get_size b = B.size b

//using b.v throughout makes the program check
val get_ref: b:box2 -> Tot (ref (lint (get_size b)))
let get_ref b = B.v b

val get_val: 
  b:box2 -> 
  ST (lint (get_size b))
    (requires (fun h -> contains h (get_ref b)))
    (ensures (fun h0 v h1 -> (h0==h1)
              /\ (contains h0 (get_ref b))
              /\ (sel h0 (get_ref b) = v)))
// let get_val b = ST.read (get_ref b) // Succeeds

(* Fails immediately *)
let get_val b = let r = get_ref b in ST.read r

