module ExtNoPfx
module U32 = FStar.UInt32
open FStar.Attributes

(* Section 117.2.  --custard_c_no_prefix would name [helper] `helper', which
   is already the external's target.  The rename table is seeded with the
   spelling that is emitted, so the rename is rejected. *)
[@@custard_extern "helper"]
assume val ext_helper (n:U32.t) : U32.t

let helper (x:U32.t) : U32.t = U32.add_mod x 1ul

let run (x:U32.t) : U32.t = U32.add_mod (helper x) (ext_helper x)

let main () : FStar.All.ML FStar.Int32.t = let _ = run 1ul in 0l
