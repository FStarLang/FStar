module ExtOwn
module U32 = FStar.UInt32
open FStar.Attributes

(* Section 117.3.  The external names a symbol this program does not own, and
   it is exactly what [c_name] spells [ExtOwn.helper] as.  Nothing renames
   either, so the collision is an error rather than a silently shadowed
   foreign implementation. *)
[@@custard_extern "ExtOwn_helper"]
assume val ext_helper (n:U32.t) : U32.t

let helper (x:U32.t) : U32.t = U32.add_mod x 1ul

let run (x:U32.t) : U32.t = U32.add_mod (helper x) (ext_helper x)

let main () : FStar.All.ML FStar.Int32.t = let _ = run 1ul in 0l
