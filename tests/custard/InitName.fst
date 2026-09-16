module InitName
module U32 = FStar.UInt32

(* Section 117.3.  [g] has a computed initializer, so the backend mints an
   [InitName_init_globals]; the definition below is spelled the same way. *)
let compute (x:U32.t) : U32.t = U32.add_mod x 1ul

let g : U32.t = compute 41ul

let init_globals (x:U32.t) : U32.t = U32.add_mod x 2ul

let run (x:U32.t) : U32.t = U32.add_mod g (init_globals x)

let main () : FStar.All.ML FStar.Int32.t = let _ = run 1ul in 0l
