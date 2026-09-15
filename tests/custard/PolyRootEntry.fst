module PolyRootEntry

(* Section 72.1.  The other half.  [--custard_entry] names one definition, and
   a name is taken at its word -- so this is still refused.  What changed is
   the message: error 368 used to end with "please report a Custard bug",
   which sent a correct refusal to the issue tracker. *)

let pick (#a:Type0) (b:bool) (x y : a) : a = if b then x else y

let use_it (x y : FStar.UInt32.t) : FStar.UInt32.t = pick true x y

(* The reject harness always passes [--custard_main], so the module needs one;
   it is [pick]'s own rooting, named by [--custard_entry], that is on trial. *)
let main () : FStar.All.ML FStar.Int32.t = if use_it 6ul 7ul = 6ul then 0l else 1l
