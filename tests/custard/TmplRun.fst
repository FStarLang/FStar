module TmplRun

(* Section 72.3.  A template argument that is only known at run time is
   refused by error 390.  The request chain the message prints names
   specializations; what the reader needs is the *declaration* that still has
   the index as a runtime parameter, which here is [helper] and not [main].
   Kuiper's report: "nothing in the message says which of our functions to
   look at". *)

open FStar.Attributes
module SZ = FStar.SizeT

[@@custard_extern "tmpl_frag<{0}>"]
assume val frag (n : nat) : Type0

[@@custard_extern "tmpl_make"]
assume val make (n : nat) : FStar.All.ML (frag n)

let helper (tm : SZ.t) : FStar.All.ML unit =
  let _ = make (SZ.v tm) in ()

let main () : FStar.All.ML FStar.Int32.t = helper 4sz; 0l
