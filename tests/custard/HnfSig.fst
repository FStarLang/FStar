(* Section 87.  [is_type_sig] asks whether a signature's result is a [Type],
   and answers it by fully normalizing that result.  Nothing below the head is
   ever read, so on an application of an opaque type constructor the whole of
   the argument is reduced and thrown away.

   [wasted] below is that argument.  With the budget this test runs under it
   is enough to exhaust it, and extraction fails with error 365 on a program
   whose classification never depended on a single one of those steps.  Under
   [Weak; HNF] the argument is not entered at all.

   The rest of the file is the control: the three shapes a head normal form
   could plausibly misclassify.  [eqtype] is a refinement of [Type0]; [myeq]
   is a refinement over an *abbreviation*, which is the case [HNF] would get
   wrong on its own because it does not descend into binder types; [u0] is a
   bare abbreviation.  All three have to stay types. *)
module HnfSig
open HnfSigAux

let costly (x: FStar.UInt32.t) : box wasted = magic ()

let t1 : eqtype = FStar.UInt32.t
let t2 : myeq   = bool
let t3 : u0     = FStar.UInt8.t
let t4 : paramrefine bool = FStar.UInt16.t

let v1 (x: t1) : t1 = x
let v2 (x: t2) : t2 = x
let v3 (x: t3) : t3 = x
let v4 (x: t4) : t4 = x

let main () : FStar.All.ML FStar.Int32.t =
  let _ = v1 0ul in let _ = v2 true in let _ = v3 0uy in let _ = v4 0us in 0l
