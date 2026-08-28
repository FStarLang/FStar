module FieldAttr

(* Section 30.4.  [@@monomorphize] on a *constructor field* is read by
   nothing: the attribute classifies the arguments of a function (section
   3.2), and a field is not an argument of anything.  Silence here is worse
   than a warning, because error 364's advice -- "mark it in the enclosing
   definition" -- sends a reader who finds that the offending name is a Type0
   field to write exactly this, and getting the same error back with no
   acknowledgement is indistinguishable from having fixed nothing.

   The 368 that follows is section 30.3: a record whose surviving field's type
   mentions its Type0 field is an existential package, and no annotation
   changes that.  The test is the warning; the error is the backdrop. *)

module SZ = FStar.SizeT
module U8 = FStar.UInt8

let measure (_: U8.t) : SZ.t = 1sz

noeq type pbundle = {
  [@@@monomorphize] pimpl_type: Type0;
  pmeasure: pimpl_type -> SZ.t;
}

let mk () : pbundle = { pimpl_type = U8.t; pmeasure = measure }
let go (x: U8.t) : SZ.t = let b = mk () in b.pmeasure x
let main () : FStar.UInt32.t = if SZ.(go 3uy =^ 1sz) then 0ul else 1ul
