module Export

(* Section 32.4.  The shape round 38 asked for: a translation unit whose
   public surface is consumed by C code Custard did not generate.  EverParse's
   COSE does exactly this -- [src/cose/c/COSE_Format.c] includes
   [CBORDetAPI.h] and calls 44 [cbor_det_*] symbols across the boundary -- and
   [ExportUser.cpp] here is that consumer in miniature, compiled as C++ so
   that the [extern "C"] guard is tested rather than merely printed.

   The definitions named by --custard_entry are emitted unqualified because of
   --custard_c_no_prefix; [helper] is not named and stays [static]. *)

module U32 = FStar.UInt32

(* Not a root: it must not appear in the header, and it must be static in the
   source, even though the exported functions below both call it. *)
let helper (x: U32.t) : U32.t = U32.add_mod x 1ul

let widget_add (x: U32.t) (y: U32.t) : U32.t = helper (U32.add_mod x y)

let widget_double (x: U32.t) : U32.t = U32.add_mod (helper x) (helper x)

(* A generic definition, to pin down the other half of the rule: this reaches
   the unit only as a specialization, its emitted name carries a section 30.15
   hint, and --custard_c_no_prefix must leave it alone. *)
let rec countdown (#a: Type) (x: a) (n: U32.t) : Tot a (decreases (U32.v n)) =
  if U32.gt n 0ul then countdown x (U32.sub n 1ul) else x

let widget_id (x: U32.t) : U32.t = countdown x 3ul

let main () : U32.t =
  if U32.eq (widget_add 2ul 3ul) 6ul && U32.eq (widget_double 5ul) 12ul
     && U32.eq (widget_id 7ul) 7ul
  then 0ul else 1ul
