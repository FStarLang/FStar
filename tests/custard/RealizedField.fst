module RealizedField
open FStar.All
module D = FStar.Dyn

(* Section 115.  A realization is the statement that the target knows the
   *name*, not the body: [FStar.Dyn.dyn] is an abbreviation in F* and an
   opaque type in every backend.  [unfold_cty] unfolded it anyway, so a field
   of that type was laid out as whatever the abbreviation expands to and the
   value stored in it no longer agreed with the realization that reads it.
   The unfolding now stops at a [Realized] abbreviation. *)
noeq type box = { payload: (d:D.dyn{D.dyn_has_ty d int}); tag: bool }

let pack (n:int) : box = { payload = D.mkdyn n; tag = true }

let roundtrip (n:int) : Dv int = let b = pack n in D.undyn #int b.payload

let main () : ML unit =
  FStar.IO.print_string (string_of_int (roundtrip 41) ^ "\n");
  FStar.IO.print_string (string_of_int (roundtrip 42) ^ "\n")
