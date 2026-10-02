(* FStarLang/FStar#4624, section 95.5.  [SzWidth]'s program on the F# leg at
   --custard_sizet_width 32: [FStar.SizeT.t] is [uint32], its literals carry
   [u], and both directions of its conversions are at that width.  A separate
   module because a test's name is its main's module name. *)
module FsSizet32

let main () : FStar.All.ML Int32.t = SzWidth.main ()
