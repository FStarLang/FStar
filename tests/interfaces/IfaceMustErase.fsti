module IfaceMustErase

(* The two negative cases of tests/micro-benchmarks/MustEraseForExtraction,
   under the names they have there; t2, the case that is accepted, stays in
   that module. Both diagnostics are raised against the interface's `val`, so
   they cannot be trapped by an [@@expect_failure] in the implementation: such
   a block defines nothing, and the declaration it attempted would be left
   unimplemented. Hence the recorded output. *)

(* Implemented by a non-informative type, so extraction erases it even though
   this declaration does not say so. *)
val t1 : Type0

(* Implemented by an informative type, which cannot be erased at all. *)
[@@erasable]
val t3 : Type0
