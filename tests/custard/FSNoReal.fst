module FSNoReal

(* Section 122.9.  A symbol whose only definition is hand-written OCaml in
   [ulib/ml].  The OCaml backend emits the name and links against that file;
   the F# backend has no such file, so emitting the name would produce
   something that does not compile, and the diagnostic would come from the F#
   compiler about a module the reader never wrote.

   The subject has to be a symbol the F# backend does not realize *and is not
   about to*: [FStar.String.lowercase] was this test's until section 122.9's
   realizations arrived and took it, at which point the test passed
   vacuously.  Reading a line is realizable and unrealized, which is the
   whole content of the rule. *)

let ask () : FStar.All.ML string = FStar.IO.input_line ()

let main () : FStar.All.ML FStar.UInt32.t =
  if ask () = "" then 0ul else 1ul
