module FSNoReal

(* Section 122.9.  A symbol whose only definition is hand-written OCaml in
   [ulib/ml].  The OCaml backend emits the name and links against that file;
   the F# backend has no such file, so emitting the name would produce
   something that does not compile, and the diagnostic would come from the F#
   compiler about a module the reader never wrote. *)

let shout (s:string) : string = FStar.String.lowercase s

let main () : FStar.UInt32.t =
  if shout "AB" = "ab" then 0ul else 1ul
