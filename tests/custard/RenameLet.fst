module RenameLet
open FStar.All
open FStar.IO

(* Section 31.4.  [FStar.Attributes.rename_let] on a local [let] renames the
   binder in the emitted code.  In Custard a local is named
   [uniq (ppname b) b.index], and
   the final [FStarC.Custard.Rename] pass rewrites each binder back to its
   [base_name], suffixing only where that would shadow.  So the rename is
   applied to the [bv] itself -- keeping its index -- and the two [dupName]s
   below come out as [dupName] and [dupName1] without any extra work. *)

let f (n:int) : ML int =
  [@@(FStar.Attributes.rename_let "renamedA")]
  let a = n + 1 in
  print_string "";
  [@@(FStar.Attributes.rename_let "dupName")]
  let b = a + a in
  [@@(FStar.Attributes.rename_let "dupName")]
  let c = b + b in
  a + b + c + a + b + c

let main () : ML unit =
  print_string (string_of_int (f 1) ^ "\n")
