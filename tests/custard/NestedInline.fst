module NestedInline
open FStar.All
open FStar.Attributes

(* Section 115.  Patterns expand innermost-first, so [O (M (I a b) c) d] was
   already a four-argument, [M]-free pattern by the time the outer
   constructor's plan -- built from [middle]'s two *declared* fields -- was
   applied to it, and layout complained that a constructor expecting three
   fields had matched four.  The plan now expands the inlined record's own
   fields first, so the declaration, the constructor application and the
   projection all count the same way. *)
noeq type inner  = | I : x:bool -> y:bool -> inner
noeq type middle = | M : [@@@custard_inline_field] i:inner -> z:bool -> middle
noeq type outer  = | O : [@@@custard_inline_field] m:middle -> t:bool -> outer

let pick (p:outer) : bool = match p with | O (M (I a b) c) d -> a && b && c && d

let main () : ML unit =
  FStar.IO.print_string
    (if pick (O (M (I true true) true) true) then "true\n" else "false\n");
  FStar.IO.print_string
    (if pick (O (M (I true true) true) false) then "true\n" else "false\n")
