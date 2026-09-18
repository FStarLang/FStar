module InlineDepth
open FStar.All
open FStar.Attributes

(* Section 116.  Eleven acyclic inline links.  The expansion of a type must
   not depend on how deep the request that reached it was: with a fuel budget,
   [t10] was described by the outermost plan with the fuel ten levels of
   nesting had left, while its own declaration was rewritten from a fresh
   budget -- and the two then disagreed on the field count. *)
noeq type t0 = | C0 : a:bool -> b:bool -> t0
noeq type t1 = | C1 : [@@@custard_inline_field] p:t0 -> q:bool -> t1
noeq type t2 = | C2 : [@@@custard_inline_field] p:t1 -> q:bool -> t2
noeq type t3 = | C3 : [@@@custard_inline_field] p:t2 -> q:bool -> t3
noeq type t4 = | C4 : [@@@custard_inline_field] p:t3 -> q:bool -> t4
noeq type t5 = | C5 : [@@@custard_inline_field] p:t4 -> q:bool -> t5
noeq type t6 = | C6 : [@@@custard_inline_field] p:t5 -> q:bool -> t6
noeq type t7 = | C7 : [@@@custard_inline_field] p:t6 -> q:bool -> t7
noeq type t8 = | C8 : [@@@custard_inline_field] p:t7 -> q:bool -> t8
noeq type t9 = | C9 : [@@@custard_inline_field] p:t8 -> q:bool -> t9
noeq type t10 = | C10 : [@@@custard_inline_field] p:t9 -> q:bool -> t10
noeq type t11 = | C11 : [@@@custard_inline_field] p:t10 -> q:bool -> t11

let pick (x:t11) : bool = match x with | (C11 (C10 (C9 (C8 (C7 (C6 (C5 (C4 (C3 (C2 (C1 (C0 a _) _) _) _) _) _) _) _) _) _) _) _) -> a

let make (v:bool) : t11 = (C11 (C10 (C9 (C8 (C7 (C6 (C5 (C4 (C3 (C2 (C1 (C0 v true) true) true) true) true) true) true) true) true) true) true) true)

let pick_make (v:bool) : Lemma (pick (make v) == v) = ()

let main () : ML unit =
  FStar.IO.print_string (if pick (make true) then "true\n" else "false\n");
  FStar.IO.print_string (if pick (make false) then "true\n" else "false\n")
