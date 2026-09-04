module DocsFixture

(* The interface wins: this text is never exported or returned by IDE lookup,
   because the interface declaration is authoritative. *)
[@@doc ["Implementation-side text, which clients of this module never see."]]
let incr (x:int) : int = x + 1

[@@doc ["Implementation-side documentation cannot fill an intentional gap in the interface."]]
let decr (x:int) : int = x - 1

(* This declaration is absent from the interface. The typechecker marks it
   KrmlPrivate, and exporting the implementation cache directly must not leak
   it into the public documentation index. *)
[@@doc ["Implementation-only documentation must remain private."]]
let helper (x:int) : int = x
