module PostconditionLocalization

(* The expected postcondition of a definition is checked at the tail of each
   branch, in that branch's own context and at that branch's own range, and not
   once for the body as a whole.

   The three shapes below all reach the tail of a match: a definition with an
   annotation, a definition whose type comes from a val declaration, and a
   lambda checked against an expected arrow type. Each reports the offending
   branch, and reports it only once. *)

assume val p : int -> prop
assume val lem (x:int) : Lemma (p x)

[@@expect_failure]
let annotated (b:bool) : Pure int (requires True) (ensures fun r -> p r) =
  if b then (lem 1; 1) else 2

val declared : b:bool -> Pure int (requires True) (ensures fun r -> p r)
[@@expect_failure]
let declared b =
  if b then (lem 1; 1) else 2

assume val apply_it (f: (x:int -> Pure int (requires True) (ensures fun r -> p r))) : unit

[@@expect_failure]
let lambda () : unit =
  apply_it (fun x -> if x > 0 then (lem x; x) else 0)
