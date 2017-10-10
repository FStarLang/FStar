module AssumeRequires

(* NB: we need the underscore in the postcondition, instead of just (), due to #1295 *)
val well_typed : o:(option nat) -> Pure unit (Some? o) (fun _ -> Some?.v o == 42)
let well_typed o = admit ()

val get : o:(option 'a) -> Pure 'a (Some? o) (fun x -> Some?.v o == x)
let get (Some x) = x

// Lemma works too
val lem : o:(option unit) -> Lemma (requires (Some? o)) (ensures (Some?.v o == ()))
let lem o = ()
