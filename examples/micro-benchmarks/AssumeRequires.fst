module AssumeRequires

(* NB: we need the underscore in the postcondition, instead of just (), due to #1295 *)
val well_typed : o:(option nat) -> Pure unit (Some? o) (fun _ -> Some?.v o == 42)
let well_typed o = admit ()

val get : o:(option 'a) -> Pure 'a (Some? o) (fun x -> Some?.v o == x)
let get (Some x) = x

val get_div : o:(option 'a) -> Div 'a (Some? o) (fun x -> Some?.v o == x)
let get_div (Some x) = x

// Lemma works too
val lem : o:(option unit) -> Lemma (requires (Some? o)) (ensures (Some?.v o == ()))
let lem o = ()

// Testing misc effects
val get_ghost : o:(option 'a) -> Ghost 'a (Some? o) (fun x -> Some?.v o == x)
let get_ghost (Some x) = x

val get_exn : o:(option 'a) -> Exn 'a (Some? o) (fun x -> V (Some?.v o) == x)
let get_exn (Some x) = x

open FStar.ST

val get_st : o:(option 'a) -> ST 'a (fun h0 -> Some? o) (fun h0 x h1 -> Some?.v o == x)
let get_st (Some x) = x

open FStar.HyperStack.All

val get_all : o:(option 'a) -> All 'a (fun h0 -> Some? o) (fun h0 x h1 -> V (Some?.v o) == x)
let get_all (Some x) = x

(* The return type must be unconditionally well-formed, thus this would fail *)

(* val fails : o:(option 'a) -> Pure (x:'a{x == Some?.v o}) (requires (Some? o)) *)
(*                                                          (ensures (fun _ -> True)) *)
(* let fails (Some x) = x *)
