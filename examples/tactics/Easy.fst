module Easy

open FStar.Tactics
open FStar.Tactics.Typeclasses

val lemma_from_squash : #a:Type -> #b:(a -> Type) -> (x:a -> squash (b x)) -> x:a -> Lemma (b x)
let lemma_from_squash #a #b f x = FStar.Squash.give_proof (f x) // Is it expected that I need to call `give_proof`?

let easy_fill () =
    let _ = repeat intro in
    (* If the goal is `a -> Lemma b`, intro will fail, try to use this switch *)
    let _ = trytac (fun () -> apply (`lemma_from_squash); intro ()) in
    smt ()

val easy : #a:Type -> (#[easy_fill] _ : a) -> a
let easy #a #x = x

val plus_assoc : x:int -> y:int -> z:int -> Lemma ((x + y) + z == x + (y + z))
let plus_assoc = easy

val plus_comm : x:int -> y:int -> Lemma (x + y == y + x)
let plus_comm = easy
