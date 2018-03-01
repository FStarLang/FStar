module Split
open FStar.Tactics
open FStar.Reflection.Types

private val split_lem : (#a:Type) -> (#b:Type) ->
                        squash a -> squash b -> Lemma (a /\ b)
let split_lem #a #b sa sb = ()

let compiled_split (): tactic unit =
    dump "In";;
    apply_lemma (fun () -> `split_lem);;
    dump "Out"
