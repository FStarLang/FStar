module Split
open FStar.Tactics
open FStar.Reflection.Types

private val split_lem : (#a:Type) -> (#b:Type) ->
                        squash a -> squash b -> Lemma (a /\ b)
let split_lem #a #b sa sb = ()

[@plugin]
let compiled_split (): Tac unit =
    dump "In";
    apply_lemma (`split_lem);
    dump "Out"
