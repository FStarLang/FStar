module Split
open FStar.Tactics
open FStar.Reflection.Types

(* assume val lemma: term *)

let compiled_split (): tactic unit =
    dump "In";;
//    apply (return lemma);;
    apply_lemma (fun () -> `split_lem);;
    dump "Out"
