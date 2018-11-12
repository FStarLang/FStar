module Canon
module XX = FStar.Tactics.Canon // load it, to get the symbols for the lemmas
open FStar.Tactics
open FStar.Mul
open FStar.Tactics.Canon

[@plugin]
let canon () = FStar.Tactics.Canon.canon()

[@plugin]
let check_canon () =
    canon ();
    or_else qed
            (fun () -> dump "`canon` left the following goals";
                       fail "")

