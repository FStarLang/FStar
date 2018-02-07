module Bane.Lib
open FStar.Tactics
(* To understand the naming convention on this file, please refer to
 * https://www.youtube.com/watch?v=w9wi0cPrU4U *)
val big_phi : int -> tactic unit
let rec big_phi (n : int) =
    if n = 0
    then exact (quote True)
    else (apply (quote l_and);;
          big_phi (n - 1);;
          big_phi (n - 1))

let for_you12 : Type0 = synth_by_tactic (big_phi 12)

let rec repeat_or_fail (t : tactic unit) () : Tac unit =
    (r <-- trytac t;
     match r with
     | None -> fail "Cannot apply t any more"
     | Some x -> repeat_or_fail t)
                 ()

let mytac =
    norm [delta_only ["Bane.Lib.for_you12"]];;
    seq (repeatseq split) (or_else (repeat_or_fail split) trivial)

