module Bane.Lib
open FStar.Tactics
(* To understand the naming convention on this file, please refer to
 * https://www.youtube.com/watch?v=w9wi0cPrU4U *)
val big_phi : int -> Tac unit
let rec big_phi (n : int) =
    if n = 0
    then exact (`True)
    else begin
        apply (`l_and);
        big_phi (n - 1);
        big_phi (n - 1)
    end

let for_you : Type0 = synth_by_tactic (fun () -> big_phi 8)

let rec repeat_or_fail (t : unit -> Tac unit) : Tac unit =
     match trytac t with
     | None -> fail "Cannot apply t any more"
     | Some x -> repeat_or_fail t

let mytac () =
    norm [delta_only ["Bane.Lib.for_you"]];
    seq (fun () -> repeatseq split)
        (fun () -> or_else (fun () -> let _ = repeat split in ()) trivial)

