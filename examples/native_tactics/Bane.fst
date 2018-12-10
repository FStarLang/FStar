(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module Bane
open FStar.Tactics
(* To understand the naming convention on this file, please refer to
 * https://www.youtube.com/watch?v=w9wi0cPrU4U *)
[@plugin]
val big_phi : int -> Tac unit
let rec big_phi (n : int) =
    if n = 0
    then exact (`True)
    else begin
        apply (`l_and);
        big_phi (n - 1);
        big_phi (n - 1)
    end

let for_you12 : Type0 = synth_by_tactic (fun () -> big_phi 12)

let rec repeat_or_fail (t : unit -> Tac unit) : Tac unit =
     match trytac t with
     | None -> fail "Cannot apply t any more"
     | Some x -> repeat_or_fail t

[@plugin]
let mytac () =
    norm [delta_only ["Bane.for_you12"]];
    seq (fun () -> repeatseq split)
        (fun () -> or_else (fun () -> let _ = repeat split in ()) trivial)

