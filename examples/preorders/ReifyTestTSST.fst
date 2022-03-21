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
module ReifyTestTSST

open FStar.Preorder
open FStar.Monotonic.Witnessed

(* *************************************************************************************************** *)
(* A nat-valued instance of time-stamped preorder-indexed state monads for reify-recall demonstration. *)
(* *************************************************************************************************** *)

let timestamp = nat

let timestamped_state (state:Type) = timestamp * state

let get_timestamp #state tss = fst tss

let get_state #state tss = snd tss

let older_than ts0 ts1 = ts0 < ts1

let older_than_transitive ts0 ts1 ts2 = ()

let older_than_antisymmetric ts0 ts1 = ()

let get () = admit ()
let put s = admit ()
let witness p = admit ()
let recall p = admit ()
let reify_ #_ #_ #_ _ _ = admit ()
