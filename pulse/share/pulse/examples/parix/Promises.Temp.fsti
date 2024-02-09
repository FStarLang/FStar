(*
   Copyright 2023 Microsoft Research

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

module Promises.Temp

(* A temporary interface that does not require anything
to be ghost, and just works in stt. Clearly bogus, only to be used
as a stepping stone. *)

open Pulse.Lib.Pervasives

val promise (f:vprop) (v:vprop) : vprop

(* Anything that holds now holds in the future too. *)
val return_promise (f:vprop) (v:vprop)
  : stt unit v (fun _ -> promise f v)

val make_promise (f:vprop) (v:vprop) (extra:vprop)
  ($k : unit -> stt unit (f ** extra) (fun _ -> f ** v))
  : stt unit extra (fun _ -> promise f v)

val redeem_promise (f:vprop) (v:vprop)
  : stt unit (f ** promise f v) (fun () -> f ** v)

val bind_promise (#f:vprop) (#v1:vprop) (#v2:vprop)
        (extra : vprop) // any better way to propagate context?
        (k : unit -> stt unit (extra ** v1) (fun () -> promise f v2))
  : stt unit (promise f v1 ** extra) (fun () -> promise f v2)

val join_promise (#f:vprop) (v1:vprop) (v2:vprop)
  : stt unit (promise f v1 ** promise f v2)
             (fun () -> promise f (v1 ** v2))

val split_promise (#f:vprop) (v1:vprop) (v2:vprop)
  : stt unit (promise f (v1 ** v2))
             (fun () -> promise f v1 ** promise f v2)

// TODO: write a variant that assumes f too
val rewrite_promise (#f:vprop) (v1 : vprop) (v2 : vprop)
  (k : unit -> stt unit v1 (fun _ -> v2))
  : stt unit (promise f v1)
             (fun _ -> promise f v2)
