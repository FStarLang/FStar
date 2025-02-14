(*
   Copyright 2024 Microsoft Research

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

module Pulse.Lib.PCM.Fraction
open FStar.PCM
open FStar.Real
open PulseCore.FractionalPermission

(* Lifted from Steel.PCMFrac *)
let fractional (a:Type u#a) = option (a & perm)
let composable #a : symrel (fractional a) =
  fun (f0 f1:fractional a) ->
    match f0, f1 with
    | None, _
    | _, None -> True
    | Some (x0, p0), Some (x1, p1) -> x0==x1 /\ p0 +. p1 <=. one
let compose #a (f0:fractional a) (f1:fractional a{composable f0 f1}) : fractional a =
  match f0, f1 with
  | None, f
  | f, None -> f
  | Some (x0, p0), Some (_, p1) -> Some (x0, p0 +. p1)

let pcm_frac #a : pcm (fractional a) = {
  p = {
         composable = composable;
         op = compose;
         one = None
      };
  comm = (fun _ _ -> ());
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun _ -> ());
  refine = (fun _ -> True)
}

let mk_frame_preserving_upd
  (#a: Type)
  (v0: Ghost.erased a)
  (v1: a)
: Tot (frame_preserving_upd pcm_frac (Some (Ghost.reveal v0, 1.0R)) (Some (v1, 1.0R)))
= fun _ -> Some (v1, 1.0R)

let mk_frame_preserving_upd_none
  (#a: Type)
  (v0: Ghost.erased a)
: Tot (frame_preserving_upd pcm_frac (Some (Ghost.reveal v0, 1.0R)) None)
= fun _ -> None

let perm_ok p : prop = p <=. 1.0R

let full_values_compatible (#a:Type u#a) (x:a)
: Lemma (compatible pcm_frac (Some (x, 1.0R)) (Some (x, 1.0R)))
= let v = Some (x, 1.0R) in
  assert (FStar.PCM.composable pcm_frac v None)
