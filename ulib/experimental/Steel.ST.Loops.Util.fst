(*
   Copyright 2021 Microsoft Research

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

module Steel.ST.Loops.Util

open Steel.FractionalPermission
open Steel.ST.Effect
open Steel.ST.Util

module R = Steel.ST.Reference

let repeat_until_inv (p:bool -> vprop) (r:R.ref bool)
  : bool -> vprop
  = fun b -> R.pts_to r full_perm b `star` p b

inline_for_extraction
let repeat_until_cond (p:bool -> vprop) (r:R.ref bool) ()
  : STT bool (exists_ (repeat_until_inv p r)) (repeat_until_inv p r)
  = let _b = elim_exists () in
    rewrite (repeat_until_inv p r _b)
            (R.pts_to r full_perm _b `star` p _b);
    let b = R.read r in
    rewrite (R.pts_to r full_perm _b `star` p _b)
            (repeat_until_inv p r b);
    return b

inline_for_extraction
let repeat_until_body
  (p:bool -> vprop)
  (r:R.ref bool)
  ($body: (unit -> STT bool (p true) (fun b -> p b)))
  ()
  : STT unit
        (repeat_until_inv p r true)
        (fun _ -> exists_ (repeat_until_inv p r))
  = rewrite (repeat_until_inv p r true)
            (R.pts_to r full_perm true `star` p true);
    let b = body () in
    R.write r b;
    rewrite (R.pts_to r full_perm b `star` p b)
            (repeat_until_inv p r b);
    intro_exists b (repeat_until_inv p r)

let repeat_until p $body
  = let r = R.alloc true in
    rewrite (R.pts_to r full_perm true `star` p true)
            (repeat_until_inv p r true);
    intro_exists true (repeat_until_inv p r);
    Steel.ST.Loops.while_loop
      (repeat_until_inv p r)
      (repeat_until_cond p r)
      (repeat_until_body p r body);
    rewrite (repeat_until_inv p r false)
            (R.pts_to r full_perm false `star` p false);
    R.free r
