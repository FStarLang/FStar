(*
   Copyright 2026 Microsoft Research

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
module Pulse.Extrinsic.Guarded
friend PulseCore.IndirectionTheorySep

module S = PulseCore.IndirectionTheorySep
module K = PulseCore.KnotInstantiation

let agrees_below (#a:Type) (n:nat) (p q:family a) : prop =
  forall x m. K.level_ m < n ==> (p x m <==> q x m)

let rec iterate (#a:Type) (f:operator a) (n:nat) : Tot (family a) (decreases n) =
  if n = 0 then (fun _ -> S.emp) else f (iterate f (n - 1))

let rec successive (#a:Type) (f:operator a) (n:nat)
  : Lemma (agrees_below n (iterate f n) (iterate f (n + 1)))
          (decreases n)
  = if n > 0 then successive f (n - 1)

let rec stable_from (#a:Type) (f:operator a) (n:nat) (k:nat{n <= k})
  : Lemma (agrees_below n (iterate f n) (iterate f k))
          (decreases k)
  = if k > n then (
      stable_from f n (k - 1);
      successive f (k - 1)
    )

let fix_pred (#a:Type) (f:operator a) (x:a) (m:K.premem) : prop =
  iterate f (K.level_ m + 1) x m

let fix (#a:Type) (f:operator a) (x:a) : S.slprop =
  S.reveal_slprop_ok ();
  S.reveal_mem_le ();
  introduce forall m. fix_pred f x m ==> fix_pred f x (S.age1_ m) with (
    let n = K.level_ m in
    let p = iterate f (n + 1) x in
    assert (S.hereditary p);
    if n > 0 then stable_from f n (n + 1)
  );
  introduce forall m m'. S.mem_le m m' /\ fix_pred f x m ==> fix_pred f x m' with (
    let p = iterate f (K.level_ m + 1) x in
    assert (S.mem_pred_affine p)
  );
  S.mk_slprop (fix_pred f x)

let fix_approximant (#a:Type) (f:operator a) (n:nat)
  : Lemma (agrees_below n (fix f) (iterate f n))
  = introduce forall x m. K.level_ m < n ==> (fix f x m <==> iterate f n x m)
    with (
      introduce K.level_ m < n ==> (fix f x m <==> iterate f n x m)
      with stable_from f (K.level_ m + 1) n
    )

let unfold_fix (#a:Type) (f:operator a) (x:a)
  : Lemma (fix f x == f (fix f) x)
  = K.mem_pred_ext (fix f x) (f (fix f) x) (fun m ->
      let n = K.level_ m in
      fix_approximant f n;
      assert (agrees_below (n + 1) (f (fix f)) (f (iterate f n)));
      ())

let later_contractive (#a:Type) ()
  : Lemma (contractive (fun (p:family a) x -> S.later (p x)))
  = introduce forall n (p q:family a).
      agrees_below n p q ==>
      agrees_below (n + 1) (fun x -> S.later (p x)) (fun x -> S.later (q x))
    with ()
