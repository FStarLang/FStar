(*
   Copyright 2020 Microsoft Research

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

module Steel.PCM.HigherReference
open Steel.PCM.Effect
open Steel.PCM.Effect.Atomic
open Steel.PCM.Memory
open FStar.Ghost
open FStar.Real
open Steel.PCM
open Steel.PCM.FractionalPermission

let fractional (a:Type u#1) = option (a & perm)
#push-options "--query_stats"
let composable #a : symrel (fractional a) =
  fun (f0 f1:fractional a) ->
    match f0, f1 with
    | None, _
    | _, None -> True
    | Some (x0, p0), Some (x1, p1) -> x0==x1 /\ (sum_perm p0 p1).v <=. 1.0R
#pop-options
let compose #a (f0:fractional a) (f1:fractional a{composable f0 f1}) : fractional a =
  match f0, f1 with
  | None, f
  | f, None -> f
  | Some (x0, p0), Some (_, p1) -> Some (x0, sum_perm p0 p1)

let pcm_frac #a : pcm (fractional a) = {
  p = {
         composable = composable;
         op = compose;
         one = None
      };
  comm = (fun _ _ -> ());
  assoc = (fun _ _ _ -> ());
  assoc_r = (fun _ _ _ -> ());
  is_unit = (fun _ -> ())
}

module Mem = Steel.PCM.Memory

let ref a = Mem.ref (fractional a) pcm_frac
let pts_to #a r p v = Mem.pts_to r (Some (Ghost.reveal v, p))

let alloc #a x =
  let v = Some (x, full_perm) in
  assert (Steel.PCM.composable pcm_frac v None);
  assert (compatible pcm_frac v v);
  Steel.PCM.Effect.alloc v

assume
val sl_assert (p:slprop)
  : SteelT unit p (fun _ -> p)

assume
val sl_admit (#a:_) (#p:_) (q:a -> slprop)
  : SteelT a p q

assume
val sl_return (#a:_) (p:a -> slprop) (x:a)
  : SteelT a (p x) p

let read (#a:Type) (#p:perm) (#v:erased a) (r:ref a)
  : SteelT a (pts_to r p v) (fun x -> pts_to r p x)
  = let v1 : erased (fractional a) = Ghost.hide (Some (Ghost.reveal v, p)) in
    let v2 = Steel.PCM.Effect.read r v1 in
    let Some (x, _) = v2 in
    sl_return #a (fun x -> pts_to r p x) x

let read_refine (#a:Type) (#p:perm) (q:a -> slprop) (r:ref a)
  : SteelT a (h_exists (fun (v:a) -> pts_to r p v `star` q v))
             (fun v -> pts_to r p v `star` q v)
  = sl_admit _

let write (#a:Type) (#v:erased a) (r:ref a) (x:a)
  : SteelT unit (pts_to r full_perm v) (fun _ -> pts_to r full_perm x)
  = let v_old : erased (fractional a) = Ghost.hide (Some (Ghost.reveal v, full_perm)) in
    let v_new : fractional a = Some (x, full_perm) in
    Steel.PCM.Effect.write r v_old v_new

assume
val drop (p:slprop)
  : SteelT unit p (fun _ -> emp)

let free (#a:Type) (#v:erased a) (r:ref a)
  : SteelT unit (pts_to r full_perm v) (fun _ -> emp)
  = let v_old : erased (fractional a) = Ghost.hide (Some (Ghost.reveal v, full_perm)) in
    Steel.PCM.Effect.free r v_old;
    drop _

(* move these to Mem *)
assume
val mem_share (#a:Type) (#p:pcm a) (r:Mem.ref a p) (v0:erased a) (v1:erased a{Steel.PCM.composable p v0 v1})
  : SteelT unit (Mem.pts_to r (Steel.PCM.op p v0 v1))
                (fun _ -> Mem.pts_to r v0 `star` Mem.pts_to r v1)


assume
val mem_gather (#a:Type) (#p:pcm a) (r:Mem.ref a p) (v0:erased a) (v1:erased a)
  : SteelT (_:unit{Steel.PCM.composable p v0 v1})
           (Mem.pts_to r v0 `star` Mem.pts_to r v1)
           (fun _ -> Mem.pts_to r (Steel.PCM.op p v0 v1))

let share (#a:Type) (#p:perm) (#v:erased a) (r:ref a) =
  let v0 : erased (fractional a) = Ghost.hide (Some (Ghost.reveal v, half_perm p)) in
  assume (p.v <=. 1.0R); //probably change the representation to have a `star` pure (p.v <= 1.0R)
  assert (composable v0 v0);
  mem_share r v0 v0

let gather (#a:Type) (#p0:perm) (#p1:perm) (#v0 #v1:erased a) (r:ref a) =
  let v0 : erased (fractional a) = Ghost.hide (Some (Ghost.reveal v0, p0)) in
  let v1 : erased (fractional a) = Ghost.hide (Some (Ghost.reveal v1, p1)) in
  let _ = mem_gather r v0 v1 in
  sl_return #unit (fun _ -> Mem.pts_to r (compose v0 v1)) ()

assume
val atomic_admit (#a:_) (#uses:_) (#p:_) (q:a -> slprop)
  : SteelAtomic a uses unobservable p q

let ghost_read_refine (#a:Type) (#uses:inames) (#p:perm) (r:ref a) (q:a -> slprop) = atomic_admit _
