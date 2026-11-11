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
module Pulse.Extrinsic.HeapLang.Memory

module H = PulseCore.Heap
open FStar.PCM

noeq
type cell_value : Type u#3 =
  | Empty
  | Full: int -> cell_value

let cell_pcm_base : pcm' cell_value = {
  composable = (fun x y -> Empty? x \/ Empty? y);
  op = (fun x y -> match x with | Empty -> y | Full _ -> x);
  one = Empty;
}

let cell_pcm : pcm cell_value = {
  p = cell_pcm_base;
  comm = (fun x y -> ());
  assoc = (fun x y z -> ());
  assoc_r = (fun x y z -> ());
  is_unit = (fun x -> ());
  refine = (fun _ -> True);
}

let heap = H.heap u#3

let contents (h:heap) (r:H.core_ref) (v:int) : prop =
  not (H.core_ref_is_null r) /\
  H.select (H.core_ref_as_addr r) h ==
    Some (H.Ref cell_value cell_pcm (Full v))

let unchanged_except (h h':heap) (r:H.core_ref) : prop =
  forall a. a <> H.core_ref_as_addr r ==> H.select a h == H.select a h'

let allocation (h:heap) (v:int) (r:H.core_ref) (h':heap) : prop =
  H.select (H.core_ref_as_addr r) h == None /\
  H.extent h <= H.extent h' /\
  contents h' r v /\ unchanged_except h h' r

let store (h:heap) (r:H.core_ref) (v:int) (h':heap) : prop =
  (exists old. contents h r old) /\
  H.extent h' == H.extent h /\
  contents h' r v /\ unchanged_except h h' r

let cas (h:heap) (r:H.core_ref) (expected desired:int) (success:bool) (h':heap) : prop =
  exists old.
    contents h r old /\
    (if old = expected
     then success /\ H.extent h' == H.extent h /\
          contents h' r desired /\ unchanged_except h h' r
     else not success /\ h' == h)

let contents_unique (h:heap) (r:H.core_ref) (v w:int)
  : Lemma (requires contents h r v /\ contents h r w)
          (ensures v == w)
  = ()

let store_unique (h:heap) (r:H.core_ref) (v:int) (h1 h2:heap)
  : Lemma (requires store h r v h1 /\ store h r v h2)
          (ensures h1 == h2)
  = introduce forall a. H.select a h1 == H.select a h2
    with (if a = H.core_ref_as_addr r then () else ());
    H.heap_ext h1 h2

let null_unallocated (h:heap) (v:int)
  : Lemma (not (contents h H.core_ref_null v))
  = ()

let points_to (r:H.core_ref) (v:int) : H.slprop u#3 =
  H.pts_to #cell_value #cell_pcm r (Full v)

let points_to_contents (r:H.core_ref) (v:int) (h:heap)
  : Lemma (requires H.interp (points_to r v) h)
          (ensures contents h r v)
  = H.interp_pts_to r #cell_value #cell_pcm (Full v) h;
    match H.select (H.core_ref_as_addr r) h with
    | None -> ()
    | Some (H.Ref _ _ _) -> ()

let allocate (v:int) (h:H.full_heap u#3)
  : r:H.core_ref & h':H.full_heap u#3 {
      allocation h v r h' /\ H.interp (points_to r v) h'
    }
  = H.intro_emp h;
    H.extend_modifies #cell_value #cell_pcm (Full v) h;
    let (| r, h' |) = H.extend #cell_value #cell_pcm (Full v) h in
    (| r, h' |)

let replace (old:FStar.Ghost.erased int) (desired:int) : frame_preserving_upd cell_pcm (Full old) (Full desired) =
  fun _ -> compatible_refl cell_pcm (Full desired); Full desired

let write (r:H.core_ref) (old desired:int)
  (h:H.full_hheap (points_to r old))
  : h':H.full_heap u#3 {
      store h r desired h' /\ H.interp (points_to r desired) h'
    }
  = points_to_contents r old h;
    let update = replace old desired in
    H.upd_gen_modifies r (Full old) (Full desired) update h;
    let (| (), h' |) = H.upd_gen_action r (Full old) (Full desired) update h in
    points_to_contents r desired h';
    h'
