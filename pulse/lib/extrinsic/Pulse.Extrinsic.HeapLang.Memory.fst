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
type cell_value_of (a:Type0) : Type u#3 =
  | Empty
  | Full: a -> cell_value_of a

let cell_pcm_base_of (#a:Type0) : pcm' (cell_value_of a) = {
  composable = (fun x y -> Empty? x \/ Empty? y);
  op = (fun x y -> match x with | Empty -> y | Full _ -> x);
  one = Empty;
}

let cell_pcm_of (#a:Type0) : pcm (cell_value_of a) = {
  p = cell_pcm_base_of #a;
  comm = (fun x y -> ());
  assoc = (fun x y z -> ());
  assoc_r = (fun x y z -> ());
  is_unit = (fun x -> ());
  refine = (fun _ -> True);
}

let cell_value = cell_value_of int
let cell_pcm = cell_pcm_of #int
let heap = H.heap u#3

let contents_of (#a:Type0) (h:heap) (r:H.core_ref) (v:a) : prop =
  not (H.core_ref_is_null r) /\
  H.select (H.core_ref_as_addr r) h ==
    Some (H.Ref (cell_value_of a) (cell_pcm_of #a) (Full v))

let contents (h:heap) (r:H.core_ref) (v:int) = contents_of h r v

let unchanged_except (h h':heap) (r:H.core_ref) : prop =
  forall a. a <> H.core_ref_as_addr r ==> H.select a h == H.select a h'

let allocation_of (#a:Type0) (h:heap) (v:a) (r:H.core_ref) (h':heap) : prop =
  H.select (H.core_ref_as_addr r) h == None /\
  H.extent h <= H.extent h' /\
  contents_of h' r v /\ unchanged_except h h' r

let allocation (h:heap) (v:int) (r:H.core_ref) (h':heap) = allocation_of h v r h'

let store_of (#a:Type0) (h:heap) (r:H.core_ref) (v:a) (h':heap) : prop =
  (exists old. contents_of #a h r old) /\
  H.extent h' == H.extent h /\
  contents_of h' r v /\ unchanged_except h h' r

let store (h:heap) (r:H.core_ref) (v:int) (h':heap) = store_of h r v h'

let cas (h:heap) (r:H.core_ref) (expected desired:int) (success:bool) (h':heap) : prop =
  exists old.
    contents h r old /\
    (if old = expected
     then success /\ H.extent h' == H.extent h /\
          contents h' r desired /\ unchanged_except h h' r
     else not success /\ h' == h)

let contents_unique_of (#a:Type0) (h:heap) (r:H.core_ref) (v w:a)
  : Lemma (requires contents_of h r v /\ contents_of h r w)
          (ensures v == w)
  = ()

let contents_unique (h:heap) (r:H.core_ref) (v w:int)
  : Lemma (requires contents h r v /\ contents h r w) (ensures v == w)
  = contents_unique_of h r v w

let store_unique_of (#a:Type0) (h:heap) (r:H.core_ref) (v:a) (h1 h2:heap)
  : Lemma (requires store_of h r v h1 /\ store_of h r v h2)
          (ensures h1 == h2)
  = introduce forall a. H.select a h1 == H.select a h2
    with (if a = H.core_ref_as_addr r then () else ());
    H.heap_ext h1 h2

let store_unique (h:heap) (r:H.core_ref) (v:int) (h1 h2:heap)
  : Lemma (requires store h r v h1 /\ store h r v h2) (ensures h1 == h2)
  = store_unique_of h r v h1 h2
let null_unallocated (h:heap) (v:int)
  : Lemma (not (contents h H.core_ref_null v))
  = ()

let cas_unique (h:heap) (r:H.core_ref) (old expected desired:int)
  (success:bool) (h':heap)
  : Lemma
      (requires contents h r old /\ cas h r expected desired success h')
      (ensures success == (old = expected) /\
        (if old = expected then store h r desired h' else h' == h))
  = eliminate exists actual.
      contents h r actual /\
      (if actual = expected
       then success /\ H.extent h' == H.extent h /\
            contents h' r desired /\ unchanged_except h h' r
       else not success /\ h' == h)
    with contents_unique h r old actual

let points_to_of (#a:Type0) (r:H.core_ref) (v:a) : H.slprop u#3 =
  H.pts_to #(cell_value_of a) #(cell_pcm_of #a) r (Full v)

let points_to (r:H.core_ref) (v:int) = points_to_of r v

let points_to_contents_of (#a:Type0) (r:H.core_ref) (v:a) (h:heap)
  : Lemma (requires H.interp (points_to_of r v) h)
          (ensures contents_of h r v)
  = H.interp_pts_to r #(cell_value_of a) #(cell_pcm_of #a) (Full v) h;
    match H.select (H.core_ref_as_addr r) h with
    | None -> ()
    | Some (H.Ref _ _ _) -> ()

let points_to_contents (r:H.core_ref) (v:int) (h:heap)
  : Lemma (requires H.interp (points_to r v) h) (ensures contents h r v)
  = points_to_contents_of r v h

let allocate_of (#a:Type0) (v:a) (h:H.full_heap u#3)
  : r:H.core_ref & h':H.full_heap u#3 {
      allocation_of h v r h' /\ H.interp (points_to_of r v) h'
    }
  = H.intro_emp h;
    H.extend_modifies #(cell_value_of a) #(cell_pcm_of #a) (Full v) h;
    let (| r, h' |) = H.extend #(cell_value_of a) #(cell_pcm_of #a) (Full v) h in
    (| r, h' |)

let allocate (v:int) (h:H.full_heap u#3) = allocate_of v h

let replace_of (#a:Type0) (old:FStar.Ghost.erased a) (desired:a)
  : frame_preserving_upd (cell_pcm_of #a) (Full (FStar.Ghost.reveal old)) (Full desired) =
  fun _ -> compatible_refl (cell_pcm_of #a) (Full desired); Full desired

let replace (old:FStar.Ghost.erased int) (desired:int) = replace_of old desired

let write_of (#a:Type0) (r:H.core_ref) (old desired:a)
  (h:H.full_hheap (points_to_of r old))
  : h':H.full_heap u#3 {
      store_of h r desired h' /\ H.interp (points_to_of r desired) h'
    }
  = points_to_contents_of r old h;
    let update = replace_of old desired in
    H.upd_gen_modifies r (Full old) (Full desired) update h;
    let (| (), h' |) = H.upd_gen_action r (Full old) (Full desired) update h in
    points_to_contents_of r desired h';
    h'

let write (r:H.core_ref) (old desired:int) (h:H.full_hheap (points_to r old)) = write_of r old desired h
