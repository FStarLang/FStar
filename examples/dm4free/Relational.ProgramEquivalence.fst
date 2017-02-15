module Relational.ProgramEquivalence

open FStar.List.Tot
open FStar.DM4F.Heap
open FStar.DM4F.Heap.ST

(* reifiable let f () :STNull unit = *)
(*   let r = alloc_weak 0 in *)
(*   () *)

(* let f_obs (h0:heap) = *)
(*   let _, h1 = reify (f ()) h0 in *)
(*   assert (forall (a:Type) (r:ref a). h0 `contains_a_well_typed` r ==> sel h0 r == sel h1 r) *)

(* reifiable let f_1 () :STNull int = *)
(*   let r_1 = alloc_weak 1 in *)
(*   let r_2 = alloc_weak 1 in *)
(*   read_weak r_1 + read_weak r_2 *)

(* reifiable let f_2 () :STNull int = *)
(*   let r_1 = alloc_weak 2 in *)
(*   read_weak r_1 *)

(* let f_1_f_2_obs (h_0:heap) :unit = *)
(*   let r_1, h_1 = reify (f_1 ()) h_0 in *)
(*   let r_2, h_2 = reify (f_1 ()) h_0 in *)
(*   assert (r_1 = r_2 /\ *)
(*           (forall (a:Type) (r:ref a). h_0 `contains` r ==> *)
(* 	                         (sel h_1 r == sel h_0 r /\ *)
(* 				  sel h_2 r == sel h_0 r))) *)

let contains_well_typed_refs (h:heap) (s:list (ref nat)) =
  forall (r:ref nat). memP r s ==> h `contains_a_well_typed` r

type fp = l:list (ref nat)

type ctr (inv:heap -> fp -> Type0) =
  s:fp
  -> ST nat (requires (fun h0       -> inv h0 s))
          (ensures  (fun h0 _ h1 -> inv h1 s))

noeq abstract type t =
  | C: inv:(heap -> fp -> Type0) -> fp:fp -> c:(ctr inv) -> t

abstract let good_t (t:t) (h:heap) = (C?.inv t) h (C?.fp t)

abstract let inv_0 (h:heap) (fp:fp) :Type0 =
  h `contains_well_typed_refs` fp /\
  length fp = 1

reifiable private let incr_0 :(ctr inv_0) =
  fun s ->
    let r = hd s in
    let c = read_weak r in
    write_weak r (c + 2);
    c

reifiable let ctr_0 () :ST t (requires (fun h0 -> True)) (ensures (fun _ r h1 -> good_t r h1))
  = let r = alloc_weak 2 in
    C inv_0 [r] incr_0

abstract let inv_1 (h:heap) (fp:fp) :Type0 =
  h `contains_well_typed_refs` fp /\
  length fp = 2

reifiable private let incr_1 :(ctr inv_1) =
  fun s ->
    let r_1 = hd s in
    let r_2 = hd (tl s) in
    let c_1 = read_weak r_1 in
    let c_2 = read_weak r_2 in
    write_weak r_1 (c_1 + 1);
    write_weak r_2 (c_2 + 1);
    c_1 + c_2

reifiable let ctr_1 (): ST t (requires (fun h0 -> True)) (ensures (fun _ r h1 -> good_t r h1))
  = let r_1 = alloc_weak 1 in
    let r_2 = alloc_weak 1 in
    C inv_1 [r_1; r_2] incr_1


let ctr0_ctr1_obs (h:heap) :unit =
  let c0, h0 = reify (ctr_0 ()) h in
  let c1, h1 = reify (ctr_1 ()) h in

  let n, h0 =
    match c0 with
    | C _ s f -> reify (let _ = f s in f s) h0
  in
  let m, h1 =
    match c1 with
    | C _ s f -> reify (let _ = f s in f s) h1
  in
  assert (n = m /\
          (forall (a:Type) (r:ref a). h `contains` r ==> (sel h r == sel h0 r /\
	                                             sel h r == sel h1 r)))
