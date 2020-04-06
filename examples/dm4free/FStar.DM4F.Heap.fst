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
module FStar.DM4F.Heap

open FStar.Classical
open FStar.Set

module F = FStar.FunctionalExtensionality

noeq type heap_rec = {
  next_addr: nat;
  memory   : F.restricted_t nat (fun _ -> option (a:Type0 & a))
}

type heap = h:heap_rec{(forall (n:nat). n >= h.next_addr ==> None? (h.memory n))}

private let consistent (h0:heap) (h1:heap) =
  forall n x y. h0.memory n == Some x /\ h1.memory n == Some y ==> dfst x == dfst y

noeq type ref (a:Type0) = {
  addr: nat;
  init: a
}

let addr_of #a r = r.addr

let compare_addrs #a #b r1 r2 = r1.addr = r2.addr

let contains_a_well_typed (#a:Type0) (h:heap) (r:ref a) =
  Some? (h.memory r.addr) /\ dfst (Some?.v (h.memory r.addr)) == a
  (* exists (x:a). h.memory r.addr == Some (| a, x |) *)

(* Select. *)
let sel_tot #a h r =
  match h.memory r.addr with
  | Some (| _ , x |) -> x

let sel #a h r =
  if FStar.StrongExcludedMiddle.strong_excluded_middle (h `contains_a_well_typed` r) then
    sel_tot #a h r
  else r.init

(* Update. *)
let upd_tot #a h0 r x =
  { h0 with memory = F.on_dom nat (fun r' -> if r.addr = r'
			                then Some (| a, x |)
                                        else h0.memory r') }

let upd #a h0 r x =
  if FStar.StrongExcludedMiddle.strong_excluded_middle (h0 `contains_a_well_typed` r)
  then upd_tot h0 r x
  else
    if r.addr >= h0.next_addr
    then (* alloc at r.addr *)
      { next_addr = r.addr + 1;
        memory    = F.on_dom nat (fun (r':nat) -> if r' = r.addr
			                    then Some (| a, x |)
                                            else h0.memory r') }
    else (* type modifying update at r.addr *)
      { h0 with memory = F.on_dom nat (fun r' -> if r' = r.addr
				             then Some (| a, x |)
                                             else h0.memory r') }

(* Generating a fresh reference for the given heap. *)

let alloc #a h0 x =
  let r = { addr = h0.next_addr; init = x } in
  let h1 = { next_addr = r.addr + 1;
             memory    = F.on_dom nat (fun (r':nat) -> if r' = r.addr
			                         then Some (| a, x |)
                                                 else h0.memory r') }
  in
  assert (let h2 = upd h0 r x in
          FStar.FunctionalExtensionality.feq h1.memory h2.memory);
  r, h1

let contains (#a:Type) (h:heap) (r:ref a): Tot Type0 = Some? (h.memory r.addr)

let contains_a_well_typed_implies_contains #a h r = ()

let contains_addr_of #a #b h r1 r2 = ()

let alloc_lemma #a h0 x = ()

let sel_same_addr_of (#a:Type) (x:ref a) (y:ref a) (h:heap)
  :Lemma (requires (addr_of x = addr_of y /\ h `contains_a_well_typed` x /\ h `contains_a_well_typed` y))
         (ensures  (sel h x == sel h y))
   [SMTPat (sel h x); SMTPat (sel h y)]
  = ()

let sel_upd1 #a h r v r' = ()

let sel_upd2 #a #b h k1 k2 v = ()

let upd_sel #a h r =
  assert (FStar.FunctionalExtensionality.feq (upd h r (sel h r)).memory h.memory)

let emp = {
  next_addr = 0;
  memory    = F.on_dom nat (fun (r:nat) -> None)
}

let in_dom_emp #a k = ()

let upd_contains #a #b h r v r' = ()

let upd_contains_a_well_typed #a #b h r v r' = ()

let lemma_modifies_trans m1 m2 m3 s1 s2 = ()

let lemma_sel_tot_is_sel_if_contains_a_well_typed #a h r = ()

let lemma_upd_tot_is_upd_if_contains_a_well_typed #a h r x = ()
