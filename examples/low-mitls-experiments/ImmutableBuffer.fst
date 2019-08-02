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
module ImmutableBuffer

module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module Seq = FStar.Seq
module U32 = FStar.UInt32

module IB = LowStar.ImmutableBuffer


(*
 * Testing normalization of lists in the buffer library
 *)
[@"opaque_to_smt"]
let l :list int = [1; 2; 3; 4; 5; 6; 7; 8; 9; 10]

let test2 (lll:list int{List.Tot.length lll > 0 /\
                      List.Tot.length lll <= UInt.max_int 32})
  :HST.ST unit (fun h0 -> HS.is_stack_region (HS.get_tip h0)) (fun _ _ _ -> True)=
  let b = B.gcmalloc_of_list HS.root l in
  assert (B.length b == 10);
  let h = HST.get () in
  assert (B.as_seq h b == Seq.seq_of_list l);
  assert (B.length b == List.Tot.length l);
  let ll = [1;2;3;4;5;6;7;8;9;10;11] in
  HST.push_frame ();
  let b = B.alloca_of_list ll in
  assert (B.length b == 11);
  let h = HST.get () in
  assert (B.as_seq h b == Seq.seq_of_list ll);
  assert (B.length b == List.Tot.length ll);
  let b = B.alloca_of_list lll in
  let h = HST.get () in
  assert (B.as_seq h b == Seq.seq_of_list lll);
  assert (B.length b == List.Tot.length lll);
  HST.pop_frame ()

assume val havoc (#a:Type0) (#rrel #rel:B.srel a) (b:B.mbuffer a rrel rel) :HST.St unit

let test (l:list int{List.Tot.length l == 10}) :HST.St unit =
  let ls = Seq.seq_of_list l in
  let b =  IB.igcmalloc_of_list HS.root l in
  assert (B.length b == 10);
  havoc b;
  IB.recall_contents b ls;
  let h = HST.get () in
  assert (B.as_seq h b == ls);
  assert (B.live h b);
  
  let sb = IB.isub b 0ul 2ul in
  IB.witness_contents sb (Seq.slice ls 0 2);
  havoc sb;
  IB.recall_contents sb (Seq.slice ls 0 2);
  IB.recall_contents b ls;
  let h = HST.get () in
  assert (B.as_seq h b == ls);
  assert (B.as_seq h sb = Seq.slice ls 0 2);

  //test partial API
  let b1 = IB.igcmalloc_of_list_partial HS.root l in
  if B.is_null b1 then ()
  else begin
    assert (B.length b1 == 10);
    IB.recall_contents b1 ls;
    let h = HST.get () in
    assert (B.as_seq h b1 == ls)
  end


(***** Tests for uninitialized buffers *****)
module UB = LowStar.UninitializedBuffer

[@expect_failure]
let test_index_ub (b:UB.ubuffer int) :HST.ST unit (requires (fun h0 -> UB.live h0 b /\ UB.length b == 10)) (ensures (fun _ _ _ -> True))
  = ignore (UB.uindex b 0)

let test_ub () :HST.St unit =
  let b = UB.ugcmalloc #int HS.root 10ul in  //allocate an uninitialized buffer, no initializer
  UB.uupd b 1ul 2;  //update at index 1 with value 2
  let j = UB.uindex b 1ul in  //can now project index 1
  assert (j == 2);  //and check that the value is indeed 2
  //let j = UB.uindex b 4ul in --> this fails since the index 4ul is not initialized
  let b1 = B.gcmalloc HS.root 0 10ul in  //allocate a different regular buffer
  let h0 = HST.get () in
  UB.ublit b1 2ul b 2ul 3ul;  //copy [2, 5) from regular buffer to [2, 5) of uninitialized buffer
  let h1 = HST.get () in
  let j = UB.uindex b 4ul in  //now 4ul is indexable
  assert (j == 0);  //and we can check its value is 0 (from the source buffer)
  let j = UB.uindex b 1ul in  //1ul remains initialized and has the same value as before
  assert (Seq.index (UB.as_seq h0 b) 1 == Seq.index (Seq.slice (UB.as_seq h0 b) 0 2) 1);
  assert (j == 2)


(***** Tests for bigops in the buffer library *****)
#push-options "--max_fuel 0 --max_ifuel 0"
let test_bigops (b1:UB.ubuffer int) (b2:IB.ibuffer int) (b3:B.buffer int) (h h0 h1:HS.mem) : unit =
  let open LowStar.Buffer in
  let l1, l2, l3 = loc_buffer b1, loc_buffer b2, loc_buffer b3 in
  assume (live h b1 /\ live h b2 /\ live h b3);
  assume (loc_disjoint l1 l2 /\ loc_disjoint l2 l3 /\ loc_disjoint l3 l1);
  assume (modifies (loc_union l1 (loc_union l2 l3)) h0 h1);
  assert (all_disjoint [l1; l2; l3]);
  assert (all_live h [buf b1; buf b2; buf b3]);
  assert (modifies (loc_union_l [l1; l2; l3]) h0 h1)
#pop-options


(***** Tests for freezable buffers *****)

module PF = LowStar.PrefixFreezableBuffer

#push-options "--max_fuel 0 --max_ifuel 0"

assume val havoc_pf (b:PF.buffer)
  : HST.ST unit (requires (fun _ -> True))
                (ensures  (fun h0 _ h1 ->
		           PF.frozen_until (PF.as_seq h0 b) == PF.frozen_until (PF.as_seq h1 b)))

let test_pf () : HST.St unit =
  let open LowStar.PrefixFreezableBuffer in
  let b = gcmalloc HS.root 5ul in

  upd b 4ul 1uy;
  upd b 5ul 2uy;
  upd b 6ul 3uy;
  upd b 7ul 4uy;
  upd b 8ul 5uy;

  freeze b 5ul;

  upd b 5ul 2uy;
  upd b 6ul 3uy;
  upd b 7ul 4uy;
  upd b 8ul 5uy;


  let snap = Ghost.hide (Seq.create 1 1uy) in
  witness_slice b 4ul 5ul snap;
  havoc_pf b;

  recall_slice b 4ul 5ul snap;

  let h = HST.get () in
  assert (Seq.equal (Seq.slice (as_seq h b) 4 5) (Ghost.reveal snap));

  ()

// (*
//  * An example of a two elements buffer
//  * The first element increases monotonically and the second element remains same
//  *)

// type immutable_sub_buffer (a:Type0) (rrel:B.srel a) = B.mbuffer a rrel (crel a)

// let trel :B.srel int =
//   fun s1 s2 -> Seq.length s1 == 2 ==> (Seq.length s2 == 2 /\ Seq.index s1 0 <= Seq.index s2 0 /\ Seq.index s2 1 == Seq.index s1 1)

// type tbuffer = b:B.mbuffer int trel trel{B.length b == 2}

// let tsub (b:tbuffer)
//   :HST.Stack (immutable_sub_buffer _ _)
//              (requires (fun h -> B.live h b))
//              (ensures  (fun h y h' -> h == h' /\ y == B.mgsub b 1ul 1ul (crel int)))
//   = B.msub b 1ul 1ul (crel int)

// let test_immutable_sub (b:tbuffer)
//   :HST.ST unit (requires (fun h0    -> B.recallable b /\ Seq.index (B.as_seq h0 b) 1 == 2))
//                (ensures  (fun _ _ _ -> True))
//   = B.recall b;

//     let s = Seq.create 1 2 in

//     let bb = tsub b in
//     let _ = B.witness_p bb (cpred s) in  //witness the contents of the subbuffer

//     havoc bb; havoc b;
//     B.recall_p bb (cpred s);
//     let h = HST.get () in
//     assert (B.as_seq h bb == s)
