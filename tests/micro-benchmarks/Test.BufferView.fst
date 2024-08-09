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
module Test.BufferView
open FStar.HyperStack
open FStar.HyperStack.ST
module L = LowStar.BufferView
module B = LowStar.Buffer
module LM = LowStar.Modifies

(** This is test program for LowStar.BufferView
  * It treats a `B.buffer int` as a `L.buffer (int * int)`
  * It also combines the two with a usage of LowStar.Modifies
  **)


let loc_vb #a (x:L.buffer a) = LM.loc_buffer (L.as_buffer x)

/// Defining the view:
let v : L.view int (int & int) =
  let get (s:Seq.lseq int 2) : int & int = Seq.index s 0, Seq.index s 1 in
  let put (x, y) : Seq.lseq int 2 = Seq.upd (Seq.create 2 x) 1 y in
  assert (forall x. put (get x) `Seq.equal` x); //requires a use of extensional equality
  L.View 2 get put

/// A convenience wrapper on LowStar.Buffer
let bsel #a h (x:B.buffer a) (i:nat{i<B.length x}) =
  Seq.index (B.as_seq h x) i

/// You can use an L.buffer without thinking about its underlying B.buffer
let use_view (n:pos) (i:nat{i<n}) (vb:L.buffer (int & int) {L.length vb = n}) (h:mem)
  : Ghost mem
    (requires L.live h vb)
    (ensures (fun h' ->
                L.live h' vb /\
                LM.modifies (loc_vb vb) h h' /\
                L.sel h' vb i = (17, 42)))
  = let h' = L.upd h vb i (17, 42) in
    let h'' = L.upd h' vb i (17, snd (L.sel h' vb i)) in
    h''


/// This test function:
///    -- constructs the view
///    -- uses the view to read and write from the underlying buffer
///    -- relates the final contents of the view back to the underlying buffer
/// Its spec is entirely in terms of B.buffer, although internally it uses L.buffer
let test (n:pos) (i:nat {i < n}) (b:B.buffer int {B.length b = FStar.Mul.(2 * n)}) (h:mem)
  : Ghost mem
          (requires B.live h b)
          (ensures (fun h' ->
                      let open FStar.Mul in
                      B.live h' b /\
                      LM.modifies (LM.loc_buffer b) h h' /\
                      bsel h' b (i * 2) == 17 /\
                      bsel h' b (i * 2 + 1) == 42))
  = let open FStar.Mul in
    let vb  = L.mk_buffer_view b v in
    //Call these lemmas explicitly to relate vb back to b
    L.as_buffer_mk_buffer_view b v;
    L.get_view_mk_buffer_view b v;
    L.length_eq vb;
    let x, y = L.sel h vb i in
    //call L.get_sel to relate L.sel to bsel
    L.get_sel h vb i;
    assert (x == bsel h b (i * 2));
    assert (y == bsel h b ((i * 2) + 1));
    let h' = use_view n i vb h in
    //call L.get_sel to relate L.sel to bsel
    L.get_sel h' vb i;
    h'
