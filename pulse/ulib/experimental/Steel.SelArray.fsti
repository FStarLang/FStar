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
   limitations under the License.o
*)

module Steel.SelArray
open Steel.Memory
open Steel.SelEffect
open FStar.Ghost
module U32 = FStar.UInt32

let contents (t:Type u#0) = erased (FStar.Seq.seq t)
let length #t (r:contents t) : GTot nat = Seq.length r

val array (t:Type u#0) : Type u#0

val is_array (#a:Type0) (r:array a) : slprop u#1
val array_sel (#a:Type0) (r:array a) : selector (Seq.seq a) (is_array r)

[@@ __steel_reduce__]
let varray' #a r : vprop' =
  {hp = is_array r;
   t = Seq.seq a;
   sel = array_sel r}

[@@ __steel_reduce__]
unfold
let varray r = VUnit (varray' r)

[@@ __steel_reduce__]
let asel (#a:Type) (#p:vprop) (r:array a)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (varray r) /\ True)})
  = h (varray r)

val alloc (#t:Type) (x:t) (n:U32.t)
  : SteelSel (array t)
             vemp
             (fun r -> varray r)
             (requires fun _ -> True)
             (ensures fun _ r h1 -> asel r h1 == Seq.create (U32.v n) x)

val index (#t:Type) (r:array t) (i:U32.t)
  : SteelSel t
             (varray r)
             (fun _ -> varray r)
             (requires fun h -> U32.v i < length (asel r h))
             (ensures fun h0 x h1 ->
               U32.v i < length (asel r h1) /\
               asel r h0 == asel r h1 /\
               x == Seq.index (asel r h1) (U32.v i))

val upd (#t:Type) (r:array t) (i:U32.t) (x:t)
  : SteelSel unit
             (varray r)
             (fun _ -> varray r)
             (requires fun h -> U32.v i < length (asel r h))
             (ensures fun h0 _ h1 ->
               U32.v i < length (asel r h0) /\
               asel r h1 == Seq.upd (asel r h0) (U32.v i) x)

val free (#t:Type) (r:array t)
  : SteelSel unit
             (varray r)
             (fun _ -> vemp)
             (requires fun _ -> True)
             (ensures fun _ _ _ -> True)
