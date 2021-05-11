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

let contents (t:Type u#0) = FStar.Seq.seq t
let length #t (r:contents t) : GTot nat = Seq.length r

val array (t:Type u#0) : Type u#0

val is_array (#a:Type0) (r:array a) : slprop u#1
val array_sel (#a:Type0) (r:array a) : selector (contents a) (is_array r)

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
             emp
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
             (fun _ -> emp)
             (requires fun _ -> True)
             (ensures fun _ _ _ -> True)


(* AF: Non-selector version of the Array module, currently unused in Steel
   TODO: Port this to the selector version

let contents (t:Type u#0) = erased (FStar.Seq.seq t)
let length #t (r:contents t) : GTot nat = Seq.length r
let perm = perm * erased nat
let full_perm (n:erased nat) : perm = full_perm, n
let is_writeable (p:perm) = fst p == Steel.FractionalPermission.full_perm
let is_freeable #t (r:contents t) (p:perm) = p == full_perm (length r)
let half_perm (p:perm) = half_perm (fst p), snd p
let sum_perm (p q:perm) = sum_perm (fst p) (fst q), snd p

val array (t:Type u#0) : Type u#0

// x:array int;
// is_array x full_perm (Seq.create 20 0) : slprop

val is_array (#t:_) (x:array t) (p:perm) (v:contents t) : slprop u#1

val alloc (#t:Type) (x:t) (n:U32.t)
  : SteelT (array t)
           (requires emp)
           (ensures fun a -> is_array a (full_perm (U32.v n)) (Seq.create (U32.v n) x))

val read (#t:Type) (#p:perm) (#r:contents t) (a:array t) (i:U32.t { U32.v i < length r })
  : Steel t
          (is_array a p r)
          (fun _ -> is_array a p r)
          (fun _ -> True)
          (fun _ x _ -> x == Seq.index r (U32.v i))

val write (#t:Type) (#p:perm{is_writeable p}) (#r:contents t) (a:array t) (i:U32.t { U32.v i < length r }) (x:t)
  : SteelT unit
          (is_array a p r)
          (fun _ -> is_array a p (Seq.upd r (U32.v i) x))

val adjacent (#t:_) (al ar:array t) : prop

val split (#t:Type) (#p:perm) (#r:contents t) (a:array t) (i:U32.t { U32.v i <= length r })
  : Steel (array t & array t)
          (is_array a p r)
          (fun (al, ar) ->
             let prefix, suffix = Seq.split r (U32.v i) in
             is_array al p prefix `star` is_array ar p suffix)
          (fun _ -> True)
          (fun _ (al, ar) _ -> adjacent al ar)

val join (#t:Type) (#p:perm) (#rl #rr:contents t) (al ar:array t)
  : Steel (array t)
          (is_array al p rl `star` is_array ar p rr)
          (fun a -> is_array a p (Seq.append rl rr))
          (fun _ -> adjacent al ar)
          (fun _ _ _ -> True)

val share (#t:Type) (#uses:_) (#p:perm) (#r:contents t) (a:array t) (i:U32.t { U32.v i < length r })
  : SteelGhostT unit uses
           (is_array a p r)
           (fun _ -> is_array a (half_perm p) r `star` is_array a (half_perm p) r)

val gather (#t:Type) (#uses:_) (#p #p':perm) (#r #r':contents t) (a:array t) (i:U32.t { U32.v i < length r })
  : SteelGhostT unit uses
           (is_array a p r `star` is_array a p' r')
           (fun _ -> is_array a (sum_perm p p') r)

val free (#t:Type) (#r:contents t) (#p:perm{is_freeable r p}) (a:array t)
  : SteelT unit
           (is_array a p r)
           (fun _ -> emp)
*)
