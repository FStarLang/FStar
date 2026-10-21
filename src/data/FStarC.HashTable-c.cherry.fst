(*
   Copyright 2008-2026 Microsoft Research

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
module FStarC.HashTable

(* The Cherry implementation.  The OCaml one (FStarC.HashTable.fst) is an
   instance of OCaml's [Hashtbl.Make] per key type, and functors exist only on
   the OCaml backend; this is a hash table written in F*, taking the key's
   [deq] and [hashable] instances as ordinary arguments.

   Its observable behaviour follows [Hashtbl]'s: a power-of-two number of
   buckets, at least 16; a new binding goes to the front of its bucket, and
   [add] replaces the first binding of the key in place; the table doubles
   once it holds more than twice as many bindings as buckets, keeping the
   order within each bucket; [clear] keeps the buckets; [iter] and [fold] go
   through the buckets in order, each from the front.  Iteration order is
   therefore the OCaml build's whenever the hash codes are, which they are for
   small integers but not for strings (FStarC.Hash-c.cherry.fst). *)

open FStarC.Effect
open FStarC.Class.Deq
open FStarC.Class.Hashable

module A = FStarC.Array
module SI = FStarC.SmallInt

noeq type tbl (k v:Type0) = {
  size: ref int;
  data: ref (A.array (list (k & v)));
}

inline_for_extraction
let t (k:Type0) {| deq k |} {| hashable k |} (v:Type0) : Type0 = tbl k v

let nbuckets (#k #v:Type0) (m:tbl k v) : ML int = SI.to_int (A.length !m.data)

let rec buckets_for (want:int) (n:int) : Tot int (decreases (if want <= n then 0 else 1)) =
  if want <= n || n >= 0x100000000000 then n else buckets_for want (n + n)

let index (#k:Type0) {| hashable k |} (n:int) (key:k) : ML SI.t =
  SI.of_int (Hash.to_int (hash key) % n)

let rec find_in (#k #v:Type0) {| deq k |} (key:k) (l:list (k & v)) : ML (option v) =
  match l with
  | [] -> None
  | (key', value) :: l -> if key =? key' then Some value else find_in key l

(* [Some l'] when [key] is bound in [l], with its first binding replaced. *)
let rec replace_in (#k #v:Type0) {| deq k |} (key:k) (value:v) (l:list (k & v))
  : ML (option (list (k & v))) =
  match l with
  | [] -> None
  | (key', value') :: l ->
    if key =? key' then Some ((key, value) :: l)
    else match replace_in key value l with
         | Some l -> Some ((key', value') :: l)
         | None -> None

(* [Some l'] when [key] is bound in [l], with its first binding removed. *)
let rec remove_in (#k #v:Type0) {| deq k |} (key:k) (l:list (k & v))
  : ML (option (list (k & v))) =
  match l with
  | [] -> None
  | (key', value') :: l ->
    if key =? key' then Some l
    else match remove_in key l with
         | Some l -> Some ((key', value') :: l)
         | None -> None

let rec iter_buckets (#k #v:Type0) (d:A.array (list (k & v))) (i n:int)
  (f:list (k & v) -> ML unit) : ML unit =
  if i < n then (f (A.get d (SI.of_int i)); iter_buckets d (i + 1) n f)

(* Bindings go to the back of their new buckets, in the order the old buckets
   are visited, so each new bucket keeps the order its bindings had. *)
let resize (#k #v:Type0) {| hashable k |} (m:tbl k v) : ML unit =
  let old = !m.data in
  let n = nbuckets m in
  let n' = n + n in
  let d = A.make (SI.of_int n') [] in
  iter_buckets old 0 n (fun l ->
    FStarC.List.iter (fun (key, value) ->
      let i = index n' key in
      A.set d i (FStarC.List.append (A.get d i) [(key, value)])) l);
  m.data := d

inline_for_extraction
let create (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (n:int) : ML (t k v) =
  { size = mk_ref 0; data = mk_ref (A.make (SI.of_int (buckets_for n 16)) []) }

inline_for_extraction
let clear (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (m:t k v) : ML unit =
  if !m.size > 0 then begin
    m.size := 0;
    m.data := A.make (A.length !m.data) []
  end

let rec copy_buckets (#k #v:Type0) (src dst:A.array (list (k & v))) (i n:int) : ML unit =
  if i < n then (A.set dst (SI.of_int i) (A.get src (SI.of_int i)); copy_buckets src dst (i + 1) n)

inline_for_extraction
let copy (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (m:t k v) : ML (t k v) =
  let n = nbuckets m in
  let d = A.make (SI.of_int n) [] in
  copy_buckets !m.data d 0 n;
  { size = mk_ref !m.size; data = mk_ref d }

(* Replaces the current binding of the key, if any. *)
inline_for_extraction
let add (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (m:t k v) (key:k) (value:v) : ML unit =
  let i = index (nbuckets m) key in
  let l = A.get !m.data i in
  match replace_in key value l with
  | Some l -> A.set !m.data i l
  | None ->
    A.set !m.data i ((key, value) :: l);
    m.size := !m.size + 1;
    if !m.size > nbuckets m + nbuckets m then resize m

inline_for_extraction
let remove (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (m:t k v) (key:k) : ML unit =
  let i = index (nbuckets m) key in
  match remove_in key (A.get !m.data i) with
  | Some l -> A.set !m.data i l; m.size := !m.size - 1
  | None -> ()

inline_for_extraction
let try_find (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (m:t k v) (key:k) : ML (option v) =
  find_in key (A.get !m.data (index (nbuckets m) key))

inline_for_extraction
let mem (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (m:t k v) (key:k) : ML bool =
  Some? (try_find m key)

inline_for_extraction
let iter (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0)
  (m:t k v) (f:k -> v -> ML unit) : ML unit =
  iter_buckets !m.data 0 (nbuckets m) (FStarC.List.iter (fun (key, value) -> f key value))

let rec fold_buckets (#k #v #a:Type0) (d:A.array (list (k & v))) (i n:int)
  (f:k -> v -> a -> ML a) (acc:a) : ML a =
  if i < n then
    fold_buckets d (i + 1) n f
      (FStarC.List.fold_left (fun acc (key, value) -> f key value acc) acc (A.get d (SI.of_int i)))
  else acc

inline_for_extraction
let fold (#k:Type0) {| deq k |} {| hashable k |} (#v #a:Type0)
  (m:t k v) (f:k -> v -> a -> ML a) (init:a) : ML a =
  fold_buckets !m.data 0 (nbuckets m) f init

inline_for_extraction
let size (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (m:t k v) : ML int =
  !m.size

inline_for_extraction
let of_list (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (l:list (k & v)) : ML (t k v) =
  let m = create (FStarC.List.length l) in
  FStarC.List.iter (fun (key, value) -> add m key value) l;
  m

inline_for_extraction
let keys (#k:Type0) {| deq k |} {| hashable k |} (#v:Type0) (m:t k v) : ML (list k) =
  fold m (fun key _ acc -> key :: acc) []
