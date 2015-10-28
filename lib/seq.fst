(*--build-config
    options:--admit_fsi Set;
    other-files: ext.fst set.fsi seq.fsi
  --*)
(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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


(* A logical theory of sequences indexed by natural numbers in [0, n) *)
module FStar.Seq
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 1 --max_ifuel 1"

(* Representation hidden from clients *)
type seq (a:Type) =
| MkSeq: length:nat -> contents:(n:nat{n<length} -> Tot a) -> seq a

(* Primitive operations on sequences *)

let length s = MkSeq.length s
(*
(match s with
  | MkSeq l c -> l)
*)


val mkSeqContents : s:(seq 'a) -> n:nat{n<length s} -> Tot 'a
let mkSeqContents s n = MkSeq.contents s n
(*
(match s with
| MkSeq l c -> c n)
*)

let create len v =  MkSeq len (fun i -> v)

val exFalso0 : a:Type -> n:nat{n<0} -> Tot a
let exFalso0 'a n = ()

let createEmpty 'a =  (MkSeq 0 (fun i -> (exFalso0 'a i)))


let index s i = mkSeqContents s i

let upd s n v =
 MkSeq (length s) (fun i -> if i=n then v else (mkSeqContents s) i)

let append s1 s2 =
  MkSeq (length s1 + length s2) (fun x -> if x < (length s1) then index s1 x else index s2 (x - (length s1)))

let slice s i j =
  MkSeq (j-i) (fun x -> index s (x + i))


(* Lemmas about length *)
let lemma_create_len n i   = ()
let lemma_len_upd n v s    = ()
let lemma_len_append s1 s2 = ()
let lemma_len_slice s i j  = ()

(* Lemmas about index *)
let lemma_index_create n v i  = ()
let lemma_index_upd1 n v s    = ()
let lemma_index_upd2 n v s i  = ()
let lemma_index_app1 s1 s2 i  = ()
let lemma_index_app2 s2 s2 i  = ()
let lemma_index_slice s i j k = ()

opaque type Eq (#a:Type) (s1:seq a) (s2:seq a) =
  (length s1 = length s2
   /\ (forall (i:nat{i < length s1}).{:pattern (index s1 i); (index s2 i)} (index s1 i == index s2 i)))

(*This should be provable now*)
assume Extensionality: forall (a:Type) (s1:seq a) (s2:seq a).{:pattern (Eq s1 s2)} Eq s1 s2 <==> (s1=s2)

let lemma_eq_intro s1 s2 = ()
let lemma_eq_refl s1 s2  = ()
let lemma_eq_elim s1 s2  = ()
