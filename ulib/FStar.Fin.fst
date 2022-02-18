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

module FStar.Fin

/// This module is supposed to contain various lemmas about
/// finiteness. For now, it mainly provides a basic pigeonhole
/// principle
///
/// TODO: We might generalize this to also support general utilities
/// for reasoning about cardinality, relation with injections and
/// surjections, etc.

module L = FStar.List.Tot
module S = FStar.Seq

(** The type of natural numbers bounded by [n] *)
let fin (n: nat) = k: int{0 <= k /\ k < n}

(** Length-indexed list *)
let vect (n: nat) (a: Type) = l: list a {L.length l = n}

(** Length-indexed sequence *)
let seqn (n: nat) (a: Type) = s: S.seq a {S.length s = n}

(** [in_ s] is the type of a valid index into the sequence [s] *)
let in_ (#a: Type) (s: S.seq a) = n: nat{n < S.length s}

(** Find an index of an element in [s] starting from [i] that validates [p]  *)
let rec find (#a: Type) (s: S.seq a) (p: (a -> bool)) (i: in_ s)
    : Pure (option (in_ s))
      (requires True)
      (ensures
        (function
          | None -> (forall (k: nat{i <= k /\ k < S.length s}). p (S.index s k) == false)
          | Some j -> i <= j /\ p (S.index s j)))
      (decreases (S.length s - i)) =
  if p (S.index s i) then Some i else if i + 1 < S.length s then find #a s p (i + 1) else None

(** Given a sequence [s] all of whose elements are at most [n], if the
    length of [s] is greater than [n], then there are two distinct
    indexes in [s] that contain the same element *)
let rec pigeonhole (#n: nat) (s: S.seq (fin n))
    : Pure (in_ s * in_ s)
      (requires S.length s = n + 1)
      (ensures (fun (i1, i2) -> i1 < i2 /\ S.index s i1 = S.index s i2))
      (decreases n) =
  if n = 0
  then (match S.index s 0 with )
  else
    if n = 1
    then
      (assert (S.index s 0 = S.index s 1);
        0, 1)
    else
      let k0 = S.index s 0 in
      match find s (fun k -> k = k0) 1 with
      | Some i -> 0, i
      | None ->
        let reduced_s:S.seq (fin (n - 1)) =
          S.init #(fin (n - 1))
            n
            (fun i ->
                let k:nat = S.index s (i + 1) in
                assert (k <> k0);
                if k < k0 then (k <: fin (n - 1)) else (k - 1 <: fin (n - 1)))
        in
        let i1, i2 = pigeonhole reduced_s in
        i1 + 1, i2 + 1

