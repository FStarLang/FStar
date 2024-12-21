(*
   Copyright 2008-2022 Microsoft Research

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
///
/// UPD. November 8, 2022 -- added support for custom equivalence relation-aware
/// pigeon principle lemma.
/// UPD. November 23, 2022 -- added interface file

module L = FStar.List.Tot
module S = FStar.Seq 

(** The type of natural numbers bounded by [n] *)
inline_for_extraction
let fin (n: nat) = k: int {0 <= k /\ k < n} 

(** Newer synonym. We perhaps should choose one over another globally.
    [under] is also defined in IntegerIntervals.fst, along with other 
    often used finite intervals. *)
inline_for_extraction
let under (p:nat) = x:nat {x<p}

(** Length-indexed list *)
inline_for_extraction
let vect (n: nat) (a: Type) = l: list a {L.length l = n}

(** Length-indexed sequence *)
inline_for_extraction
let seqn (n: nat) (a: Type) = s: S.seq a {S.length s = n}

(** [in_ s] is the type of a valid index into the sequence [s] *)
inline_for_extraction
let in_ (#a: Type) (s: S.seq a) = n: nat{n < S.length s}

(** Find an index of an element in [s] starting from [i] that validates [p]  *)
val find (#a: Type) (s: S.seq a) (p: (a -> bool)) (i: under (S.length s))
    : Pure (option (in_ s))
      (requires True)
      (ensures (function
                | None -> (forall (k: nat{i <= k /\ k < S.length s}). p (S.index s k) == false)
                | Some j -> i <= j /\ p (S.index s j)))
      (decreases (S.length s - i))  

(** Given a sequence [s] all of whose elements are at most [n], if the
    length of [s] is greater than [n], then there are two distinct
    indexes in [s] that contain the same element *)
val pigeonhole (#n: pos) (s: S.seq (under n))
    : Pure (in_ s & in_ s)
      (requires S.length s = n + 1)
      (ensures (fun (i1, i2) -> i1 < i2 /\ S.index s i1 = S.index s i2))
      (decreases n)  

(** Here we prepare to prove pigeonhole principle for a finite sequence
    with a custom equivalence relation (as opposed to eqtype).
    
    Think setoids. *)

(** Following code is extracted from CuteCAS, which will eventually make 
    its way into F* -- when I wrap things up with most important notions
    of abstract algebra. 
    
    As I port more code from my CAS project to F*, such things will be
    moved to separate modules. -- Alex Rozanov *)
 
inline_for_extraction
type binary_relation (a: Type) = a -> a -> bool
 
(** For performance reasons, forall definitions are best kept hidden from SMT.
    Use reveal_opaque when you really need it. Or use refl/trans/symm lemmas
    below to keep the context clean. *)

val is_reflexive (#a:Type) (r: binary_relation a) : Type0
val is_symmetric (#a:Type) (r: binary_relation a) : Type0
val is_transitive (#a:Type) (r: binary_relation a) : Type0

val is_reflexive_intro (#a:Type) (r: binary_relation a)
  : Lemma (requires forall (x:a). r x x) (ensures is_reflexive r)
  
val is_symmetric_intro (#a:Type) (r: binary_relation a)
  : Lemma (requires forall (x:a). r x x) (ensures is_reflexive r)
 
val is_transitive_intro (#a:Type) (r: binary_relation a)
  : Lemma (requires forall (x:a). r x x) (ensures is_reflexive r)
   
(** Textbook stuff on equivalence relations *)
type equivalence_relation (a: Type) 
  = r:binary_relation a { is_reflexive r /\ is_symmetric r /\ is_transitive r }

val refl_lemma (#a:Type) (eq: equivalence_relation a) (x:a) 
  : Lemma (eq x x)
   
val symm_lemma (#a:Type) (eq:equivalence_relation a) (x y:a) 
  : Lemma (eq x y == eq y x)  
  
val trans_lemma (#a:Type) (eq: equivalence_relation a) (x y z:a)
  : Lemma (requires (eq x y \/ eq y x) /\ (eq y z \/ eq z y))  
          (ensures (x `eq` z) && (z `eq` x))    
  

(** (contains) predicate, but with custom comparison operation (a->a->bool) *) 
[@@"opaque_to_smt"]
let contains_eq #a (eq: equivalence_relation a) (s: S.seq a) (x:a)
  = exists (i:under (S.length s)). eq x (S.index s i)

val contains_eq_means_nonempty (#a:Type) (eq:equivalence_relation a) (s: S.seq a) (x:a)
  : Lemma (requires contains_eq eq s x) 
          (ensures S.length s > 0) 
          [SMTPat(contains_eq eq s x)]  

(** a type of all elements present in a given sequence *)
let items_of #a (eq: equivalence_relation a) (s: S.seq a) 
  = x:a { contains_eq eq s x } 
   
(** retrieves the index of an element given prior knowledge of its presense 
    unlike find function above, that returns option, this one guarantees
    success, thus returning bare index instead. *)
val find_eq (#a:Type) (eq:equivalence_relation a) (s: S.seq a) (x:a { contains_eq eq s x })
  : (i: nat { (i < S.length s) 
          /\ (x `eq` S.index s i) 
          /\ (forall (j: under i). not (x `eq` S.index s j)) })  
  
(** pigeonhole principle for setoids:
    If we have a nonempty sequence (all), and a sequence (s),
    and we know in advance that each item of (s) equals some 
    item in (all), equals meaning (eq), not (==),
    then we automatically know that there are at least
    2 equivalent elements in (s).
  
    This procedure returns the first such pair. *)

val pigeonhole_eq (#a:Type) (eq: equivalence_relation a) 
                            (holes: S.seq a{S.length holes > 0}) 
                            (pigeons: S.seq (items_of eq holes))
  : Pure (under (S.length pigeons) & under (S.length pigeons))
         (requires S.length pigeons > S.length holes)
         (ensures (fun (i1, i2) -> i1 < i2 /\ (S.index pigeons i1 `eq` S.index pigeons i2)))
         (decreases S.length holes)  
