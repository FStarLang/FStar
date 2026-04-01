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

   Author: A. Rozanov
*)

module FStar.Seq.Partitions
 
open FStar.Seq
open FStar.IntegerIntervals

(**
  This module implements theory for duplicate-less seqence partitions
  We only work with eqtypes here.

  Here we call 
  - a (finite) [set] a sequence with no repeating elements,
  - a [part] of a given set [s] a subset sequence entirely contained in [s], 
  and 
  - a [partition] of a given set [s] a set of non-intersecting subsets
    such that its union contains the same set of elements as [s].
    More precisely, a (p: seq (seq t)) is a partition of (s: seq t)
    exactly when 
      * [s] is a set (i.e. no repeating elements)
      * all sequences in [p] are subsets of [s]
      * there are no intersections between subsets in [p]
      * any element [x] in [s] is contained in some subset among [p]

  We prove that total length of all subsets in partition [p]
  should always add up to the length of [s].
*)

(* a seq with no intersections can be thought of as a set, if
   we discard the order and only count membership *)
let seq_is_set (#t: eqtype) (s: seq t) = forall (x:t). count x s <= 1

(* in this module, we restrict most of our definitions to sets,
   even though some would have worked with general seqs *)
let is_subset_of (#t: eqtype) (subset: seq t) (superset: seq t) 
  : Pure prop (requires seq_is_set subset /\ seq_is_set superset)
              (ensures fun _ -> True)
  = forall (x:t). ((x `mem` subset) ==> (x `mem` superset))
  
(* set equality only accounts for mem, disregarding element order *)
let set_equals (#t: eqtype) (a b: seq t)
  : Pure prop (requires seq_is_set a /\ seq_is_set b)
              (ensures fun _ -> True)
  = forall (x:t). ((x `mem` a) <==> (x `mem` b))
  
(* True if two sets share no elements *)
let no_intersections (#t: eqtype) (a b: seq t)
  : Pure prop (requires seq_is_set a /\ seq_is_set b)
              (ensures fun _ -> True)
  = forall (x:t). not ((x `mem` a) && (x `mem` b))
  
(* True if any pair of sets from [p] has empty intersection *)
let rec no_intersections_among (#t: eqtype) (p: seq (seq t)) 
  : Pure prop (requires (forall (i: under (length p)). seq_is_set (index p i)))
              (ensures fun _ -> True)         
              (decreases length p)
   = length p == 0 \/
     ((length p > 0) /\
      ((forall (i: under (length (tail p))). no_intersections (head p) (index (tail p) i)) 
                                      /\ no_intersections_among (tail p)))


(* True if each set in the collection [parts] is a subset of [s] *)
let are_parts_of (#t: eqtype) (parts: seq (seq t)) (s: seq t)
  = seq_is_set s /\
    (forall (i: under (length parts)). seq_is_set (index parts i) 
                                /\ (index parts i `is_subset_of` s))

(* true if the element [x] is found in one of the sets in [parts] collection 
   this is a general property, it does not require the collection of parts
   to be free of duplicates *)
  
let rec is_found_in (#t:eqtype) (x:t) (parts: seq (seq t))
  : Tot bool (decreases length parts) =     
    if length parts = 0 then false
    else (x `mem` (head parts)) || (x `is_found_in` (tail parts))

val remove_element : (#t: eqtype) -> (s: seq t) -> (x: t) 
  -> Pure (seq t) (requires seq_is_set s /\ (x `mem` s))
                 (ensures fun r -> seq_is_set r 
                              /\ not (x `mem` r)
                              /\ (r `is_subset_of` s)
                              /\ (forall (p:t). (p `mem` r) == ((p `mem` s) && (p <> x)))
                              /\ (length r == length s - 1))
                 (decreases length s)

val subtract_subset : (#t: eqtype) -> (a: seq t) -> (b: seq t) 
  -> Pure (seq t) (requires seq_is_set a 
                         /\ seq_is_set b 
                         /\ (b `is_subset_of` a))
                 (ensures fun diff -> seq_is_set diff
                          /\ (diff `is_subset_of` a)
                          /\ (length diff == length a - length b)
                          /\ (forall (x:t). (x `mem` diff) 
                                   == ((x `mem` a) && not (x `mem` b))))
                 (decreases length b)
 
(* we publish the implementation details as they might be used in outside proofs *) 
let rec total_length (#t: eqtype) (s: seq (seq t)) : Tot nat (decreases length s)
  = if length s = 0 then 0
    else length (head s) + total_length (tail s)
    
(* true if the collection [parts] is actually a partition of set [s] *)
let is_partition_of (#t: eqtype) (parts: seq (seq t)) (s: seq t)
  : Pure prop (requires parts `are_parts_of` s)
              (ensures fun _ -> True) = (no_intersections_among parts)
                                /\ (forall (x:t). (x `mem` s) ==> (x `is_found_in` parts))

val equal_sets_have_equal_lengths : (#t: eqtype) -> (a: seq t) -> (b: seq t)
  -> Lemma (requires seq_is_set a 
                  /\ seq_is_set b 
                  /\ (a `set_equals` b))
          (ensures length a == length b) 
          
val equal_length_subset_equals_as_set : (#t: eqtype) -> (superset: seq t) -> (subset: seq t)
  -> Lemma (requires seq_is_set superset 
                  /\ seq_is_set subset
                  /\ (subset `is_subset_of` superset)
                  /\ (length superset == length subset))
          (ensures superset `set_equals` subset)

val partition_length_lemma : (#t: eqtype) -> (parts: seq (seq t)) -> (s: seq t)
  -> Lemma (requires (parts `are_parts_of` s)
                  /\ (parts `is_partition_of` s))
          (ensures length s == total_length parts)  
