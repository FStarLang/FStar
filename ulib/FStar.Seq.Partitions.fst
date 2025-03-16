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
*)

(* As always, we are proud to require least possible resources *)
#set-options "--z3rlimit 1 --ifuel 0 --fuel 1"

(* auxiliary lemmas *)
let count_head_lemma (#t:eqtype) (s: seq t{length s > 0}) (x:t)
  : Lemma (requires head s = x) (ensures count x (tail s) == count x s - 1) = ()
  
let count_non_head_lemma (#t:eqtype) (s: seq t{length s > 0}) (x:t)
  : Lemma (requires head s <> x) (ensures count x (tail s) == count x s) = ()

(* element removal with all relevant properties assured *)
let rec remove_element #t s x =  
  if head s = x then tail s
  else begin 
    let tl = (remove_element (tail s) x) in
    let r = cons (head s) tl in
    lemma_eq_elim (tail r) tl; 
    let aux_set_property (p:t) : Lemma (count p r <= 1) = 
      if p = head s then count_head_lemma r p 
      else count_non_head_lemma r p
    in Classical.forall_intro aux_set_property;
    r
  end                             

(* subset subtraction with all relevant properties assured 
   This one occasionally fails without splitting queries,
   and gets accepted fast with the option set, so I see no
   reason why not to... *)
#push-options "--split_queries"
let rec subtract_subset #t a b =
  if length b = 0 then a 
  else subtract_subset (remove_element a (head b)) (tail b) 
#pop-options

(* auxiliary to establish provable equality of sequences of length zero *)
let empty_lemma (#t:eqtype) (s: seq t) 
  : Lemma (requires seq_is_set s /\ (s `set_equals` empty))
          (ensures s == empty) = 
    if length s > 0 then assert ((head s) `mem` s)
    else lemma_eq_elim s empty

let rec equal_sets_have_equal_lengths #t a b
  : Lemma (requires seq_is_set a 
                  /\ seq_is_set b 
                  /\ (a `set_equals` b))
          (ensures length a == length b)
          (decreases length a) = 
  if length a = 0 then empty_lemma b
  else equal_sets_have_equal_lengths (remove_element a (head a)) (remove_element b (head a)) 

let rec equal_length_subset_equals_as_set #t superset subset 
  : Lemma (requires seq_is_set superset
                  /\ seq_is_set subset 
                  /\ (subset `is_subset_of` superset)
                  /\ (length superset == length subset))
          (ensures superset `set_equals` subset)
          (decreases length subset) = 
  if (length superset > 0) 
  then equal_length_subset_equals_as_set (remove_element superset (head subset))
                                         (remove_element subset (head subset))


(* Couldn't rewrite this in terms of dependent tuples *)
type partition (t: eqtype) = 
  | Partition : (s: seq t) -> 
                (parts: seq (seq t) { seq_is_set s 
                                    /\ (parts `are_parts_of` s) 
                                    /\ is_partition_of parts s }) -> 
                partition t

(* The following code extracts a subpartition of [s `subtract_subset` head pt.parts],
   ensuring total length to be decreased precisely by (length (head pt.parts)),
   thus making the final step to the proof of partition length sum breakdown.
   
   We don't really need to publish this -- or at least I don't see the reason to. *)

(* True if [sub_parts] is a partition of [sub], 
   and [sub] is a subset of [s], 
   given [parts] is a partition of [s]  *)
let is_subpartition (#t: eqtype) (s: seq t) (parts: seq (seq t)) 
                                    (sub: seq t) (sub_parts: seq (seq t))
  : Pure prop (requires seq_is_set s 
                      /\ seq_is_set sub
                      /\ (parts `are_parts_of` s)
                      /\ (sub_parts `are_parts_of` sub)
                      /\ (s `is_subset_of` s))
              (ensures fun _ -> True) = sub_parts `is_partition_of` sub


(* this one wants ifuel, and gets accepted really quickly with it *)
#push-options "--ifuel 1"
let partition_split (#t: eqtype) (pt: partition t)
  : Pure (partition t) (requires length pt.parts > 0)
                       (ensures fun p -> is_subpartition pt.s pt.parts p.s p.parts
                                    /\ (length p.parts == length pt.parts - 1)
                                    /\ (length p.s == length pt.s - length (head pt.parts))) =   
  let ps = pt.s `subtract_subset` head pt.parts in
  let pp = tail pt.parts in   
  let ps_is_subset_of_pp_ith (i: under (length pp)) (x:t)
    : Lemma ((x `mem` index pp i) ==> (x `mem` ps)) = 
      if x `mem` index pp i then assert (x `mem` pt.s)
    in Classical.forall_intro_2 ps_is_subset_of_pp_ith; 
  assert (is_subpartition pt.s pt.parts ps pp); 
  assert (length ps == length pt.s - length (head pt.parts));
  Partition ps pp
#pop-options

(* Final result, any partition will have total length 
   of [parts] equal to the length of base set [s] 
   
   This one wants a bit more resources to verify, somehow *)
#push-options "--z3rlimit 2"
let rec partition_length_lemma #t parts s
  : Lemma (requires (parts `are_parts_of` s)
                  /\ (parts `is_partition_of` s))
          (ensures length s == total_length parts) 
          (decreases length parts) = 
  if length parts > 0 then
    let p = partition_split (Partition s parts) in
    partition_length_lemma p.parts p.s;
    assert (total_length parts == length (head parts) + total_length (tail parts));
    assert (length p.s == length s - length (head parts))
#pop-options
  
