(*
   Copyright 2022 Microsoft Research

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


(* Sequence equivalence relation (see FStar.Algebra.CommMonoid.Equiv)
*)

module FStar.Seq.Equiv
module CE = FStar.Algebra.CommMonoid.Equiv
open FStar.Seq.Base
open FStar.Seq.Properties
open FStar.IntegerIntervals

val eq_of_seq (#c:_) (eq:CE.equiv c) (s1 s2: seq c) : prop

val eq_of_seq_element_equality (#c:_) (eq: CE.equiv c) (s1 s2: seq c)
  : Lemma (requires eq_of_seq eq s1 s2) 
          (ensures length s1 = length s2 /\ 
                   (forall (i: under (length s1)). (index s1 i `eq.eq` index s2 i))) 

val eq_of_seq_from_element_equality (#c:_) (eq: CE.equiv c) (s1 s2: seq c)
  : Lemma (requires (length s1 = length s2) /\ 
                    (forall (i: under (length s1)). (index s1 i `eq.eq` index s2 i)))
          (ensures eq_of_seq eq s1 s2)
         
val eq_of_seq_condition (#c:_) (eq: CE.equiv c) (s1 s2: seq c)
  : Lemma ((length s1 = length s2) /\ 
           (forall (i: under (length s1)). (index s1 i `eq.eq` index s2 i)) <==>
            eq_of_seq eq s1 s2)

val eq_of_seq_reflexivity (#c:_) (eq: CE.equiv c) (s: seq c)
  : Lemma (ensures eq_of_seq eq s s)

val eq_of_seq_symmetry (#c:_) (eq: CE.equiv c) (s1 s2: seq c)
  : Lemma (requires eq_of_seq eq s1 s2) 
          (ensures eq_of_seq eq s2 s1)

val eq_of_seq_transitivity (#c:_) (eq: CE.equiv c) (s1 s2 s3: seq c)
  : Lemma (requires eq_of_seq eq s1 s2 /\ eq_of_seq eq s2 s3) 
          (ensures eq_of_seq eq s1 s3) 
   
val seq_equiv (#c:_) (eq:CE.equiv c) : (CE.equiv (seq c)) 
 
val eq_of_seq_unsnoc (#c:_) (eq:CE.equiv c) (m:pos) (s1 s2: (z:seq c{length z==m}))
  : Lemma (requires eq_of_seq eq s1 s2)
          (ensures eq.eq (snd (un_snoc s1)) (snd (un_snoc s2)) /\
                   eq_of_seq eq (fst (un_snoc s1)) (fst (un_snoc s2)))
