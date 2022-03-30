module FStar.Seq.Equiv
module CE = FStar.Algebra.CommMonoid.Equiv

open FStar.Seq.Base
open FStar.Seq.Properties
open FStar.IntegerIntervals

let rec eq_of_seq #c (eq:CE.equiv c) (s1 s2: seq c) 
  : Tot prop (decreases length s1) = 
  (length s1 = length s2 /\
   (length s1 = 0 \/ (
    let s1s, s1l = un_snoc s1 in
     let s2s, s2l = un_snoc s2 in
      eq.eq s1l s2l /\ eq_of_seq eq s1s s2s)))

let rec eq_of_seq_element_equality #c (eq: CE.equiv c) (s1 s2: seq c)
  : Lemma (requires eq_of_seq eq s1 s2) 
          (ensures length s1 = length s2 /\ (forall (i: under (length s1)). (index s1 i `eq.eq` index s2 i))) 
          (decreases length s1)
  = 
  if (length s1 > 0) then 
  let s1liat, s1last = un_snoc s1 in
  let s2liat, s2last = un_snoc s2 in
  eq_of_seq_element_equality eq s1liat s2liat

let rec eq_of_seq_from_element_equality #c (eq: CE.equiv c) (s1 s2: seq c)
  : Lemma (requires (length s1 = length s2) /\ (forall (i: under (length s1)). (index s1 i `eq.eq` index s2 i)))
          (ensures eq_of_seq eq s1 s2)
          (decreases length s1) = 
  if length s1 = 0 then () else 
  let s1liat, s1last = un_snoc s1 in
  let s2liat, s2last = un_snoc s2 in  
  eq_of_seq_from_element_equality eq s1liat s2liat

let eq_of_seq_condition #c (eq: CE.equiv c) (s1 s2: seq c)
  : Lemma ((length s1==length s2) /\ (forall (i: under (length s1)). (index s1 i `eq.eq` index s2 i)) <==>
            eq_of_seq eq s1 s2) = 
  Classical.move_requires_2 (eq_of_seq_element_equality eq) s1 s2;
  Classical.move_requires_2 (eq_of_seq_from_element_equality eq) s1 s2

let rec eq_of_seq_reflexivity #c (eq: CE.equiv c) (s: seq c)
  : Lemma (ensures eq_of_seq eq s s) (decreases length s) = 
  if length s > 0 then 
  let liat, last = un_snoc s in
  eq_of_seq_reflexivity eq liat;
  eq.reflexivity last

let rec eq_of_seq_symmetry #c (eq: CE.equiv c) (s1 s2: seq c)
  : Lemma (requires eq_of_seq eq s1 s2) (ensures eq_of_seq eq s2 s1) (decreases length s1) =  
  if length s1 > 0 then 
  let lia1, las1 = un_snoc s1 in
  let lia2, las2 = un_snoc s2 in
  eq_of_seq_symmetry eq lia1 lia2;
  eq.symmetry las1 las2

let rec eq_of_seq_transitivity #c (eq: CE.equiv c) (s1 s2 s3: seq c)
  : Lemma (requires eq_of_seq eq s1 s2 /\ eq_of_seq eq s2 s3) (ensures eq_of_seq eq s1 s3) (decreases length s1) =  
  if length s1 > 0 then 
  let lia1, las1 = un_snoc s1 in
  let lia2, las2 = un_snoc s2 in
  let lia3, las3 = un_snoc s3 in
  eq_of_seq_transitivity eq lia1 lia2 lia3;
  eq.transitivity las1 las2 las3

let seq_equiv #c (eq:CE.equiv c) : (CE.equiv (seq c)) = 
  CE.EQ (eq_of_seq eq) (eq_of_seq_reflexivity eq)
                       (eq_of_seq_symmetry eq)
                       (eq_of_seq_transitivity eq)
 
let eq_of_seq_unsnoc #c (eq:CE.equiv c) (m:pos) (s1 s2: (z:seq c{length z==m}))
  : Lemma (requires eq_of_seq eq s1 s2)
          (ensures eq.eq (snd (un_snoc s1)) (snd (un_snoc s2)) /\
                   eq_of_seq eq (fst (un_snoc s1)) (fst (un_snoc s2))) =
  eq_of_seq_element_equality eq s1 s2;
  eq_of_seq_from_element_equality eq (fst (un_snoc s1)) (fst (un_snoc s2))
