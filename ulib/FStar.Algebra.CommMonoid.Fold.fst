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

   Author: A. Rozanov
*)

module FStar.Algebra.CommMonoid.Fold

open FStar.Seq.Base
open FStar.Seq.Properties
open FStar.Seq.Permutation

(* Here we define the notion for big sums and big products for 
   arbitrary commutative monoids. We construct the folds from 
   an integer range and a function, then calculate the fold --
   a sum or a product, depending on the monoid operation. *)
 
(* We refine multiplication a bit to make proofs smoothier *)
let ( *) (x y: int) : (t:int{(x>0 /\ y>0) ==> t>0}) = op_Multiply x y
 
type under (k: pos) = x:nat{x<k}
type not_less_than (x: int) = (t: int{t>=x})
type inbetween (x: int) (y: not_less_than x) = (t: int{t>=x && t<=y})
type counter_of_range (x: int) (y: not_less_than x) = (t: nat{t<(y+1-x)})

let range_count (x: int) (y: not_less_than x) : pos = (y+1)-x
 
(* This lemma, especially when used with forall_intro, helps the 
   prover verify the index ranges of sequences that correspond 
   to arbitrary big_sums *)
let bounds_lemma (n0:int) (nk: not_less_than n0) (i: counter_of_range n0 nk) 
  : Lemma (n0+i >= n0 /\ n0+i <= nk) = ()
  
let init_func_from_expr #c (#n0: int) (#nk: not_less_than n0) 
                        (expr: (inbetween n0 nk) -> c) 
                        (a: inbetween n0 nk) 
                        (b: inbetween a nk) 
  : ((counter_of_range a b) -> c)
  = fun (i: counter_of_range a b) -> expr (n0+i)
  
type comm_monoid c eq = Algebra.CommMonoid.Equiv.cm c eq 

(* 
   Fold (Big Σ or Big Π notation in mathematics) of an arbitrary 
   function expr defined over a finite range of integers.

   Notice how one should very strictly control the domains of 
   lambdas, otherwise the proofs easily fail. 
*)
let rec fold #c #eq 
             (cm: comm_monoid c eq) 
             (n0: int) 
             (nk: not_less_than n0) 
             (expr: (inbetween n0 nk) -> c) 
  : Pure c (requires True)  
           (ensures (fun (x:c) -> ((nk = n0) ==> (x == expr nk)))) 
           (decreases nk-n0) = 
  if nk = n0 then expr nk
  else (fold cm n0 (nk-1) expr) `cm.mult` expr nk

(* This lemma establishes the definitional equality of the fold 
   given said equality for all the values from the allowed range *)
let rec fold_equality #c #eq (cm: comm_monoid c eq) 
  (n0: int) (nk: int{nk>=n0}) (expr1 expr2: (inbetween n0 nk)->c)
  : Lemma (requires (forall (i: inbetween n0 nk). expr1 i == expr2 i))
          (ensures fold cm n0 nk expr1 == fold cm n0 nk expr2)
          (decreases nk-n0) = 
  if nk>n0 then fold_equality cm n0 (nk-1) expr1 expr2 
  
(* This lemma decomposes the big_sum into the sum of the first 
   (k-1) elements plus the remaining last one.
   Obviously requires the argument range that is at least 
   2 elements long. *)
let fold_snoc_decomposition #c #eq 
  (cm: comm_monoid c eq) 
  (n0: int) 
  (nk: int{nk > n0}) 
  (expr: (inbetween n0 nk) -> c) 
  : Lemma (fold cm n0 nk expr == 
           fold cm n0 (nk-1) expr `cm.mult` (expr nk)) = ()

(* This lemma establishes the equality of fold over int range to its
   seq-based foldm_snoc counterpart. *)
let rec fold_equals_seq_foldm #c #eq  
                             (cm: comm_monoid c eq) 
                             (n0: int) 
                             (nk: not_less_than n0) 
                             (expr: (inbetween n0 nk) -> c)
  : Lemma (ensures fold cm n0 nk expr `eq.eq` 
                   foldm_snoc cm (init (range_count n0 nk) 
                                       (init_func_from_expr expr n0 nk)))
          (decreases nk-n0) = 
  if (nk=n0) then (
   let ts = init (range_count n0 nk) (init_func_from_expr expr n0 nk) in
   lemma_eq_elim (create 1 (expr nk)) ts; 
   Seq.Permutation.foldm_snoc_singleton cm (expr nk);   
   eq.symmetry (foldm_snoc cm ts) (expr nk);
   eq.reflexivity (expr nk); 
   eq.transitivity (fold cm n0 nk expr) (expr nk) (foldm_snoc cm ts)
  )
  else (
    let lhs = fold cm n0 nk expr in
    let fullseq = init (range_count n0 nk) (init_func_from_expr expr n0 nk) in    
    let rhs = foldm_snoc cm fullseq in
    let subseq = init (range_count n0 (nk-1)) (init_func_from_expr expr n0 (nk-1)) in
    let subsum = fold cm n0 (nk-1) expr in 
    let subfold = foldm_snoc cm subseq in
    let last = expr nk in
    let op = cm.mult in
    fold_equals_seq_foldm cm n0 (nk-1) expr;    
    lemma_eq_elim (fst (un_snoc fullseq)) subseq;
    cm.commutativity last subfold;
    eq.reflexivity last; 
    cm.congruence subsum last subfold last;
    eq.symmetry rhs (subfold `op` last);
    eq.transitivity lhs (subfold `op` last) rhs
  )
