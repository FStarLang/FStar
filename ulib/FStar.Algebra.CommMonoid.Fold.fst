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

module FStar.Algebra.CommMonoid.Fold
module CE = FStar.Algebra.CommMonoid.Equiv

open FStar.Seq.Base
open FStar.Seq.Properties 
open FStar.Seq.Permutation

open FStar.IntegerIntervals

(* Here we define the notion for big sums and big products for 
   arbitrary commutative monoids. We construct the folds from 
   an integer range and a function, then calculate the fold --
   a sum or a product, depending on the monoid operation. *)
 
(* We refine multiplication a bit to make proofs smoothier *)

open FStar.Mul  

let rec fold #c #eq 
             (cm: CE.cm c eq) 
             (a: int) (b: not_less_than a) 
             (expr: (ifrom_ito a b) -> c) 
  // some of the lemmas want (ensures (fun (x:c) -> ((nk = n0) ==> (x == expr nk)))) 
  : Tot (c) (decreases b-a) 
  = if b = a then expr b
    else (fold cm a (b-1) expr) `cm.mult` expr b

let rec fold_equality #c #eq (cm: CE.cm c eq) 
  (a: int) (b: not_less_than a) 
  (expr1 expr2: (ifrom_ito a b) -> c)
  : Lemma (requires (forall (i: ifrom_ito a b). expr1 i == expr2 i))
          (ensures fold cm a b expr1 == fold cm a b expr2)
          (decreases b - a) = 
  if b > a then fold_equality cm a (b - 1) expr1 expr2 
  
let fold_singleton_lemma #c #eq cm a expr
  : Lemma (fold #c #eq cm a a expr == expr a) = () 
  
let fold_snoc_decomposition #c #eq (cm: CE.cm c eq) a b expr
  : Lemma (fold cm a b expr == fold cm a (b-1) expr `cm.mult` (expr b)) = ()

 
let rec fold_equals_seq_foldm #c #eq (cm: CE.cm c eq) 
                             (a: int) 
                             (b: not_less_than a) 
                             (expr: (ifrom_ito a b) -> c)
  : Lemma (ensures fold cm a b expr `eq.eq` 
                   foldm_snoc cm (init (closed_interval_size a b) 
                                       (init_func_from_expr expr a b)))
          (decreases b-a) = 
  if (b=a) then  
    let ts = init (closed_interval_size a b) (init_func_from_expr expr a b) in
    lemma_eq_elim (create 1 (expr b)) ts; 
    foldm_snoc_singleton cm (expr b);   
    eq.symmetry (foldm_snoc cm ts) (expr b);
    eq.reflexivity (expr b); 
    eq.transitivity (fold cm a b expr) (expr b) (foldm_snoc cm ts)
  else  
    let lhs = fold cm a b expr in
    let subexpr : ifrom_ito a (b-1) -> c = expr in
    let fullseq = init (b+1-a) (init_func_from_expr expr a b) in    
    let rhs = foldm_snoc cm fullseq in
    let subseq = init (b-a) (init_func_from_expr subexpr a (b-1)) in
    let subsum = fold cm a (b-1) expr in 
    let subfold = foldm_snoc cm subseq in
    let last = expr b in
    let op = cm.mult in
    fold_equals_seq_foldm cm a (b-1) subexpr;    
    cm.commutativity last subfold;
    eq.reflexivity last; 
    cm.congruence subsum last subfold last;
    foldm_snoc_decomposition cm fullseq;
    lemma_eq_elim subseq (fst (un_snoc fullseq));
    eq.symmetry rhs (subfold `op` last);
    eq.transitivity lhs (subfold `op` last) rhs 

(* I keep the argument types explicitly stated here because it makes
   the lemma easier to read. *)
let rec fold_offset_irrelevance_lemma #c #eq (cm: CE.cm c eq) 
  (m0: int) (mk: not_less_than m0) (expr1 : ifrom_ito m0 mk -> c)
  (n0: int) (nk: not_less_than n0) (expr2 : ifrom_ito n0 nk -> c)
  : Lemma (requires (((mk-m0) = (nk-n0)) /\ 
                    (forall (i:under (closed_interval_size m0 mk)). 
                        expr1 (i+m0) == expr2 (i+n0))))
          (ensures fold cm m0 mk expr1 == fold cm n0 nk expr2)
          (decreases (mk-m0)) = 
  if (mk>m0 && nk>n0) then (
      fold_offset_irrelevance_lemma cm m0 (mk-1) expr1 n0 (nk-1) expr2;
      assert (expr1 ((mk-m0)+m0) == expr2 ((nk-n0)+n0))
  ) else if (mk=m0) then (
    eq.reflexivity (expr1 m0);
    assert (expr1 (0+m0) == expr2 (0+n0));
    assert (expr1 m0 == expr2 n0)
  )

let fold_offset_elimination_lemma #c #eq (cm: CE.cm c eq) 
                             (m0: int) (mk: not_less_than m0) 
                             (expr1 : ifrom_ito m0 mk -> c)
                             (expr2 : under (closed_interval_size m0 mk) -> c)
  : Lemma (requires ((forall (i:under (closed_interval_size m0 mk)). 
                         expr2 i == expr1 (i+m0))))
          (ensures fold cm m0 mk expr1 == fold cm 0 (mk-m0) expr2)
          (decreases (mk-m0)) 
  = fold_offset_irrelevance_lemma cm m0 mk expr1 0 (mk-m0) expr2
