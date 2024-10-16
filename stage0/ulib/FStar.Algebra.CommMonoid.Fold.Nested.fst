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

(*
   Here we reason about nested folds of functions over arbitrary 
   integer intervals. We call such functions generators.
*)

module FStar.Algebra.CommMonoid.Fold.Nested

module CF = FStar.Algebra.CommMonoid.Fold
module CE = FStar.Algebra.CommMonoid.Equiv

open FStar.IntegerIntervals
open FStar.Matrix 
  
(* Auxiliary utility that casts (matrix c m n) to seq of length (m*n) *)
let matrix_seq #c #m #r (generator: matrix_generator c m r) = 
  seq_of_matrix (Matrix.init generator)

(*
   Most general form of nested fold swap theorem. Here we prove that we can 
   exchange the order of nested foldings over any suitable generator function.
   
   We use the previously proved weaker version (for zero-based indices) in 
   order to prove this, because this way the two proofs together are way shorter.

   I keep the argument types explicit in order to make the proof easier to read.
*)
let double_fold_transpose_lemma #c #eq 
                                (#m0: int) (#mk: not_less_than m0)
                                (#n0: int) (#nk: not_less_than n0)
                                (cm: CE.cm c eq) 
                                (offset_gen: ifrom_ito m0 mk -> ifrom_ito n0 nk -> c)
  : Lemma (double_fold cm offset_gen
           `eq.eq`            
           double_fold cm (transpose_generator offset_gen)) =    
  let m = interval_size (ifrom_ito m0 mk) in
  let n = interval_size (ifrom_ito n0 nk) in 
  let gen : matrix_generator c m n = fun i j -> offset_gen (m0+i) (n0+j) in
  let trans #c #a #b (f: matrix_generator c a b) = transposed_matrix_gen f in
  let trans_ofs #c (#a1 #a2 #b1 #b2:int) (f: ifrom_ito a1 a2 -> ifrom_ito b1 b2 -> c) 
    = transpose_generator f in
  // Here, F* agrees that (n-1) == (nk-n0).
  // But, replace (n-1) with (nk-n0) below, and the proof will fail :)
  let subfold_lhs_base0 (i: under m) = CF.fold cm 0 (n-1) (gen i) in
  let subfold_rhs_base0 (j: under n) = CF.fold cm 0 (m-1) (trans gen j) in
  let subfold_lhs_precise (i: ifrom_ito m0 mk) 
    = CF.fold cm n0 nk (offset_gen i) in  
  let subfold_rhs_precise (j: ifrom_ito n0 nk) 
    = CF.fold cm m0 mk (trans_ofs offset_gen j) in
  let lhs = CF.fold cm m0 mk subfold_lhs_precise in
  let rhs = CF.fold cm n0 nk subfold_rhs_precise in 
  let aux_lhs (i: under m) : Lemma 
    (CF.fold cm n0 nk (offset_gen (m0+i)) == CF.fold cm 0 (n-1) (gen i)) = 
      CF.fold_offset_irrelevance_lemma cm n0 nk (offset_gen (m0+i)) 0 (n-1) (gen i) in
  let aux_rhs (j: under n) : Lemma 
    (CF.fold cm m0 mk (trans_ofs offset_gen (n0+j)) == 
     CF.fold cm 0 (m-1) (trans gen j)) 
    = CF.fold_offset_irrelevance_lemma cm m0 mk (trans_ofs offset_gen (n0+j)) 
                                       0 (m-1) (trans gen j) in
  FStar.Classical.forall_intro aux_lhs;    
  FStar.Classical.forall_intro aux_rhs;    
  FStar.Classical.forall_intro eq.reflexivity;    
  matrix_fold_equals_func_double_fold cm gen; 
  matrix_fold_equals_func_double_fold cm (trans gen);
  let matrix_mn = matrix_seq gen in
  let matrix_nm = matrix_seq (trans gen) in
  CF.fold_offset_elimination_lemma cm m0 mk subfold_lhs_precise subfold_lhs_base0;  
  CF.fold_offset_elimination_lemma cm n0 nk subfold_rhs_precise subfold_rhs_base0;  
  FStar.Classical.forall_intro_2 (FStar.Classical.move_requires_2 eq.symmetry);
  FStar.Classical.forall_intro_3 (FStar.Classical.move_requires_3 eq.transitivity);  
  matrix_fold_equals_fold_of_transpose cm gen;
  matrix_fold_equals_func_double_fold cm gen; 
  matrix_fold_equals_func_double_fold cm (transposed_matrix_gen gen); 
  assert_norm (double_fold cm (transpose_generator offset_gen) == rhs);
  eq.transitivity (FStar.Seq.Permutation.foldm_snoc cm matrix_mn) lhs rhs
 
