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

(*
   In this module we provide basic definitions to work with matrices via
   seqs, and define transpose transform together with theorems that assert
   matrix fold equality of original and transposed matrices.
*)


module FStar.Matrix

module CE = FStar.Algebra.CommMonoid.Equiv
module CF = FStar.Algebra.CommMonoid.Fold
module SP = FStar.Seq.Permutation
module SB = FStar.Seq.Base
module ML = FStar.Math.Lemmas

open FStar.IntegerIntervals   
open FStar.Mul

(* This is similar to lambdas passed to FStar.Seq.Base.init *)
type matrix_generator c (m n: pos) = under m -> under n -> c

(* We hide the implementation details of a matrix. *)
val matrix (c:Type u#a) (m n : pos) : Type u#a

(* This lemma asserts the flattened index to be valid 
   for the flattened matrix seq *)
let flattened_index_is_under_flattened_size (m n: pos) (i: under m) (j: under n) 
  : Lemma ((((i*n)+j)) < m*n) = assert (i*n <= (m-1)*n)

(* Returns the flattened index from 2D indices pair 
   and the two array dimensions. *) 
let get_ij (m n: pos) (i:under m) (j: under n) : under (m*n) 
  = flattened_index_is_under_flattened_size m n i j; i*n + j 

(* The following two functions return the matrix indices from the 
   flattened index and the two dimensions *)
let get_i (m n: pos) (ij: under (m*n)) : under m = ij / n
let get_j (m n: pos) (ij: under (m*n)) : under n = ij % n

(* A proof that getting a 2D index back from the flattened 
   index works correctly *)
let consistency_of_i_j (m n: pos) (i: under m) (j: under n) 
  : Lemma (get_i m n (get_ij m n i j) = i /\ get_j m n (get_ij m n i j) = j) = 
  flattened_index_is_under_flattened_size m n i j; //speeds up the proof
  ML.lemma_mod_plus j i n;
  ML.lemma_div_plus j i n 
  
(* A proof that getting the flattened index from 2D 
   indices works correctly *)
let consistency_of_ij (m n: pos) (ij: under (m*n)) 
  : Lemma (get_ij m n (get_i m n ij) (get_j m n ij) == ij) = ()

(* The transposition transform for the flattened index *)
let transpose_ji (m n: pos) (ij: under (m*n)) : under (n*m) =  
  flattened_index_is_under_flattened_size n m (get_j m n ij) (get_i m n ij);
  (get_j m n ij)*m + (get_i m n ij)

(* Auxiliary arithmetic lemma *)
let indices_transpose_lemma (m: pos) (i: under m) (j: nat) 
  : Lemma (((j*m+i)%m=i) && ((j*m+i)/m=j)) = ML.lemma_mod_plus i j m
 
(* A proof of trasnspotition transform bijectivity *)
let ji_is_transpose_of_ij (m n: pos) (ij: under (m*n)) 
  : Lemma (transpose_ji n m (transpose_ji m n ij) = ij) = 
  indices_transpose_lemma m (get_i m n ij) (get_j m n ij)
   
(* A proof that 2D indices are swapped with the transpotition transform *)
let dual_indices (m n: pos) (ij: under (m*n)) : Lemma (
     (get_j n m (transpose_ji m n ij) = get_i m n ij) /\
     (get_i n m (transpose_ji m n ij) = get_j m n ij)) 
  = consistency_of_ij m n ij;
    indices_transpose_lemma m (get_i m n ij) (get_j m n ij)  

(* A matrix can always be treated as a flattened seq *)
val seq_of_matrix : (#c: Type) -> (#m:pos) -> (#n:pos) -> (mx: matrix c m n) -> 
  (s:SB.seq c {
    SB.length s=m*n /\
    (forall (ij: under (m*n)). SB.index s ij == SB.index s (get_ij m n (get_i m n ij) (get_j m n ij)))
  })

(* Indexer for a matrix *)
val ijth : (#c:Type) -> (#m:pos) -> (#n:pos) -> (mx: matrix c m n) -> (i: under m) -> (j: under n) ->
  (t:c{t == SB.index (seq_of_matrix mx) (get_ij m n i j)})

(* Indexer for a matrix returns the correct value *)
val ijth_lemma : (#c:Type) -> (#m:pos) -> (#n:pos) -> (mx: matrix c m n) -> (i: under m) -> (j: under n) ->
  Lemma (ijth mx i j == SB.index (seq_of_matrix mx) (get_ij m n i j))

(* A matrix can always be constructed from an m*n-sized seq *)
val matrix_of_seq : (#c: Type) -> (m:pos) -> (n:pos) -> (s: SB.seq c{SB.length s = m*n}) -> matrix c m n

(* A type for matrices constructed via concrete generator *)
type matrix_of #c (#m #n: pos) (gen: matrix_generator c m n) = z:matrix c m n {
  (forall (i: under m) (j: under n). ijth z i j == gen i j) /\ 
  (forall (ij: under (m*n)). (SB.index (seq_of_matrix z) ij) == (gen (get_i m n ij) (get_j m n ij)))  
}

(* Monoid-based fold of a matrix  treated as a flat seq *)
val foldm : (#c:Type) -> (#eq:CE.equiv c) -> (#m:pos) -> (#n:pos) -> (cm: CE.cm c eq) -> (mx:matrix c m n) -> c

(* foldm_snoc of the corresponding seq is equal to foldm of the matrix *)
val matrix_fold_equals_fold_of_seq : 
  (#c:Type) -> (#eq:CE.equiv c) -> (#m:pos) -> (#n:pos) -> (cm: CE.cm c eq) -> (mx:matrix c m n) 
  -> Lemma (ensures foldm cm mx `eq.eq` SP.foldm_snoc cm (seq_of_matrix mx)) [SMTPat(foldm cm mx)]

(* A matrix constructed from given generator *)
val init : (#c:Type) -> (#m:pos) -> (#n: pos) -> (generator: matrix_generator c m n) 
  -> matrix_of generator 

(* A matrix fold is equal to double foldm_snoc over init-generated seq of seqs *)
val matrix_fold_equals_fold_of_seq_folds : (#c:Type) -> (#eq: CE.equiv c) -> 
                                           (#m: pos) -> (#n: pos) ->
                                           (cm: CE.cm c eq) ->
                                           (generator: matrix_generator c m n) ->
  Lemma (ensures foldm cm (init generator) `eq.eq`
         SP.foldm_snoc cm (SB.init m (fun i -> SP.foldm_snoc cm (SB.init n (generator i))))
         /\ SP.foldm_snoc cm (seq_of_matrix (init generator)) `eq.eq`
         SP.foldm_snoc cm (SB.init m (fun i -> SP.foldm_snoc cm (SB.init n (generator i))))         
         ) 

(* This auxiliary lemma shows that the fold of the last line of a matrix
   is equal to the corresponding fold of the generator function *)
 
(* This lemma establishes that the fold of a matrix is equal to
   nested Algebra.CommMonoid.Fold.fold over the matrix generator *)
val matrix_fold_equals_func_double_fold  : (#c:Type) -> (#eq: CE.equiv c) -> 
                                           (#m: pos) -> (#n: pos) ->
                                           (cm: CE.cm c eq) ->
                                           (generator: matrix_generator c m n) ->
  Lemma (foldm cm (init generator) `eq.eq` 
           CF.fold cm 0 (m-1) (fun (i:under m) -> CF.fold cm 0 (n-1) (generator i)))
 

(* This function provides the transposed matrix generator, with indices swapped
   Notice how the forall property of the result function is happily proved 
   automatically by z3 :) *)
let transposed_matrix_gen #c (#m:pos) (#n:pos) (generator: matrix_generator c m n) 
  : (f: matrix_generator c n m { forall i j. f j i == generator i j }) 
  = fun j i -> generator i j

(* This lemma shows that the transposed matrix is 
   a permutation of the original one *)
let matrix_transpose_is_permutation #c (#m #n: pos) 
                             (generator: matrix_generator c m n)
  : Lemma (SP.is_permutation (seq_of_matrix (init generator))
                          (seq_of_matrix (init (transposed_matrix_gen generator)))
                          (transpose_ji m n)) = 
  let matrix_transposed_eq_lemma #c (#m #n: pos) 
                                        (gen: matrix_generator c m n) 
                                        (ij: under (m*n)) 
    : Lemma (SB.index (seq_of_matrix (init gen)) ij ==
             SB.index (seq_of_matrix (init (transposed_matrix_gen gen))) (transpose_ji m n ij)) 
    = 
      ijth_lemma (init gen) (get_i m n ij) (get_j m n ij);
      ijth_lemma (init (transposed_matrix_gen gen)) 
                 (get_i n m (transpose_ji m n ij)) 
                 (get_j n m (transpose_ji m n ij));
    () in 
  let transpose_inequality_lemma (m n: pos) (ij: under (m*n)) (kl: under (n*m)) 
    : Lemma (requires kl <> ij) (ensures transpose_ji m n ij <> transpose_ji m n kl) = 
      dual_indices m n ij;
      dual_indices m n kl in
  Classical.forall_intro (matrix_transposed_eq_lemma generator); 
  Classical.forall_intro_2 (Classical.move_requires_2 
                           (transpose_inequality_lemma m n));
  SP.reveal_is_permutation (seq_of_matrix (init generator))
                           (seq_of_matrix (init (transposed_matrix_gen generator)))
                           (transpose_ji m n) 

(* Fold over matrix equals fold over transposed matrix *)
let matrix_fold_equals_fold_of_transpose #c #eq 
                                         (#m #n: pos) 
                                         (cm: CE.cm c eq) 
                                         (gen: matrix_generator c m n)
  : Lemma (foldm cm (init gen) `eq.eq`
           foldm cm (init (transposed_matrix_gen gen))) = 
  let matrix_seq #c #m #n (g: matrix_generator c m n) = (seq_of_matrix (init g)) in
  let matrix_mn = matrix_seq gen in
  let matrix_nm = matrix_seq (transposed_matrix_gen gen) in
  matrix_transpose_is_permutation gen;
  SP.foldm_snoc_perm cm (matrix_seq gen)
                     (matrix_seq (transposed_matrix_gen gen))
                     (transpose_ji m n);
  matrix_fold_equals_fold_of_seq cm (init gen);
  matrix_fold_equals_fold_of_seq cm (init (transposed_matrix_gen gen));
  eq.symmetry (foldm cm (init (transposed_matrix_gen gen))) 
              (SP.foldm_snoc cm (matrix_seq (transposed_matrix_gen gen)));
  eq.transitivity (foldm cm (init gen)) (SP.foldm_snoc cm (matrix_seq gen))
                                        (SP.foldm_snoc cm (matrix_seq (transposed_matrix_gen gen)));
  eq.transitivity (foldm cm (init gen)) (SP.foldm_snoc cm (matrix_seq (transposed_matrix_gen gen)))
                  (foldm cm (init (transposed_matrix_gen gen))) 

val matrix_equiv : (#c: Type) ->
                   (eq:  CE.equiv c) ->
                   (m: pos) -> (n: pos) ->
                   CE.equiv (matrix c m n)                   

val matrix_add_comm_monoid : (#c:Type) -> 
                             (#eq:CE.equiv c) -> 
                             (add: CE.cm c eq) -> 
                             (m:pos) -> (n: pos) -> 
                             CE.cm (matrix c m n) (matrix_equiv eq m n)
