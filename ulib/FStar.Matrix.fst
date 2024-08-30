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
   In this module we provide basic definitions to work with matrices via
   seqs, and define transpose transform together with theorems that assert
   matrix fold equality of original and transposed matrices.
*)


module FStar.Matrix

module CE = FStar.Algebra.CommMonoid.Equiv
module CF = FStar.Algebra.CommMonoid.Fold
module SP = FStar.Seq.Permutation
module SB = FStar.Seq.Base
module SProp = FStar.Seq.Properties
module ML = FStar.Math.Lemmas

open FStar.IntegerIntervals   
open FStar.Mul
open FStar.Seq.Equiv

(* 
   A little glossary that might help reading this file
   We don't list common terms like associativity and reflexivity.

   lhs, rhs               left hand side, right hand side
   liat                   subsequence of all elements except the last (tail read backwards)
   snoc                   construction of sequence from a pair (liat, last) (cons read backwards)
   un_snoc                decomposition of sequence into a pair (liat, last)
   foldm                  sum or product of all elements in a sequence using given CommMonoid
   foldm_snoc             recursively defined sum/product of a sequence, starting from the last element
   congruence             respect of equivalence ( = ) by a binary operation ( * ), a=b ==> a*x = b*x
   unit                   identity element (xu=x, ux=x) (not to be confused with invertible elements)
*)

type matrix c m n = z:SB.seq c { SB.length z = m*n }
 
let seq_of_matrix #c #m #n mx = mx

let ijth #c #m #n mx i j = SB.index mx (get_ij m n i j)

let ijth_lemma #c #m #n mx i j 
 : Lemma (ijth mx i j == SB.index (seq_of_matrix mx) (get_ij m n i j)) = ()

let matrix_of_seq #c m n s = s

let foldm #c #eq #m #n cm mx = SP.foldm_snoc cm mx
 
let matrix_fold_equals_fold_of_seq #c #eq #m #n cm mx
  : Lemma (ensures foldm cm mx `eq.eq` SP.foldm_snoc cm (seq_of_matrix mx)) [SMTPat(foldm cm mx)]
  = eq.reflexivity (foldm cm mx)

let matrix_fold_internal #c #eq #m #n (cm:CE.cm c eq) (mx: matrix c m n)
  : Lemma (ensures foldm cm mx == SP.foldm_snoc cm mx) = ()
     
(* A flattened matrix (seq) constructed from generator function
   Notice how the domains of both indices are strictly controlled. *)
let init #c (#m #n: pos) (generator: matrix_generator c m n)
  : matrix_of generator =  
  let mn = m * n in
  let generator_ij ij = generator (get_i m n ij) (get_j m n ij) in
  let flat_indices = indices_seq mn in  
  let result = SProp.map_seq generator_ij flat_indices in
  SProp.map_seq_len generator_ij flat_indices;
  assert (SB.length result == SB.length flat_indices);
  let aux (i: under m) (j: under n) 
    : Lemma (SB.index (SProp.map_seq generator_ij flat_indices) (get_ij m n i j) == generator i j) 
    = consistency_of_i_j m n i j;
      consistency_of_ij m n (get_ij m n i j);
      assert (generator_ij (get_ij m n i j) == generator i j);
      SProp.map_seq_index generator_ij flat_indices (get_ij m n i j) in
  let aux1 (ij: under mn) 
    : Lemma (SB.index (SProp.map_seq generator_ij flat_indices) ij == generator_ij ij) 
    = SProp.map_seq_index generator_ij flat_indices ij in 
  FStar.Classical.forall_intro aux1;
  FStar.Classical.forall_intro_2 aux;
  result
  
private let matrix_seq #c #m #n (gen: matrix_generator c m n) : (t:SB.seq c{ (SB.length t = (m*n)) /\
  (forall (i: under m) (j: under n). SB.index t (get_ij m n i j) == gen i j) /\ 
  (forall(ij: under (m*n)). SB.index t ij == gen (get_i m n ij) (get_j m n ij))
}) = init gen

(* This auxiliary lemma establishes the decomposition of the seq-matrix 
   into the concatenation of its first (m-1) rows and its last row (thus snoc)  *)
let matrix_append_snoc_lemma #c (#m #n: pos) (generator: matrix_generator c m n)
  : Lemma (matrix_seq generator == (SB.slice (matrix_seq generator) 0 ((m-1)*n))
                                   `SB.append`
                                   (SB.slice (matrix_seq generator) ((m-1)*n) (m*n))) 
  = SB.lemma_eq_elim (matrix_seq generator) 
                  (SB.append (SB.slice (matrix_seq generator) 0 ((m-1)*n))
                          (SB.slice (matrix_seq generator) ((m-1)*n) (m*n)))

let matrix_seq_decomposition_lemma  #c (#m:greater_than 1) (#n: pos) (generator: matrix_generator c m n)
  : Lemma ((matrix_seq generator) == 
          SB.append (matrix_seq #c #(m-1) #n generator)
                    (SB.slice (matrix_seq generator) ((m-1)*n) (m*n)))
  = SB.lemma_eq_elim (matrix_seq generator)
                  ((matrix_seq #c #(m-1) #n generator) `SB.append` 
                  (SB.slice (matrix_seq generator) ((m-1)*n) (m*n))) 

(* This auxiliary lemma establishes the equality of the fold of the entire matrix
   to the op of folds of (the submatrix of the first (m-1) rows) and (the last row). *) 
let matrix_fold_snoc_lemma #c #eq 
                           (#m: not_less_than 2) 
                           (#n: pos) 
                           (cm: CE.cm c eq) 
                           (generator: matrix_generator c m n)
  : Lemma (assert ((m-1)*n < m*n);
            SP.foldm_snoc cm (matrix_seq generator) `eq.eq` 
    cm.mult (SP.foldm_snoc cm (matrix_seq #c #(m-1) #n generator))
            (SP.foldm_snoc cm (SB.slice (matrix_seq #c #m #n generator) ((m-1)*n) (m*n))))
  = SB.lemma_eq_elim (matrix_seq generator)
                  ((matrix_seq #c #(m-1) #n generator) `SB.append` 
                  (SB.slice (matrix_seq generator) ((m-1)*n) (m*n)));    
    SP.foldm_snoc_append cm (matrix_seq #c #(m-1) #n generator) 
                         (SB.slice (matrix_seq generator) ((m-1)*n) (m*n)) 

(* 
   There are many auxiliary lemmas like this that are extracted because
   lemma_eq_elim invocations often impact verification speed more than
   one might expect they would.
*)
let matrix_submatrix_lemma #c (#m: not_less_than 2) (#n: pos)  
                           (generator: matrix_generator c m n)
  : Lemma ((matrix_seq generator) == (matrix_seq (fun (i:under(m-1)) (j:under n) -> generator i j) 
                                     `SB.append` SB.init n (generator (m-1))))
  = SB.lemma_eq_elim (matrix_seq (fun (i:under (m-1)) (j:under n) -> generator i j)) 
                     (matrix_seq #c #(m-1) #n generator);
    SB.lemma_eq_elim (SB.slice (matrix_seq generator) ((m-1)*n) (m*n)) 
                     (SB.init n (generator (m-1)));
    matrix_seq_decomposition_lemma generator

let matrix_seq_of_one_row_matrix #c #m #n (generator : matrix_generator c m n) 
  : Lemma (requires m==1)
          (ensures matrix_seq generator == (SB.init n (generator 0))) = 
  SB.lemma_eq_elim (matrix_seq generator) (SB.init n (generator 0))

let one_row_matrix_fold_aux #c #eq #m #n (cm:CE.cm c eq) (generator : matrix_generator c m n) : Lemma 
  (requires m=1)
  (ensures foldm cm (init generator) `eq.eq`
           SP.foldm_snoc cm (SB.init m (fun i -> SP.foldm_snoc cm (SB.init n (generator i)))) /\ 
           SP.foldm_snoc cm (seq_of_matrix (init generator)) `eq.eq`
           SP.foldm_snoc cm (SB.init m (fun i -> SP.foldm_snoc cm (SB.init n (generator i))))) =
  let lhs_seq = matrix_seq generator in
  let rhs_seq = SB.init m (fun i -> SP.foldm_snoc cm (SB.init n (generator i))) in
  let lhs = SP.foldm_snoc cm (matrix_seq generator) in
  let rhs = SP.foldm_snoc cm rhs_seq in
  SP.foldm_snoc_singleton cm (SP.foldm_snoc cm (SB.init n (generator 0)));
  SB.lemma_eq_elim (SB.create 1 (SP.foldm_snoc cm (SB.init n (generator 0))))
    (SB.init m (fun i -> SP.foldm_snoc cm (SB.init n (generator i))));
  matrix_seq_of_one_row_matrix generator;
  eq.symmetry rhs lhs


let fold_of_subgen_aux #c #eq (#m:pos{m>1}) #n (cm: CE.cm c eq) (gen: matrix_generator c m n) (subgen: matrix_generator c (m-1) n) : Lemma
  (requires subgen == (fun (i: under (m-1)) (j: under n) -> gen i j))
  (ensures forall (i: under (m-1)). SP.foldm_snoc cm (SB.init n (subgen i)) ==
                               SP.foldm_snoc cm (SB.init n (gen i))) =         
  let aux_pat (i: under (m-1)) : Lemma (SP.foldm_snoc cm (SB.init n (subgen i)) 
                                     == SP.foldm_snoc cm (SB.init n (gen i))) = 
  SB.lemma_eq_elim (SB.init n (subgen i)) (SB.init n (gen i)) in
  Classical.forall_intro aux_pat          

let arithm_aux (m: pos{m>1}) (n: pos) : Lemma ((m-1)*n < m*n) = ()

let terminal_case_aux #c #eq (#p:pos{p=1}) #n (cm:CE.cm c eq) (generator: matrix_generator c p n) (m: pos{m<=p}) : Lemma 
  (ensures SP.foldm_snoc cm (SB.slice (seq_of_matrix (init generator)) 0 (m*n)) `eq.eq`
           SP.foldm_snoc cm (SB.init m (fun (i:under m) -> SP.foldm_snoc cm (SB.init n (generator i)))))
  = one_row_matrix_fold_aux cm generator

#push-options "--ifuel 0 --fuel 1 --z3rlimit 10"
let terminal_case_two_aux #c #eq (#p:pos) #n (cm:CE.cm c eq) (generator: matrix_generator c p n) (m: pos{m=1}) : Lemma 
  (ensures SP.foldm_snoc cm (SB.slice (seq_of_matrix (init generator)) 0 (m*n)) `eq.eq`
           SP.foldm_snoc cm (SB.init m (fun (i:under m) -> SP.foldm_snoc cm (SB.init n (generator i)))))
  = 
   SP.foldm_snoc_singleton cm (SP.foldm_snoc cm (SB.init n (generator 0)));
   assert (SP.foldm_snoc cm (SB.init m (fun (i:under m) -> SP.foldm_snoc cm (SB.init n (generator i)))) `eq.eq`
           SP.foldm_snoc cm (SB.init n (generator 0)));
   let line = SB.init n (generator 0) in
   let slice = SB.slice (matrix_seq generator) 0 n in
   let aux (ij: under n) : Lemma (SB.index slice ij == SB.index line ij) = 
     Math.Lemmas.small_div ij n;
     Math.Lemmas.small_mod ij n 
   in Classical.forall_intro aux;
   SB.lemma_eq_elim line slice;        
   eq.symmetry (SP.foldm_snoc cm (SB.init m (fun (i:under m) -> SP.foldm_snoc cm (SB.init n (generator i)))))
               (SP.foldm_snoc cm line) 
#pop-options

let liat_equals_init #c (m:pos) (gen: under m -> c)
  : Lemma (fst (SProp.un_snoc (SB.init m gen)) == SB.init (m-1) gen) = 
  SB.lemma_eq_elim (fst (SProp.un_snoc (SB.init m gen))) (SB.init (m-1) gen)

let math_aux (m n: pos) (j: under n) : Lemma (j+((m-1)*n) < m*n) = ()

let math_aux_2 (m n: pos) (j: under n) : Lemma (get_j m n (j+(m-1)*n) == j) 
  = 
  Math.Lemmas.modulo_addition_lemma j n (m-1);
  Math.Lemmas.small_mod j n 
  
let math_aux_3 (m n: pos) (j: under n) : Lemma (get_i m n (j+(m-1)*n) == (m-1)) 
  = 
  Math.Lemmas.division_addition_lemma j n (m-1);
  Math.Lemmas.small_div j n 

let math_aux_4 (m n: pos) (j: under n) : Lemma ((j+((m-1)*n)) - ((m-1)*n) == j) = ()

let seq_eq_from_member_eq #c (n: pos) (p q: (z:SB.seq c{SB.length z=n}))
                          (proof: (i: under n) -> Lemma (SB.index p i == SB.index q i))
  : Lemma (p == q) = 
  Classical.forall_intro proof;
  SB.lemma_eq_elim p q

let math_wut_lemma (x: pos) : Lemma (requires x>1) (ensures x-1 > 0) = ()

(* This proof used to be very unstable, so I rewrote it with as much precision
   and control over lambdas as possible. 

   I also left intact some trivial auxiliaries and the quake option 
   in order to catch regressions the moment they happen instead of several 
   releases later -- Alex *)
#push-options "--ifuel 0 --fuel 0 --z3rlimit 15"
#restart-solver
let rec matrix_fold_equals_double_fold #c #eq (#p:pos) #n (cm:CE.cm c eq) 
                                       (generator: matrix_generator c p n) (m: pos{m<=p}) 
  : Lemma (ensures SP.foldm_snoc cm (SB.slice (seq_of_matrix (init generator)) 0 (m*n)) `eq.eq`
                   SP.foldm_snoc cm (SB.init m (fun (i: under m) -> SP.foldm_snoc cm (SB.init n (generator i)))))
          (decreases m) =
  if p=1 then terminal_case_aux cm generator m 
  else if m=1 then terminal_case_two_aux cm generator m
  else 
    let lhs_seq = (SB.slice (matrix_seq generator) 0 (m*n)) in
    let rhs_seq_gen = fun (i: under m) -> SP.foldm_snoc cm (SB.init n (generator i)) in
    let rhs_seq_subgen = fun (i: under (m-1)) -> SP.foldm_snoc cm (SB.init n (generator i)) in
    let rhs_seq = SB.init m rhs_seq_gen in
    let lhs = SP.foldm_snoc cm lhs_seq in
    let rhs = SP.foldm_snoc cm rhs_seq in
    let matrix = lhs_seq in 
    let submatrix = SB.slice (matrix_seq generator) 0 ((m-1)*n) in
    let last_row = SB.slice (matrix_seq generator) ((m-1)*n) (m*n) in  
    SB.lemma_len_slice (matrix_seq generator) ((m-1)*n) (m*n);
    assert (SB.length last_row = n);
    SB.lemma_eq_elim matrix (SB.append submatrix last_row); 
    SP.foldm_snoc_append cm submatrix last_row; 
    matrix_fold_equals_double_fold #c #eq #p #n cm generator (m-1);  
    SB.lemma_eq_elim (SB.init (m-1) rhs_seq_gen)
                     (SB.init (m-1) rhs_seq_subgen); 
    let aux (j: under n) : Lemma (SB.index last_row j == generator (m-1) j) =
      SB.lemma_index_app2 submatrix last_row (j+((m-1)*n));
      math_aux_2 m n j;
      math_aux_3 m n j;
      math_aux_4 m n j;
      () in Classical.forall_intro aux; 
    let rhs_liat, rhs_last = SProp.un_snoc rhs_seq in 
    let rhs_last_seq = SB.init n (generator (m-1)) in
    liat_equals_init m rhs_seq_gen;
    SP.foldm_snoc_decomposition cm rhs_seq;    
    let aux_2 (j: under n) : Lemma (SB.index last_row j == SB.index rhs_last_seq j) = () in
    seq_eq_from_member_eq n last_row rhs_last_seq aux_2;
    SB.lemma_eq_elim rhs_liat (SB.init (m-1) rhs_seq_gen);
    cm.commutativity (SP.foldm_snoc cm submatrix) (SP.foldm_snoc cm last_row);
    eq.transitivity lhs (SP.foldm_snoc cm submatrix `cm.mult` SP.foldm_snoc cm last_row)
                        (SP.foldm_snoc cm last_row `cm.mult` SP.foldm_snoc cm submatrix);
    eq.reflexivity (SP.foldm_snoc cm last_row);
    cm.congruence (SP.foldm_snoc cm last_row) (SP.foldm_snoc cm submatrix)
                  (SP.foldm_snoc cm last_row) (SP.foldm_snoc cm (SB.init (m-1) rhs_seq_subgen));
    eq.transitivity lhs (SP.foldm_snoc cm last_row `cm.mult` SP.foldm_snoc cm submatrix) rhs 
#pop-options

let matrix_fold_equals_fold_of_seq_folds #c #eq #m #n cm generator : Lemma 
  (ensures foldm cm (init generator) `eq.eq`
           SP.foldm_snoc cm (SB.init m (fun i -> SP.foldm_snoc cm (SB.init n (generator i)))) /\ 
           SP.foldm_snoc cm (seq_of_matrix (init generator)) `eq.eq`
           SP.foldm_snoc cm (SB.init m (fun i -> SP.foldm_snoc cm (SB.init n (generator i))))) =  
  matrix_fold_equals_double_fold cm generator m;
  assert ((SB.slice (seq_of_matrix (init generator)) 0 (m*n)) == seq_of_matrix (init generator));
  SB.lemma_eq_elim (SB.init m (fun i -> SP.foldm_snoc cm (SB.init n (generator i))))
                   (SB.init m (fun (i: under m) -> SP.foldm_snoc cm (SB.init n (generator i))));
  assert ((SB.init m (fun i -> SP.foldm_snoc cm (SB.init n (generator i)))) ==
          (SB.init m (fun (i: under m) -> SP.foldm_snoc cm (SB.init n (generator i)))));
()

(* This auxiliary lemma shows that the fold of the last line of a matrix
   is equal to the corresponding fold of the generator function *) 
let matrix_last_line_equals_gen_fold #c #eq 
                                        (#m #n: pos)  
                                        (cm: CE.cm c eq) 
                                        (generator: matrix_generator c m n) 
  : Lemma (SP.foldm_snoc cm (SB.slice (matrix_seq generator) ((m-1)*n) (m*n))
           `eq.eq` CF.fold cm 0 (n-1) (generator (m-1))) = 
  let slice = SB.slice #c in
  let foldm_snoc = SP.foldm_snoc #c #eq in
  assert (matrix_seq generator == seq_of_matrix (init generator));
  let init = SB.init #c in
  let lemma_eq_elim = SB.lemma_eq_elim #c in 
  lemma_eq_elim (slice (matrix_seq generator) ((m-1)*n) (m*n)) 
                (init n (generator (m-1))); 
  let g : ifrom_ito 0 (n-1) -> c = generator (m-1) in 
  CF.fold_equals_seq_foldm cm 0 (n-1) g;
  let gen = CF.init_func_from_expr g 0 (n-1) in
  eq.reflexivity (foldm_snoc cm (init (closed_interval_size 0 (n-1)) gen));  
  lemma_eq_elim (slice (matrix_seq generator) ((m-1)*n) (m*n))    
                (init (closed_interval_size 0 (n-1)) gen); 
  eq.symmetry (CF.fold cm 0 (n-1) (generator (m-1)))
              (foldm_snoc cm (init (closed_interval_size 0 (n-1)) gen)); 
  eq.transitivity (foldm_snoc cm (slice (matrix_seq generator) ((m-1)*n) (m*n)))
                  (foldm_snoc cm (init (closed_interval_size 0 (n-1)) gen))
                  (CF.fold cm 0 (n-1) (generator (m-1))) 
 
(* This lemma proves that a matrix fold is the same thing as double-fold of
   its generator function against full indices ranges *)
#push-options "--ifuel 0 --fuel 0"
let rec matrix_fold_aux #c #eq // lemma needed for precise generator domain control
                           (#gen_m #gen_n: pos) // full generator domain
                           (cm: CE.cm c eq) 
                           (m: ifrom_ito 1 gen_m) (n: ifrom_ito 1 gen_n) //subdomain
                           (generator: matrix_generator c gen_m gen_n)
  : Lemma (ensures SP.foldm_snoc cm (matrix_seq #c #m #n generator) `eq.eq` 
                   CF.fold cm 0 (m-1) (fun (i: under m) -> CF.fold cm 0 (n-1) (generator i)))
          (decreases m) = 
  Classical.forall_intro_2 (ijth_lemma (init generator));
  let slice = SB.slice #c in
  let foldm_snoc = SP.foldm_snoc #c #eq in
  let lemma_eq_elim = SB.lemma_eq_elim #c in
  if m = 1 then begin
    matrix_fold_equals_fold_of_seq cm (init generator);
    matrix_last_line_equals_gen_fold #c #eq #m #n cm generator;  
    CF.fold_singleton_lemma cm 0 (fun (i:under m) -> CF.fold cm 0 (n-1) (generator i));
    assert (CF.fold cm 0 (m-1) (fun (i: under m) -> CF.fold cm 0 (n-1) (generator i)) 
            == CF.fold cm 0 (n-1) (generator 0)) 
  end else begin     
    Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity);  
    matrix_fold_aux cm (m-1) n generator;    
    let outer_func (i: under m) = CF.fold cm 0 (n-1) (generator i) in
    let outer_func_on_subdomain (i: under (m-1)) = CF.fold cm 0 (n-1) (generator i) in
    CF.fold_equality cm 0 (m-2) outer_func_on_subdomain outer_func;
    CF.fold_snoc_decomposition cm 0 (m-1) outer_func;  
    matrix_fold_snoc_lemma #c #eq #m #n cm generator;
    matrix_last_line_equals_gen_fold #c #eq #m #n cm generator;
    cm.congruence (foldm_snoc cm (matrix_seq #c #(m-1) #n generator))
                  (foldm_snoc cm (slice (matrix_seq #c #m #n generator) ((m-1)*n) (m*n)))
                  (CF.fold cm 0 (m-2) outer_func)
                  (CF.fold cm 0 (n-1) (generator (m-1))) 
  end  
#pop-options

(* This lemma establishes that the fold of a matrix is equal to
   nested Algebra.CommMonoid.Fold.fold over the matrix generator *)
let matrix_fold_equals_func_double_fold #c #eq #m #n cm generator
  : Lemma (foldm cm (init generator) `eq.eq` 
           CF.fold cm 0 (m-1) (fun (i:under m) -> CF.fold cm 0 (n-1) (generator i))) 
  = matrix_fold_aux cm m n generator

(* This function provides the transposed matrix generator, with indices swapped
   Notice how the forall property of the result function is happily proved 
   automatically by z3 :) *)
let transposed_matrix_gen #c #m #n (generator: matrix_generator c m n) 
  : (f: matrix_generator c n m { forall i j. f j i == generator i j }) 
  = fun j i -> generator i j

(* This lemma shows that the transposed matrix is 
   a permutation of the original one *)
let matrix_transpose_is_permutation #c #m #n generator
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
let matrix_fold_equals_fold_of_transpose #c #eq #m #n
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

let matrix_eq_fun #c (#m #n: pos) (eq: CE.equiv c) (ma mb: matrix c m n) =   
  eq_of_seq eq (seq_of_matrix ma) (seq_of_matrix mb)

(*
   Matrix equivalence, defined as element-wise equivalence of its underlying 
   flattened sequence, is constructed trivially from the element equivalence
   and the lemmas defined above.
*)
let matrix_equiv #c (eq: CE.equiv c) (m n: pos) : CE.equiv (matrix c m n) = 
  CE.EQ (matrix_eq_fun eq)
        (fun m -> eq_of_seq_reflexivity eq (seq_of_matrix m))
        (fun ma mb -> eq_of_seq_symmetry eq (seq_of_matrix ma) (seq_of_matrix mb))
        (fun ma mb mc -> eq_of_seq_transitivity eq (seq_of_matrix ma) (seq_of_matrix mb) (seq_of_matrix mc))

(* Equivalence of matrices means equivalence of all corresponding elements *)
let matrix_equiv_ijth #c (#m #n: pos) (eq: CE.equiv c) (ma mb: matrix c m n) (i: under m) (j: under n)
  : Lemma (requires (matrix_equiv eq m n).eq ma mb) (ensures ijth ma i j `eq.eq` ijth mb i j) = 
  eq_of_seq_element_equality eq (seq_of_matrix ma) (seq_of_matrix mb)

(* Equivalence of all corresponding elements means equivalence of matrices *)
let matrix_equiv_from_element_eq #c (#m #n: pos) (eq: CE.equiv c) (ma mb: matrix c m n)
  : Lemma (requires (forall (i: under m) (j: under n). ijth ma i j `eq.eq` ijth mb i j))
          (ensures matrix_eq_fun eq ma mb) = 
  assert (SB.length (seq_of_matrix ma) = SB.length (seq_of_matrix mb));
  let s1 = seq_of_matrix ma in
  let s2 = seq_of_matrix mb in
  assert (forall (ij: under (m*n)). SB.index s1 ij == ijth ma (get_i m n ij) (get_j m n ij));
  assert (forall (ij: under (m*n)). SB.index s2 ij == ijth mb (get_i m n ij) (get_j m n ij));
  assert (forall (ij: under (m*n)). SB.index s1 ij `eq.eq` SB.index s2 ij);  
  eq_of_seq_from_element_equality eq (seq_of_matrix ma) (seq_of_matrix mb)

(* We construct addition CommMonoid from the following definitions *)
let matrix_add_is_associative #c #eq #m #n (add: CE.cm c eq) (ma mb mc: matrix c m n)
  : Lemma (matrix_add add (matrix_add add ma mb) mc `(matrix_equiv eq m n).eq` 
           matrix_add add ma (matrix_add add mb mc)) =  
  matrix_equiv_from_proof eq 
    (matrix_add add (matrix_add add ma mb) mc)
    (matrix_add add ma (matrix_add add mb mc))  
    (fun i j -> add.associativity (ijth ma i j) (ijth mb i j) (ijth mc i j))

let matrix_add_is_commutative #c #eq (#m #n: pos) (add: CE.cm c eq) (ma mb: matrix c m n)
  : Lemma (matrix_add add ma mb `(matrix_equiv eq m n).eq` matrix_add add mb ma) = 
  matrix_equiv_from_proof eq (matrix_add add ma mb) (matrix_add add mb ma)
    (fun i j -> add.commutativity (ijth ma i j) (ijth mb i j)) 

let matrix_add_congruence #c #eq (#m #n: pos) (add: CE.cm c eq) (ma mb mc md: matrix c m n)
  : Lemma (requires matrix_eq_fun eq ma mc /\ matrix_eq_fun eq mb md)
          (ensures matrix_add add ma mb `matrix_eq_fun eq` matrix_add add mc md) =
  matrix_equiv_from_proof eq (matrix_add add ma mb) (matrix_add add mc md)
                          (fun i j -> matrix_equiv_ijth eq ma mc i j;
                                   matrix_equiv_ijth eq mb md i j; 
                                   add.congruence (ijth ma i j) (ijth mb i j) 
                                                  (ijth mc i j) (ijth md i j)) 
 
let matrix_add_zero #c #eq (add: CE.cm c eq) (m n: pos) 
  : (z: matrix c m n { forall (i: under m) (j: under n). ijth z i j == add.unit }) 
  = matrix_of_seq m n (SB.create (m*n) add.unit)

let matrix_add_identity #c #eq (add: CE.cm c eq) (#m #n: pos) (mx: matrix c m n)
  : Lemma (matrix_add add (matrix_add_zero add m n) mx `matrix_eq_fun eq` mx) =
  matrix_equiv_from_proof eq (matrix_add add (matrix_add_zero add m n) mx) mx
                          (fun i j -> add.identity (ijth mx i j))
  
let matrix_add_comm_monoid #c #eq (add: CE.cm c eq) (m n: pos)
  : CE.cm (matrix c m n) (matrix_equiv eq m n) 
  = CE.CM (matrix_add_zero add m n)
          (matrix_add add)
          (matrix_add_identity add)
          (matrix_add_is_associative add)
          (matrix_add_is_commutative add)
          (matrix_add_congruence add)

(* equivalence of addressing styles *)
let matrix_row_col_lemma #c #m #n (mx: matrix c m n) (i: under m) (j: under n) 
  : Lemma (ijth mx i j == SB.index (row mx i) j /\ ijth mx i j == SB.index (col mx j) i) = ()

(* 
   See how lemma_eq_elim is defined, note the SMTPat there.
   Invoking this is often more efficient in big proofs than invoking 
   lemma_eq_elim directly.
*)
let seq_of_products_lemma #c #eq (mul: CE.cm c eq) (s: SB.seq c) (t: SB.seq c {SB.length t == SB.length s})
  (r: SB.seq c{SB.equal r (SB.init (SB.length s) (fun (i: under (SB.length s)) -> SB.index s i `mul.mult` SB.index t i))})
  : Lemma (seq_of_products mul s t == r) = ()

let dot_lemma #c #eq add mul s t
  : Lemma (dot add mul s t == SP.foldm_snoc add (seq_of_products mul s t)) = ()
  
let matrix_mul_gen #c #eq #m #n #p (add mul: CE.cm c eq) 
                   (mx: matrix c m n) (my: matrix c n p) 
                   (i: under m) (k: under p)
  = dot add mul (row mx i) (col my k)

let matrix_mul #c #eq #m #n #p (add mul: CE.cm c eq) (mx: matrix c m n) (my: matrix c n p) 
  = init (matrix_mul_gen add mul mx my)

(* the following lemmas improve verification performance. *) 
(* Sometimes this fact gets lost and needs an explicit proof *)
let seq_last_index #c (s: SB.seq c{SB.length s > 0}) 
  : Lemma (SProp.last s == SB.index s (SB.length s - 1)) = ()

(* It often takes assert_norm to obtain the fact that,
   (fold s == last s `op` fold (slice s 0 (length s - 1))).
   Invoking this lemma instead offers a more stable option. *)
let seq_fold_decomposition #c #eq (cm: CE.cm c eq) (s: SB.seq c{SB.length s > 0}) 
  : Lemma (SP.foldm_snoc cm s == cm.mult (SProp.last s) (SP.foldm_snoc cm (fst (SProp.un_snoc s)))) = ()


(* Using common notation for algebraic operations instead of `mul` / `add` infix 
   simplifies the code and makes it more compact. *)
let rec foldm_snoc_distributivity_left #c #eq (mul add: CE.cm c eq) (a: c) (s: SB.seq c)
  : Lemma (requires is_fully_distributive mul add /\ is_absorber add.unit mul) 
          (ensures mul.mult a (SP.foldm_snoc add s) `eq.eq`
                   SP.foldm_snoc add (const_op_seq mul a s))
          (decreases SB.length s) = 
  if SB.length s > 0 then 
    let ((+), ( * ), (=)) = add.mult, mul.mult, eq.eq in
    let sum s = SP.foldm_snoc add s in
    let liat, last = SProp.un_snoc s in 
    let rhs_liat, rhs_last = SProp.un_snoc (const_op_seq mul a s) in
    foldm_snoc_distributivity_left mul add a liat; 
    SB.lemma_eq_elim rhs_liat (const_op_seq mul a liat);
    eq.reflexivity rhs_last;
    add.congruence rhs_last (a*sum liat) rhs_last (sum rhs_liat);
    eq.transitivity (a*sum s) (rhs_last + a*sum liat) (rhs_last + sum rhs_liat) 

let rec foldm_snoc_distributivity_right #c #eq (mul add: CE.cm c eq) (s: SB.seq c) (a: c)
  : Lemma (requires is_fully_distributive mul add /\ is_absorber add.unit mul) 
          (ensures mul.mult (SP.foldm_snoc add s) a `eq.eq`
                   SP.foldm_snoc add (seq_op_const mul s a))
          (decreases SB.length s) = 
  if SB.length s > 0 then 
    let ((+), ( * ), (=)) = add.mult, mul.mult, eq.eq in
    let sum s = SP.foldm_snoc add s in
    let liat, last = SProp.un_snoc s in
    let rhs_liat, rhs_last = SProp.un_snoc (seq_op_const mul s a) in
    foldm_snoc_distributivity_right mul add liat a; 
    SB.lemma_eq_elim rhs_liat (seq_op_const mul liat a);
    eq.reflexivity rhs_last;
    add.congruence rhs_last (sum liat*a) rhs_last (sum rhs_liat);
    eq.transitivity (sum s*a) (rhs_last + sum liat*a) (rhs_last + sum rhs_liat) 

let foldm_snoc_distributivity_right_eq #c #eq (mul add: CE.cm c eq) (s: SB.seq c) (a: c) (r: SB.seq c)
  : Lemma (requires is_fully_distributive mul add /\ is_absorber add.unit mul /\
                    SB.equal r (seq_op_const mul s a)) 
          (ensures mul.mult (SP.foldm_snoc add s) a `eq.eq`
                   SP.foldm_snoc add r)
  = foldm_snoc_distributivity_right mul add s a

let foldm_snoc_distributivity_left_eq #c #eq (mul add: CE.cm c eq) (a: c) 
                                             (s: SB.seq c) 
                                             (r: SB.seq c{SB.equal r (const_op_seq mul a s)})
  : Lemma (requires is_fully_distributive mul add /\ is_absorber add.unit mul) 
          (ensures (mul.mult a(SP.foldm_snoc add s)) `eq.eq`
                   SP.foldm_snoc add r)
  = foldm_snoc_distributivity_left mul add a s 
 
let matrix_mul_ijth #c #eq #m #n #k (add mul: CE.cm c eq) 
                    (mx: matrix c m n) (my: matrix c n k) i h
  : Lemma (ijth (matrix_mul add mul mx my) i h == dot add mul (row mx i) (col my h)) = ()

let matrix_mul_ijth_as_sum #c #eq #m #n #p (add mul: CE.cm c eq)  
                    (mx: matrix c m n) (my: matrix c n p) i k
  : Lemma (ijth (matrix_mul add mul mx my) i k == 
           SP.foldm_snoc add (SB.init n (fun (j: under n) -> mul.mult (ijth mx i j) (ijth my j k)))) =
  let r = SB.init n (fun (j: under n) -> mul.mult (ijth mx i j) (ijth my j k)) in
  assert (ijth (matrix_mul add mul mx my) i k == 
          SP.foldm_snoc add (seq_of_products mul (row mx i) (col my k)));
  seq_of_products_lemma mul (row mx i) (col my k) r

let matrix_mul_ijth_eq_sum_of_seq #c #eq #m #n #p (add: CE.cm c eq) 
                                  (mul: CE.cm c eq{is_fully_distributive mul add /\ is_absorber add.unit mul}) 
                                  (mx: matrix c m n) (my: matrix c n p) (i: under m) (k: under p)
                                  (r: SB.seq c{r `SB.equal` seq_of_products mul (row mx i) (col my k)})
  : Lemma (ijth (matrix_mul add mul mx my) i k == SP.foldm_snoc add r) = ()

  
let double_foldm_snoc_transpose_lemma #c #eq (#m #n: pos) (cm: CE.cm c eq) (f: under m -> under n -> c)
  : Lemma (SP.foldm_snoc cm (SB.init m (fun (i: under m) -> SP.foldm_snoc cm (SB.init n (fun (j: under n) -> f i j)))) `eq.eq`
           SP.foldm_snoc cm (SB.init n (fun (j: under n) -> SP.foldm_snoc cm (SB.init m (fun (i: under m) -> f i j))))) = 
  Classical.forall_intro_2 (Classical.move_requires_2 eq.symmetry);
  let gen : matrix_generator c m n = f in  
  let mx = init gen in 
  let mx_seq = matrix_seq gen in
  matrix_fold_equals_fold_of_seq_folds cm gen; 
  let aux (i: under m) : Lemma (SB.init n (gen i) == SB.init n (fun (j: under n) -> f i j))
    = SB.lemma_eq_elim (SB.init n (gen i))(SB.init n (fun (j: under n) -> f i j)) 
    in Classical.forall_intro aux;  
  SB.lemma_eq_elim (SB.init m (fun i -> SP.foldm_snoc cm (SB.init n (gen i))))
                   (SB.init m (fun i -> SP.foldm_snoc cm (SB.init n (fun (j: under n) -> f i j))));      
  SB.lemma_eq_elim (SB.init m (fun (i: under m) -> SP.foldm_snoc cm (SB.init n (fun (j: under n) -> f i j))))
                   (SB.init m (fun i -> SP.foldm_snoc cm (SB.init n (fun (j: under n) -> f i j))));                   
  matrix_transpose_is_permutation gen;
  matrix_fold_equals_fold_of_transpose cm gen;
  let trans_gen = transposed_matrix_gen gen in
  let mx_trans = init trans_gen in
  let mx_trans_seq = matrix_seq trans_gen in
  matrix_fold_equals_fold_of_seq_folds cm trans_gen;
  assert (foldm cm mx_trans `eq.eq` 
          SP.foldm_snoc cm (SB.init n (fun j -> SP.foldm_snoc cm (SB.init m (trans_gen j)))));
  let aux_tr_lemma (j: under n) 
    : Lemma ((SB.init m (trans_gen j)) == (SB.init m (fun (i: under m) -> f i j))) 
    = SB.lemma_eq_elim (SB.init m (trans_gen j)) (SB.init m (fun (i: under m) -> f i j)) 
    in Classical.forall_intro aux_tr_lemma;
  SB.lemma_eq_elim (SB.init n (fun j -> SP.foldm_snoc cm (SB.init m (trans_gen j))))
                   (SB.init n (fun (j:under n) -> SP.foldm_snoc cm (SB.init m (fun (i: under m) -> f i j))));
  assert (foldm cm mx_trans `eq.eq` 
          SP.foldm_snoc cm (SB.init n (fun (j:under n) -> SP.foldm_snoc cm (SB.init m (fun (i: under m) -> f i j)))));
  eq.transitivity (SP.foldm_snoc cm (SB.init m (fun (i: under m) -> SP.foldm_snoc cm (SB.init n (fun (j: under n) -> f i j)))))
                  (foldm cm mx)
                  (foldm cm mx_trans);
  eq.transitivity (SP.foldm_snoc cm (SB.init m (fun (i: under m) -> SP.foldm_snoc cm (SB.init n (fun (j: under n) -> f i j)))))
                  (foldm cm mx_trans)
                  (SP.foldm_snoc cm (SB.init n (fun (j:under n) -> SP.foldm_snoc cm (SB.init m (fun (i: under m) -> f i j)))))

let matrix_mul_ijth_eq_sum_of_seq_for_init #c #eq #m #n #p (add mul: CE.cm c eq)  
  (mx: matrix c m n) (my: matrix c n p) i k
  (f: under n -> c { SB.init n f `SB.equal` seq_of_products mul (row mx i) (col my k)})
  : Lemma (ijth (matrix_mul add mul mx my) i k == SP.foldm_snoc add (SB.init n f)) = ()

let double_foldm_snoc_of_equal_generators #c #eq (#m #n: pos) 
                                          (cm: CE.cm c eq) 
                                          (f g: under m -> under n -> c)
  : Lemma (requires (forall (i: under m) (j: under n). f i j `eq.eq` g i j))
          (ensures SP.foldm_snoc cm (SB.init m (fun (i: under m) -> SP.foldm_snoc cm (SB.init n (fun (j: under n) -> f i j))))
          `eq.eq`  SP.foldm_snoc cm (SB.init m (fun (i: under m) -> SP.foldm_snoc cm (SB.init n (fun (j: under n) -> g i j))))) = 
  let aux i : Lemma (SP.foldm_snoc cm (SB.init n (fun (j: under n) -> f i j)) `eq.eq`
                     SP.foldm_snoc cm (SB.init n (fun (j: under n) -> g i j))) 
    = SP.foldm_snoc_of_equal_inits cm (fun j -> f i j) (fun j -> g i j) in
  Classical.forall_intro aux;
  SP.foldm_snoc_of_equal_inits cm (fun (i: under m) -> SP.foldm_snoc cm (SB.init n (fun (j: under n) -> f i j)))
                                  (fun (i: under m) -> SP.foldm_snoc cm (SB.init n (fun (j: under n) -> g i j)))

#push-options "--z3rlimit 15 --ifuel 0 --fuel 0"  
let matrix_mul_is_associative #c #eq #m #n #p #q (add: CE.cm c eq) 
                    (mul: CE.cm c eq{is_fully_distributive mul add /\ is_absorber add.unit mul}) 
                    (mx: matrix c m n) (my: matrix c n p) (mz: matrix c p q)
  : Lemma (matrix_eq_fun eq ((matrix_mul add mul mx my) `matrix_mul add mul` mz)
                            (matrix_mul add mul mx (matrix_mul add mul my mz))) =  
  let rhs = mx `matrix_mul add mul` (my `matrix_mul add mul` mz) in
  let lhs = (mx `matrix_mul add mul` my) `matrix_mul add mul` mz in
  let mxy = matrix_mul add mul mx my in
  let myz = matrix_mul add mul my mz in
  let ((+), ( * ), (=)) = add.mult, mul.mult, eq.eq in 
  let aux i l : squash (ijth lhs i l = ijth rhs i l) =
    let sum_j (f: under n -> c) = SP.foldm_snoc add (SB.init n f) in
    let sum_k (f: under p -> c) = SP.foldm_snoc add (SB.init p f) in 
    let xy_products_init k j = ijth mx i j * ijth my j k in
    let xy_cell_as_sum k = sum_j (xy_products_init k) in    
    let xy_cell_lemma k : Lemma (ijth mxy i k == xy_cell_as_sum k) = 
        matrix_mul_ijth_eq_sum_of_seq_for_init add mul mx my i k (xy_products_init k)
        in Classical.forall_intro xy_cell_lemma;  
    let xy_z_products_init k = xy_cell_as_sum k * ijth mz k l in
    matrix_mul_ijth_eq_sum_of_seq_for_init add mul mxy mz i l xy_z_products_init;
    let full_init_kj k j = (ijth mx i j * ijth my j k) * ijth mz k l in
    let full_init_jk j k = (ijth mx i j * ijth my j k) * ijth mz k l in 
    let full_init_rh j k = ijth mx i j * (ijth my j k * ijth mz k l) in
    let sum_jk (f: (under n -> under p -> c)) = sum_j (fun j -> sum_k (fun k -> f j k)) in
    let sum_kj (f: (under p -> under n -> c)) = sum_k (fun k -> sum_j (fun j -> f k j)) in
    let xy_z_distr k : Lemma (((xy_cell_as_sum k) * (ijth mz k l)) = sum_j (full_init_kj k))
      = foldm_snoc_distributivity_right_eq mul add (SB.init n (xy_products_init k)) (ijth mz k l) 
                                                   (SB.init n (full_init_kj k)) 
      in Classical.forall_intro xy_z_distr;
    SP.foldm_snoc_of_equal_inits add xy_z_products_init 
                                  (fun k -> sum_j (full_init_kj k));  
    double_foldm_snoc_transpose_lemma add full_init_kj;
    eq.transitivity (ijth lhs i l) (sum_kj full_init_kj)
                                   (sum_jk full_init_jk);
    let aux_rh j k : Lemma (full_init_jk j k = full_init_rh j k)
      = mul.associativity (ijth mx i j) (ijth my j k) (ijth mz k l)
      in Classical.forall_intro_2 aux_rh;
    double_foldm_snoc_of_equal_generators add full_init_jk full_init_rh;
    eq.transitivity (ijth lhs i l) (sum_jk full_init_jk) (sum_jk full_init_rh); 
    
    // now expand the right hand side, fully dual to the first part of the lemma.
    let yz_products_init j k = ijth my j k * ijth mz k l in
    let yz_cell_as_sum j = sum_k (yz_products_init j) in
    let x_yz_products_init j = ijth mx i j * yz_cell_as_sum j in 
    let yz_cell_lemma j : Lemma (ijth myz j l == sum_k (yz_products_init j)) = 
        matrix_mul_ijth_eq_sum_of_seq_for_init add mul my mz j l (yz_products_init j);
      () in Classical.forall_intro yz_cell_lemma; 
    matrix_mul_ijth_eq_sum_of_seq_for_init add mul mx myz i l x_yz_products_init; 
    let x_yz_distr j : Lemma (ijth mx i j * yz_cell_as_sum j = sum_k (full_init_rh j))  
      = foldm_snoc_distributivity_left_eq mul add (ijth mx i j) (SB.init p (yz_products_init j))   
                                                                (SB.init p (full_init_rh j)) 
      in Classical.forall_intro x_yz_distr;
    SP.foldm_snoc_of_equal_inits add x_yz_products_init (fun j -> sum_k (full_init_rh j));  
    eq.symmetry (ijth rhs i l) (sum_jk full_init_rh);
    eq.transitivity (ijth lhs i l) (sum_jk full_init_rh) (ijth rhs i l);   
  () in matrix_equiv_from_proof eq lhs rhs aux
#pop-options

let matrix_mul_unit_row_lemma #c #eq m (add mul: CE.cm c eq) (i: under m)
  : Lemma ((row (matrix_mul_unit add mul m) i 
             == (SB.create i add.unit) `SB.append` 
                ((SB.create 1 mul.unit) `SB.append` (SB.create (m-i-1) add.unit))) /\
           (row (matrix_mul_unit add mul m) i 
             == ((SB.create i add.unit) `SB.append` (SB.create 1 mul.unit)) `SB.append`
                (SB.create (m-i-1) add.unit))) =  
  SB.lemma_eq_elim ((SB.create i add.unit `SB.append` SB.create 1 mul.unit) 
                   `SB.append` (SB.create (m-i-1) add.unit))
                   (row (matrix_mul_unit add mul m) i); 
  SB.lemma_eq_elim ((SB.create i add.unit) `SB.append` 
                   (SB.create 1 mul.unit `SB.append` SB.create (m-i-1) add.unit))
                   (row (matrix_mul_unit add mul m) i)
                   
let matrix_mul_unit_col_lemma #c #eq m (add mul: CE.cm c eq) (i: under m)
  : Lemma ((col (matrix_mul_unit add mul m) i 
             == (SB.create i add.unit) `SB.append` 
                ((SB.create 1 mul.unit) `SB.append` (SB.create (m-i-1) add.unit))) /\
           (col (matrix_mul_unit add mul m) i == 
                ((SB.create i add.unit) `SB.append` (SB.create 1 mul.unit)) `SB.append`
                (SB.create (m-i-1) add.unit))) =  
  SB.lemma_eq_elim ((SB.create i add.unit `SB.append` SB.create 1 mul.unit) 
                   `SB.append` (SB.create (m-i-1) add.unit))
                   (col (matrix_mul_unit add mul m) i); 
  SB.lemma_eq_elim ((SB.create i add.unit) `SB.append` 
                   (SB.create 1 mul.unit `SB.append` SB.create (m-i-1) add.unit))
                   (col (matrix_mul_unit add mul m) i)
 
let seq_of_products_zeroes_lemma #c #eq #m (mul: CE.cm c eq) 
                                 (z: c{is_absorber z mul})
                                 (s: SB.seq c{SB.length s == m})
  : Lemma (ensures (eq_of_seq eq (seq_of_products mul (SB.create m z) s) (SB.create m z))) 
  = eq_of_seq_from_element_equality eq (seq_of_products mul (SB.create m z) s) (SB.create m z) 

let rec foldm_snoc_zero_lemma #c #eq (add: CE.cm c eq) (zeroes: SB.seq c)
  : Lemma (requires (forall (i: under (SB.length zeroes)). SB.index zeroes i `eq.eq` add.unit))
          (ensures eq.eq (SP.foldm_snoc add zeroes) add.unit) 
          (decreases SB.length zeroes) =
  if (SB.length zeroes < 1) then begin
    assert_norm (SP.foldm_snoc add zeroes == add.unit);
    eq.reflexivity add.unit    
  end else
    let liat, last = SProp.un_snoc zeroes in
    foldm_snoc_zero_lemma add liat;
    add.congruence last (SP.foldm_snoc add liat) add.unit add.unit;
    add.identity add.unit;
    SP.foldm_snoc_decomposition add zeroes;
    eq.transitivity (SP.foldm_snoc add zeroes)                                
                    (add.mult add.unit add.unit)
                    add.unit


let matrix_mul_unit_ijth #c #eq (add mul: CE.cm c eq) m (i j: under m)
  : Lemma (ijth (matrix_mul_unit add mul m) i j == (if i=j then mul.unit else add.unit))=() 

let last_equals_index #c (s: SB.seq c{SB.length s > 0}) 
  : Lemma ((snd (SProp.un_snoc s)) == SB.index s (SB.length s - 1)) = ()



let matrix_right_mul_identity_aux_0 #c #eq #m 
                                    (add: CE.cm c eq) 
                                    (mul: CE.cm c eq{is_absorber add.unit mul}) 
                                    (mx: matrix c m m)
                                    (i j: under m) (k:nat{k=0})                     
  : Lemma (ensures SP.foldm_snoc add (SB.init k (fun (k: under m) 
                                                 -> ijth mx i k `mul.mult` 
                                                   ijth (matrix_mul_unit add mul m) k j))
                   `eq.eq` add.unit)
  = eq.reflexivity add.unit 
 
let rec matrix_right_mul_identity_aux_1 #c #eq #m 
                                        (add: CE.cm c eq) 
                                        (mul: CE.cm c eq{is_absorber add.unit mul}) 
                                        (mx: matrix c m m)
                                        (i j: under m) (k:nat{k<=j})                     
  : Lemma (ensures SP.foldm_snoc add (SB.init k (fun (k: under m) 
                                                 -> ijth mx i k `mul.mult` 
                                                   ijth (matrix_mul_unit add mul m) k j))
                   `eq.eq` add.unit)
          (decreases k)
  = if k = 0 then matrix_right_mul_identity_aux_0 add mul mx i j k
    else 
      let unit = matrix_mul_unit add mul m in
      let mxu = matrix_mul add mul mx unit in
      let ( * ) = mul.mult in
      let ( $=$ ) = eq.eq in
      let gen = fun (k: under m) -> ijth mx i k * ijth unit k j in   
      let full = SB.init k gen in
      let liat,last = SProp.un_snoc full in
      matrix_right_mul_identity_aux_1 add mul mx i j (k-1);
      liat_equals_init k gen;
      eq.reflexivity (SP.foldm_snoc add liat);
      mul.congruence last (SP.foldm_snoc add liat) add.unit (SP.foldm_snoc add liat);
      eq.transitivity (last * SP.foldm_snoc add liat)
                      (add.unit * SP.foldm_snoc add liat)
                      (add.unit);
                      
      eq.reflexivity (SP.foldm_snoc add (SB.init (k-1) gen));  
      matrix_mul_unit_ijth add mul m (k-1) j; // This one reduces the rlimits needs to default
      add.congruence last (SP.foldm_snoc add liat) add.unit add.unit;
      add.identity add.unit;
      SP.foldm_snoc_decomposition add full;
      eq.transitivity (SP.foldm_snoc add full)
                      (add.mult add.unit add.unit)
                      add.unit
              
let matrix_right_mul_identity_aux_2 #c #eq #m 
                                    (add: CE.cm c eq) 
                                    (mul: CE.cm c eq{is_absorber add.unit mul}) 
                                    (mx: matrix c m m)
                                    (i j: under m) (k:nat{k=j+1})                     
  : Lemma (ensures SP.foldm_snoc add (SB.init k (fun (k: under m) 
                                                 -> ijth mx i k `mul.mult` 
                                                   ijth (matrix_mul_unit add mul m) k j))
                   `eq.eq` ijth mx i j) = 
  let unit = matrix_mul_unit add mul m in
  let mxu = matrix_mul add mul mx unit in
  let ( * ) = mul.mult in
  let ( $=$ ) = eq.eq in
  let gen = fun (k: under m) -> ijth mx i k * ijth unit k j in  
  let full = SB.init k gen in
  let liat,last = SProp.un_snoc full in
  matrix_right_mul_identity_aux_1 add mul mx i j j;
  liat_equals_init k gen;
  mul.identity (ijth mx i j);
  eq.reflexivity last; 
  add.congruence last (SP.foldm_snoc add liat) last add.unit;
  matrix_mul_unit_ijth add mul m (k-1) j; // This one reduces the rlimits needs to default
  add.identity last;
  add.commutativity last add.unit;
  mul.commutativity (ijth mx i j) mul.unit;
  eq.transitivity (add.mult last add.unit) (add.mult add.unit last) last;
  SP.foldm_snoc_decomposition add full;    
  eq.transitivity (SP.foldm_snoc add full) (add.mult last add.unit) last;                         
  eq.transitivity last (mul.unit * ijth mx i j) (ijth mx i j);
  eq.transitivity (SP.foldm_snoc add full) last (ijth mx i j) 

let rec matrix_right_mul_identity_aux_3 #c #eq #m 
                                        (add: CE.cm c eq) 
                                       (mul: CE.cm c eq{is_absorber add.unit mul}) 
                                       (mx: matrix c m m)
                                       (i j: under m) (k:under (m+1){k>j+1})                         
  : Lemma (ensures SP.foldm_snoc add (SB.init k 
                     (fun (k: under m) -> ijth mx i k `mul.mult` ijth (matrix_mul_unit add mul m) k j))
                   `eq.eq` ijth mx i j)
          (decreases k) = 
  if (k-1) > j+1 then matrix_right_mul_identity_aux_3 add mul mx i j (k-1)
  else matrix_right_mul_identity_aux_2 add mul mx i j (k-1);
  let unit = matrix_mul_unit add mul m in
  let mxu = matrix_mul add mul mx unit in
  let ( * ) = mul.mult in
  let ( $=$ ) = eq.eq in
  let gen = fun (k: under m) -> ijth mx i k * ijth unit k j in  
  let subgen (i: under (k)) = gen i in
  let full = SB.init k gen in
  SP.foldm_snoc_decomposition add full;
  liat_equals_init k gen;   
  let liat,last = SProp.un_snoc full in
  SB.lemma_eq_elim liat (SB.init (k-1) gen); 
  add.identity add.unit;
  mul.commutativity (ijth mx i (k-1)) add.unit;
  eq.reflexivity (SP.foldm_snoc add (SB.init (k-1) gen));  
  matrix_mul_unit_ijth add mul m (k-1) j; // This one reduces the rlimits needs to default
  add.congruence last (SP.foldm_snoc add (SB.init (k-1) gen)) 
    add.unit (SP.foldm_snoc add (SB.init (k-1) gen));
  add.identity (SP.foldm_snoc add (SB.init (k-1) gen));
  eq.transitivity (SP.foldm_snoc add full)
                  (add.mult add.unit (SP.foldm_snoc add (SB.init (k-1) gen)))
                  (SP.foldm_snoc add (SB.init (k-1) gen));
  eq.transitivity (SP.foldm_snoc add full)
                  (SP.foldm_snoc add (SB.init (k-1) gen))
                  (ijth mx i j) 
 
let matrix_right_identity_aux #c #eq #m 
                              (add: CE.cm c eq) 
                              (mul: CE.cm c eq{is_absorber add.unit mul}) 
                              (mx: matrix c m m)
                              (i j: under m) (k:under (m+1))                         
  : Lemma (ensures SP.foldm_snoc add (SB.init k 
                     (fun (k: under m) -> ijth mx i k `mul.mult` ijth (matrix_mul_unit add mul m) k j))
                   `eq.eq`
                   (if k>j then ijth mx i j else add.unit))
          (decreases k) =  
  if k=0 then matrix_right_mul_identity_aux_0 add mul mx i j k
  else if k <= j then matrix_right_mul_identity_aux_1 add mul mx i j k
  else if k = j+1 then matrix_right_mul_identity_aux_2 add mul mx i j k
  else matrix_right_mul_identity_aux_3 add mul mx i j k
 
let matrix_left_mul_identity_aux_0 #c #eq #m 
                                   (add: CE.cm c eq) 
                                   (mul: CE.cm c eq{is_absorber add.unit mul}) 
                                   (mx: matrix c m m)
                                   (i j: under m) (k:nat{k=0})
  : Lemma (ensures SP.foldm_snoc add (SB.init k 
            (fun (k: under m) -> ijth (matrix_mul_unit add mul m) i k `mul.mult` ijth mx k j)) 
           `eq.eq` add.unit) = eq.reflexivity add.unit 
           
#restart-solver           
let rec matrix_left_mul_identity_aux_1 #c #eq #m 
                                       (add: CE.cm c eq) 
                                       (mul: CE.cm c eq{is_absorber add.unit mul}) 
                                       (mx: matrix c m m)
                                       (i j: under m) (k:nat{k<=i /\ k>0})  
  : Lemma (ensures SP.foldm_snoc add (SB.init k 
            (fun (k: under m) -> ijth (matrix_mul_unit add mul m) i k `mul.mult` ijth mx k j)) 
           `eq.eq` add.unit) = 
  let unit = matrix_mul_unit add mul m in
  let mxu = matrix_mul add mul mx unit in
  let ( * ) = mul.mult in
  let ( $=$ ) = eq.eq in
  let gen (k: under m) = ijth unit i k * ijth mx k j in 
  let full = SB.init k gen in
  let liat,last = SProp.un_snoc full in        
  if k=1 then matrix_left_mul_identity_aux_0 add mul mx i j (k-1)
  else matrix_left_mul_identity_aux_1 add mul mx i j (k-1);
  liat_equals_init k gen;
  eq.reflexivity (SP.foldm_snoc add liat);
  SP.foldm_snoc_decomposition add full;
  mul.congruence last (SP.foldm_snoc add liat) add.unit (SP.foldm_snoc add liat);
  eq.transitivity (last * SP.foldm_snoc add liat)
                  (add.unit * SP.foldm_snoc add liat)
                  (add.unit);
  add.congruence last (SP.foldm_snoc add liat) add.unit add.unit;
  add.identity add.unit;
  eq.transitivity (SP.foldm_snoc add full)
                  (add.mult add.unit add.unit)
                  add.unit 

#push-options "--z3rlimit 20"
let matrix_left_mul_identity_aux_2 #c #eq #m 
                                       (add: CE.cm c eq) 
                                       (mul: CE.cm c eq{is_absorber add.unit mul}) 
                                       (mx: matrix c m m)
                                       (i j: under m) (k:nat{k=i+1})  
  : Lemma (ensures SP.foldm_snoc add (SB.init k 
            (fun (k: under m) -> ijth (matrix_mul_unit add mul m) i k `mul.mult` ijth mx k j)) 
           `eq.eq` ijth mx i j) =  
  let unit = matrix_mul_unit add mul m in
  let mxu = matrix_mul add mul mx unit in 
  let ( * ) = mul.mult in
  let ( $=$ ) = eq.eq in
  let gen (k: under m) = ijth unit i k * ijth mx k j in 
  let full = SB.init k gen in
  let liat,last = SProp.un_snoc full in 
  assert (k-1 <= i /\ k-1 >= 0);
  if (k-1)=0 then matrix_left_mul_identity_aux_0 add mul mx i j (k-1)
  else matrix_left_mul_identity_aux_1 add mul mx i j (k-1);
  matrix_mul_unit_ijth add mul m i (k-1); // This one reduces the rlimits needs to default
  SP.foldm_snoc_decomposition add full;
  liat_equals_init k gen; 
  mul.identity (ijth mx i j);
  eq.reflexivity last; 
  add.congruence last (SP.foldm_snoc add liat) last add.unit;
  add.identity last;
  add.commutativity last add.unit;
  mul.commutativity (ijth mx i j) mul.unit;
  eq.transitivity (add.mult last add.unit) (add.mult add.unit last) last;
  eq.transitivity (SP.foldm_snoc add full) (add.mult last add.unit) last;                         
  eq.transitivity last (mul.unit * ijth mx i j) (ijth mx i j); 
  eq.transitivity (SP.foldm_snoc add full) last (ijth mx i j)
 
let rec matrix_left_mul_identity_aux_3 #c #eq #m 
                                       (add: CE.cm c eq) 
                                       (mul: CE.cm c eq{is_absorber add.unit mul}) 
                                       (mx: matrix c m m)
                                       (i j: under m) (k:under(m+1){k>i+1})  
  : Lemma (ensures SP.foldm_snoc add (SB.init k 
            (fun (k: under m) -> ijth (matrix_mul_unit add mul m) i k `mul.mult` ijth mx k j)) 
           `eq.eq` ijth mx i j) =  
  let unit = matrix_mul_unit add mul m in
  let mxu = matrix_mul add mul mx unit in 
  let ( * ) = mul.mult in
  let ( $=$ ) = eq.eq in
  let gen (k: under m) = ijth unit i k * ijth mx k j in   
  let full = SB.init k gen in
  if (k-1 = i+1) then matrix_left_mul_identity_aux_2 add mul mx i j (k-1)
  else matrix_left_mul_identity_aux_3 add mul mx i j (k-1);
  matrix_mul_unit_ijth add mul m i (k-1); // This one reduces the rlimits needs to default
  SP.foldm_snoc_decomposition add full;
  liat_equals_init k gen;  
  let liat,last = SProp.un_snoc full in
  SB.lemma_eq_elim liat (SB.init (k-1) gen); 
  add.identity add.unit;
  mul.commutativity (ijth mx i (k-1)) add.unit;
  eq.reflexivity (SP.foldm_snoc add (SB.init (k-1) gen));
  add.congruence last (SP.foldm_snoc add (SB.init (k-1) gen)) 
    add.unit (SP.foldm_snoc add (SB.init (k-1) gen));
  add.identity (SP.foldm_snoc add (SB.init (k-1) gen));
  eq.transitivity (SP.foldm_snoc add full)
                  (add.mult add.unit (SP.foldm_snoc add (SB.init (k-1) gen)))
                  (SP.foldm_snoc add (SB.init (k-1) gen));
  eq.transitivity (SP.foldm_snoc add full)
                  (SP.foldm_snoc add (SB.init (k-1) gen))
                  (ijth mx i j) 
  
let matrix_left_identity_aux #c #eq #m 
                        (add: CE.cm c eq) 
                        (mul: CE.cm c eq{is_absorber add.unit mul}) 
                        (mx: matrix c m m)
                        (i j: under m)  (k:under (m+1)) 
  : Lemma (ensures SP.foldm_snoc add (SB.init k 
            (fun (k: under m) -> ijth (matrix_mul_unit add mul m) i k `mul.mult` ijth mx k j)) 
           `eq.eq` (if k>i then ijth mx i j else add.unit))
          (decreases k) = 
  if k=0 then matrix_left_mul_identity_aux_0 add mul mx i j k
  else if k <= i then matrix_left_mul_identity_aux_1 add mul mx i j k
  else if k = i+1 then matrix_left_mul_identity_aux_2 add mul mx i j k
  else matrix_left_mul_identity_aux_3 add mul mx i j k
   
let matrix_mul_right_identity #c #eq #m (add: CE.cm c eq) 
                              (mul: CE.cm c eq{is_absorber add.unit mul}) 
                              (mx: matrix c m m)
  : Lemma (matrix_mul add mul mx (matrix_mul_unit add mul m) `matrix_eq_fun eq` mx) =   
  let unit = matrix_mul_unit add mul m in
  let mxu = matrix_mul add mul mx unit in
  let ( * ) = mul.mult in
  let ( $=$ ) = eq.eq in
  let aux (i j: under m) : Lemma (ijth mxu i j $=$ ijth mx i j) = 
    let gen = fun (k: under m) -> ijth mx i k * ijth unit k j in
    matrix_mul_ijth_eq_sum_of_seq_for_init add mul mx unit i j gen;
    let seq = SB.init m gen in       
    matrix_right_identity_aux add mul mx i j m
    in Classical.forall_intro_2 aux;
  matrix_equiv_from_element_eq eq mxu mx  
 
let matrix_mul_left_identity #c #eq #m (add: CE.cm c eq) 
                              (mul: CE.cm c eq{is_absorber add.unit mul}) 
                              (mx: matrix c m m)
  : Lemma (matrix_mul add mul (matrix_mul_unit add mul m) mx `matrix_eq_fun eq` mx) =   
  let unit = matrix_mul_unit add mul m in
  let mxu = matrix_mul add mul unit mx in
  let ( * ) = mul.mult in
  let ( $=$ ) = eq.eq in
  let aux (i j: under m) : squash (ijth mxu i j $=$ ijth mx i j) = 
    let gen (k: under m) = ijth unit i k * ijth mx k j in
    matrix_mul_ijth_eq_sum_of_seq_for_init add mul unit mx i j gen;
    let seq = SB.init m gen in       
    matrix_left_identity_aux add mul mx i j m
    in  
  matrix_equiv_from_proof eq mxu mx aux 
 
let matrix_mul_identity #c #eq #m (add: CE.cm c eq) 
                              (mul: CE.cm c eq{is_absorber add.unit mul}) 
                              (mx: matrix c m m)
  : Lemma (matrix_mul add mul mx (matrix_mul_unit add mul m) `matrix_eq_fun eq` mx /\
           matrix_mul add mul (matrix_mul_unit add mul m) mx `matrix_eq_fun eq` mx) =
  matrix_mul_left_identity add mul mx;
  matrix_mul_right_identity add mul mx
 
let dot_of_equal_sequences #c #eq (add mul: CE.cm c eq) m
                                  (p q r s: (z:SB.seq c{SB.length z == m}))
  : Lemma (requires eq_of_seq eq p r /\ eq_of_seq eq q s) 
          (ensures eq.eq (dot add mul p q) (dot add mul r s)) = 
  eq_of_seq_element_equality eq p r;
  eq_of_seq_element_equality eq q s;
  let aux (i: under (SB.length p)) : Lemma (SB.index (seq_of_products mul p q) i `eq.eq`
                                            SB.index (seq_of_products mul r s) i)
    = mul.congruence (SB.index p i) (SB.index q i) (SB.index r i) (SB.index s i) 
    in Classical.forall_intro aux;  
  eq_of_seq_from_element_equality eq (seq_of_products mul p q) (seq_of_products mul r s);
  SP.foldm_snoc_equality add (seq_of_products mul p q) (seq_of_products mul r s)  
 
let matrix_mul_congruence #c #eq #m #n #p (add mul: CE.cm c eq)  
                    (mx: matrix c m n) (my: matrix c n p) 
                    (mz: matrix c m n) (mw: matrix c n p)
  : Lemma (requires matrix_eq_fun eq mx mz /\ matrix_eq_fun eq my mw)
          (ensures matrix_eq_fun eq (matrix_mul add mul mx my) (matrix_mul add mul mz mw)) =  
  let aux (i: under m) (k: under p) : Lemma (ijth (matrix_mul add mul mx my) i k 
                                      `eq.eq` ijth (matrix_mul add mul mz mw) i k) = 
    let init_xy (j: under n) = mul.mult (ijth mx i j) (ijth my j k) in
    let init_zw (j: under n) = mul.mult (ijth mz i j) (ijth mw j k) in
    matrix_mul_ijth_eq_sum_of_seq_for_init add mul mx my i k init_xy;
    matrix_mul_ijth_eq_sum_of_seq_for_init add mul mz mw i k init_zw; 
    let sp_xy = SB.init n init_xy in
    let sp_zw = SB.init n init_zw in
    let all_eq (j: under n) : Lemma (init_xy j `eq.eq` init_zw j) = 
      matrix_equiv_ijth eq mx mz i j;
      matrix_equiv_ijth eq my mw j k;
      mul.congruence (ijth mx i j) (ijth my j k) (ijth mz i j) (ijth mw j k) 
    in Classical.forall_intro all_eq;      
    eq_of_seq_from_element_equality eq sp_xy sp_zw;
    SP.foldm_snoc_equality add sp_xy sp_zw
  in matrix_equiv_from_proof eq (matrix_mul add mul mx my) (matrix_mul add mul mz mw) aux
 
#push-options "--z3rlimit 30 --ifuel 0 --fuel 0"
let matrix_mul_is_left_distributive #c #eq #m #n #p (add: CE.cm c eq)
                                    (mul: CE.cm c eq{is_fully_distributive mul add /\ is_absorber add.unit mul}) 
                                    (mx: matrix c m n) (my mz: matrix c n p)
  : Lemma (matrix_mul add mul mx (matrix_add add my mz) `matrix_eq_fun eq`
           matrix_add add (matrix_mul add mul mx my) (matrix_mul add mul mx mz)) = 
  let myz = matrix_add add my mz in
  let mxy = matrix_mul add mul mx my in
  let mxz = matrix_mul add mul mx mz in
  let lhs = matrix_mul add mul mx myz in
  let rhs = matrix_add add mxy mxz in
  let sum_j (f: under n -> c) = SP.foldm_snoc add (SB.init n f) in
  let sum_k (f: under p -> c) = SP.foldm_snoc add (SB.init p f) in 
  let aux i k : Lemma (ijth lhs i k `eq.eq` ijth rhs i k) = 
    let init_lhs j = mul.mult (ijth mx i j) (ijth myz j k) in
    let init_xy j  = mul.mult (ijth mx i j) (ijth my j k) in
    let init_xz j  = mul.mult (ijth mx i j) (ijth mz j k) in
    let init_rhs j = mul.mult (ijth mx i j) (ijth my j k) `add.mult` 
                     mul.mult (ijth mx i j) (ijth mz j k) in
    Classical.forall_intro eq.reflexivity; 
    matrix_mul_ijth_eq_sum_of_seq_for_init add mul mx myz i k init_lhs; 
    matrix_mul_ijth_eq_sum_of_seq_for_init add mul mx my i k init_xy;
    matrix_mul_ijth_eq_sum_of_seq_for_init add mul mx mz i k init_xz;    
    SP.foldm_snoc_split_seq add (SB.init n init_xy) 
                                (SB.init n init_xz) 
                                (SB.init n init_rhs) 
                                (fun j -> ()); 
    eq.symmetry  (ijth rhs i k) (sum_j init_rhs);
    SP.foldm_snoc_of_equal_inits add init_lhs init_rhs;
    eq.transitivity (ijth lhs i k)
                    (sum_j init_rhs)
                    (ijth rhs i k) 
  in matrix_equiv_from_proof eq lhs rhs aux 
#pop-options

let matrix_mul_is_right_distributive #c #eq #m #n #p (add: CE.cm c eq)
                                    (mul: CE.cm c eq{is_fully_distributive mul add /\ is_absorber add.unit mul}) 
                                    (mx my: matrix c m n) (mz: matrix c n p)
  : Lemma (matrix_mul add mul (matrix_add add mx my) mz `matrix_eq_fun eq`
           matrix_add add (matrix_mul add mul mx mz) (matrix_mul add mul my mz)) = 
  let mxy = matrix_add add mx my in
  let mxz = matrix_mul add mul mx mz in
  let myz = matrix_mul add mul my mz in
  let lhs = matrix_mul add mul mxy mz in
  let rhs = matrix_add add mxz myz in
  let sum_j (f: under n -> c) = SP.foldm_snoc add (SB.init n f) in
  let sum_k (f: under p -> c) = SP.foldm_snoc add (SB.init p f) in 
  let aux i k : Lemma (ijth lhs i k `eq.eq`
                       ijth rhs i k) = 
    let init_lhs j = mul.mult (ijth mxy i j) (ijth mz j k) in
    let init_xz j  = mul.mult (ijth mx i j) (ijth mz j k) in
    let init_yz j  = mul.mult (ijth my i j) (ijth mz j k) in
    let init_rhs j = mul.mult (ijth mx i j) (ijth mz j k) `add.mult`
                     mul.mult (ijth my i j) (ijth mz j k) in
    Classical.forall_intro eq.reflexivity; 
    matrix_mul_ijth_eq_sum_of_seq_for_init add mul mxy mz i k init_lhs; 
    matrix_mul_ijth_eq_sum_of_seq_for_init add mul mx mz i k init_xz;
    matrix_mul_ijth_eq_sum_of_seq_for_init add mul my mz i k init_yz;
    SP.foldm_snoc_split_seq add (SB.init n init_xz) 
                                (SB.init n init_yz) 
                                (SB.init n init_rhs) 
                                (fun j -> ()); 
    eq.symmetry (ijth rhs i k) (sum_j init_rhs); 
    SP.foldm_snoc_of_equal_inits add init_lhs init_rhs;
    eq.transitivity (ijth lhs i k)
                    (sum_j init_rhs)
                    (ijth rhs i k) 
  in matrix_equiv_from_proof eq lhs rhs aux
#pop-options 
