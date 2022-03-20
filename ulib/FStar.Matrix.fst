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
module SProp = FStar.Seq.Properties
module ML = FStar.Math.Lemmas

open FStar.IntegerIntervals   
open FStar.Mul

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

let foldm_snoc_last #c #eq (cm: CE.cm c eq) (s: SB.seq c{SB.length s > 0})
  : Lemma (SP.foldm_snoc cm s == cm.mult (snd (SProp.un_snoc s)) 
                                         (SP.foldm_snoc cm (fst (SProp.un_snoc s)))) 
  = ()


let matrix_submatrix_lemma #c (#m: not_less_than 2) (#n: pos)  
                           (generator: matrix_generator c m n)
  : Lemma ((matrix_seq generator) == (matrix_seq (fun (i:under(m-1)) (j:under n) -> generator i j) `SB.append` SB.init n (generator (m-1))))
  = SB.lemma_eq_elim (matrix_seq (fun (i:under (m-1)) (j:under n) -> generator i j)) (matrix_seq #c #(m-1) #n generator);
    SB.lemma_eq_elim (SB.slice (matrix_seq generator) ((m-1)*n) (m*n)) (SB.init n (generator (m-1)));
    matrix_seq_decomposition_lemma generator

(* This one could be probably written more efficiently -- 
   but this implementation also works. *)
#push-options "--ifuel 0 --fuel 0 --z3rlimit 25"
#restart-solver
let rec matrix_fold_equals_fold_of_seq_folds #c #eq #m #n cm generator : Lemma 
  (ensures foldm cm (init generator) `eq.eq`
           SP.foldm_snoc cm (SB.init m (fun i -> SP.foldm_snoc cm (SB.init n (generator i)))) /\ 
           SP.foldm_snoc cm (seq_of_matrix (init generator)) `eq.eq`
           SP.foldm_snoc cm (SB.init m (fun i -> SP.foldm_snoc cm (SB.init n (generator i))))) 
  (decreases m) =
  let lhs_seq = matrix_seq generator in
  let rhs_seq = SB.init m (fun i -> SP.foldm_snoc cm (SB.init n (generator i))) in
  let lhs = SP.foldm_snoc cm (matrix_seq generator) in
  let rhs = SP.foldm_snoc cm rhs_seq in
  if m=1 then begin
    SP.foldm_snoc_singleton cm (SP.foldm_snoc cm (SB.init n (generator 0)));
    SB.lemma_eq_elim (SB.create 1 (SP.foldm_snoc cm (SB.init n (generator 0))))
                  (SB.init m (fun i -> SP.foldm_snoc cm (SB.init n (generator i))));
    SB.lemma_eq_elim (matrix_seq generator) (SB.init n (generator 0));
    eq.symmetry rhs lhs 
  end else 
  let matrix = matrix_seq generator in 
  let subgen = (fun (i:under (m-1)) (j:under n) -> generator i j) in 
  let submatrix = SB.slice (matrix_seq generator) 0 ((m-1)*n) in
  let last_row = SB.slice (matrix_seq #c #m #n generator) ((m-1)*n) (m*n) in
  Classical.forall_intro_2 (Classical.move_requires_2 eq.symmetry);
  matrix_fold_snoc_lemma cm generator;
  Math.Lemmas.multiplication_order_lemma (m) (m-1) n;
  assert ((m-1)*n < m*n);
  SB.lemma_len_slice (matrix_seq generator) ((m-1)*n) (m*n); 
  SB.lemma_eq_elim (matrix_seq subgen) submatrix;
  matrix_fold_equals_fold_of_seq_folds cm subgen;    
  SB.lemma_eq_elim last_row (SB.init n (generator (m-1))); 
  matrix_submatrix_lemma generator;
  let rec_seq = SB.init (m-1) (fun i -> SP.foldm_snoc cm (SB.init n (subgen i))) in
  let rec_subseq = SB.init (m-1) (fun i -> SP.foldm_snoc cm (SB.init n (generator i))) in
  let aux_eq (i: under (m-1)) : Lemma (SB.index rec_seq i == SB.index rec_subseq i) = 
    SB.lemma_eq_elim (SB.init n (subgen i)) (SB.init n (generator i));
  () in 
  Classical.forall_intro aux_eq;
  matrix_append_snoc_lemma generator;
  SP.foldm_snoc_append cm (matrix_seq subgen) last_row;
  SB.lemma_eq_elim rhs_seq (SProp.snoc rec_subseq (SP.foldm_snoc cm (SB.init n (generator (m-1)))));
  let liat_rhs_seq, last_rhs_seq = SProp.un_snoc rhs_seq in
  SB.lemma_eq_elim liat_rhs_seq rec_seq;
  foldm_snoc_last cm rhs_seq;
  SB.lemma_eq_elim rec_subseq liat_rhs_seq; 
  eq.reflexivity (SP.foldm_snoc cm last_row);
  cm.congruence (SP.foldm_snoc cm (matrix_seq subgen)) (SP.foldm_snoc cm last_row)
                (SP.foldm_snoc cm liat_rhs_seq) (last_rhs_seq);
  eq.transitivity lhs 
                  (SP.foldm_snoc cm (matrix_seq subgen) `cm.mult` SP.foldm_snoc cm last_row)
                  (SP.foldm_snoc cm liat_rhs_seq `cm.mult` last_rhs_seq); 
  cm.commutativity (SP.foldm_snoc cm liat_rhs_seq) last_rhs_seq;
  eq.transitivity lhs (SP.foldm_snoc cm liat_rhs_seq `cm.mult` last_rhs_seq) rhs;
  matrix_fold_equals_fold_of_seq cm (init generator);
  assert (SP.foldm_snoc cm (matrix_seq generator) `eq.eq` rhs);
  assert (lhs == SP.foldm_snoc cm (matrix_seq generator));
  assert (lhs `eq.eq` rhs);
  assert_spinoff (foldm cm (init generator) == lhs);
  assert (SP.foldm_snoc cm (init generator) `eq.eq` rhs);
  () 
#pop-options 

(* This auxiliary lemma shows that the fold of the last line of a matrix
   is equal to the corresponding fold of the generator function *) 
let matrix_last_line_equals_gen_fold #c #eq 
                                        (#m #n: pos)  
                                        (cm: CE.cm c eq) 
                                        (generator: matrix_generator c m n) 
    : Lemma (SP.foldm_snoc cm (SB.slice (matrix_seq generator) ((m-1)*n) (m*n)) 
            `eq.eq` CF.fold cm 0 (n-1) (generator (m-1)))
    = 

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
 

#push-options "--ifuel 0 --fuel 0 --z3rlimit 1"
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
            == CF.fold cm 0 (n-1) (generator 0));
    ()
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
  = let slice = SB.slice #c in
    let foldm_snoc = SP.foldm_snoc #c #eq in
    let init = SB.init #c in
    let lemma_eq_elim = SB.lemma_eq_elim #c in 
    matrix_fold_aux cm m n generator

let rec eq_of_seq #c (eq:CE.equiv c) (s1 s2: SB.seq c) 
  : Tot prop (decreases SB.length s1) = 
  (SB.length s1 = SB.length s2 /\
   (SB.length s1 = 0 \/ (
    let s1s, s1l = SProp.un_snoc s1 in
     let s2s, s2l = SProp.un_snoc s2 in
      eq.eq s1l s2l /\ eq_of_seq eq s1s s2s)))

let rec eq_of_seq_element_equality #c (eq: CE.equiv c) (s1 s2: SB.seq c)
  : Lemma (requires eq_of_seq eq s1 s2) 
          (ensures SB.length s1 = SB.length s2 /\ (forall (i: under (SB.length s1)). (SB.index s1 i `eq.eq` SB.index s2 i))) 
          (decreases SB.length s1)
  = 
  if (SB.length s1 > 0) then 
  let s1liat, s1last = SProp.un_snoc s1 in
  let s2liat, s2last = SProp.un_snoc s2 in
  eq_of_seq_element_equality eq s1liat s2liat

let rec eq_of_seq_from_element_equality #c (eq: CE.equiv c) (s1 s2: SB.seq c)
  : Lemma (requires (SB.length s1 = SB.length s2) /\ (forall (i: under (SB.length s1)). (SB.index s1 i `eq.eq` SB.index s2 i)))
          (ensures eq_of_seq eq s1 s2)
          (decreases SB.length s1) = 
  if SB.length s1 = 0 then () else 
  let s1liat, s1last = SProp.un_snoc s1 in
  let s2liat, s2last = SProp.un_snoc s2 in  
  eq_of_seq_from_element_equality eq s1liat s2liat

let eq_of_seq_condition #c (eq: CE.equiv c) (s1 s2: SB.seq c)
  : Lemma ((SB.length s1==SB.length s2) /\ (forall (i: under (SB.length s1)). (SB.index s1 i `eq.eq` SB.index s2 i)) <==>
            eq_of_seq eq s1 s2) = 
  Classical.move_requires_2 (eq_of_seq_element_equality eq) s1 s2;
  Classical.move_requires_2 (eq_of_seq_from_element_equality eq) s1 s2

let rec eq_of_seq_reflexivity #c (eq: CE.equiv c) (s: SB.seq c)
  : Lemma (ensures eq_of_seq eq s s) (decreases SB.length s) = 
  if SB.length s > 0 then 
  let liat, last = SProp.un_snoc s in
  eq_of_seq_reflexivity eq liat;
  eq.reflexivity last

let rec eq_of_seq_symmetry #c (eq: CE.equiv c) (s1 s2: SB.seq c)
  : Lemma (requires eq_of_seq eq s1 s2) (ensures eq_of_seq eq s2 s1) (decreases SB.length s1) =  
  if SB.length s1 > 0 then 
  let lia1, las1 = SProp.un_snoc s1 in
  let lia2, las2 = SProp.un_snoc s2 in
  eq_of_seq_symmetry eq lia1 lia2;
  eq.symmetry las1 las2

let rec eq_of_seq_transitivity #c (eq: CE.equiv c) (s1 s2 s3: SB.seq c)
  : Lemma (requires eq_of_seq eq s1 s2 /\ eq_of_seq eq s2 s3) (ensures eq_of_seq eq s1 s3) (decreases SB.length s1) =  
  if SB.length s1 > 0 then 
  let lia1, las1 = SProp.un_snoc s1 in
  let lia2, las2 = SProp.un_snoc s2 in
  let lia3, las3 = SProp.un_snoc s3 in
  eq_of_seq_transitivity eq lia1 lia2 lia3;
  eq.transitivity las1 las2 las3

let seq_equiv #c (eq:CE.equiv c) : (CE.equiv (SB.seq c)) = 
  CE.EQ (eq_of_seq eq) (eq_of_seq_reflexivity eq)
                       (eq_of_seq_symmetry eq)
                       (eq_of_seq_transitivity eq)

let matrix_add_generator #c #eq (#m #n: pos) (add: CE.cm c eq) (ma mb: matrix c m n) 
  : matrix_generator c m n = fun i j -> add.mult (ijth ma i j) (ijth mb i j)

let matrix_add #c #eq (#m #n: pos) (add: CE.cm c eq) (ma mb: matrix c m n) 
  : matrix_of (matrix_add_generator add ma mb)
  = init (matrix_add_generator add ma mb)

let matrix_add_ijth #c #eq (#m #n: pos) (add: CE.cm c eq) (ma mb: matrix c m n) (i: under m) (j: under n)
  : Lemma (ijth (matrix_add add ma mb) i j == add.mult (ijth ma i j) (ijth mb i j)) = ()

let matrix_eq_fun #c (#m #n: pos) (eq: CE.equiv c) (ma mb: matrix c m n) =   
  eq_of_seq eq (seq_of_matrix ma) (seq_of_matrix mb)

let matrix_equiv #c (eq: CE.equiv c) (m n: pos) : CE.equiv (matrix c m n) = 
  CE.EQ (matrix_eq_fun eq)
        (fun m -> eq_of_seq_reflexivity eq (seq_of_matrix m))
        (fun ma mb -> eq_of_seq_symmetry eq (seq_of_matrix ma) (seq_of_matrix mb))
        (fun ma mb mc -> eq_of_seq_transitivity eq (seq_of_matrix ma) (seq_of_matrix mb) (seq_of_matrix mc))

let matrix_equiv_ijth #c (#m #n: pos) (eq: CE.equiv c) (ma mb: matrix c m n) (i: under m) (j: under n)
  : Lemma (requires (matrix_equiv eq m n).eq ma mb) (ensures ijth ma i j `eq.eq` ijth mb i j) = 
  eq_of_seq_element_equality eq (seq_of_matrix ma) (seq_of_matrix mb)

#push-options "--fuel 1 --z3rlimit 2"
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
#pop-options

let matrix_add_is_associative #c #eq (#m #n: pos) (add: CE.cm c eq) (ma mb mc: matrix c m n)
  : Lemma (matrix_add add (matrix_add add ma mb) mc `(matrix_equiv eq m n).eq` 
           matrix_add add ma (matrix_add add mb mc)) = 
  let rhs = matrix_add add ma (matrix_add add mb mc) in
  let lhs = matrix_add add (matrix_add add ma mb) mc in
  let lemma (i: under m) (j: under n) : Lemma (ijth lhs i j `eq.eq` ijth rhs i j) 
    = add.associativity (ijth ma i j) (ijth mb i j) (ijth mc i j) 
    in Classical.forall_intro_2 lemma;
  matrix_equiv_from_element_eq eq lhs rhs

let matrix_add_is_commutative #c #eq (#m #n: pos) (add: CE.cm c eq) (ma mb: matrix c m n)
  : Lemma (matrix_add add ma mb `(matrix_equiv eq m n).eq` matrix_add add mb ma) =
  let lhs = matrix_add add ma mb in
  let rhs = matrix_add add mb ma in
  let lemma (i: under m) (j: under n) 
    : Lemma (ijth lhs i j `eq.eq` ijth rhs i j) 
    = add.commutativity (ijth ma i j) (ijth mb i j)
    in Classical.forall_intro_2 lemma;
  matrix_equiv_from_element_eq eq lhs rhs

let matrix_add_congruence #c #eq (#m #n: pos) (add: CE.cm c eq) (ma mb mc md: matrix c m n)
  : Lemma (requires matrix_eq_fun eq ma mc /\ matrix_eq_fun eq mb md)
          (ensures matrix_add add ma mb `matrix_eq_fun eq` matrix_add add mc md) =
  let lhs = matrix_add add ma mb in
  let rhs = matrix_add add mc md in
  let lemma (i: under m) (j: under n) 
    : Lemma (ijth lhs i j `eq.eq` ijth rhs i j) 
    = matrix_equiv_ijth eq ma mc i j;
      matrix_equiv_ijth eq mb md i j;
      add.congruence (ijth ma i j) (ijth mb i j) (ijth mc i j) (ijth md i j)
    in Classical.forall_intro_2 lemma;
  matrix_equiv_from_element_eq eq lhs rhs

let matrix_add_zero #c #eq (add: CE.cm c eq) (m n: pos) : (z: matrix c m n {
  forall (i: under m) (j: under n). ijth z i j == add.unit
}) = matrix_of_seq m n (SB.create (m*n) add.unit)

let matrix_add_identity #c #eq (add: CE.cm c eq) (#m #n: pos) (mx: matrix c m n)
  : Lemma (matrix_add add (matrix_add_zero add m n) mx `matrix_eq_fun eq` mx) =
  let zero = matrix_add_zero add m n in
  let lhs = matrix_add add zero mx in
  let rhs = matrix_add add mx zero in
  let lemma (i: under m) (j: under n) 
    : Lemma (ijth lhs i j `eq.eq` ijth mx i j) 
    = add.identity (ijth mx i j) 
    in Classical.forall_intro_2 lemma;
  matrix_equiv_from_element_eq eq lhs mx 

let matrix_add_comm_monoid #c #eq (add: CE.cm c eq) (m n: pos)
  : CE.cm (matrix c m n) (matrix_equiv eq m n) 
  = CE.CM (matrix_add_zero add m n)
          (matrix_add add)
          (matrix_add_identity add)
          (matrix_add_is_associative add)
          (matrix_add_is_commutative add)
          (matrix_add_congruence add)
