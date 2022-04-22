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
 
val transposed_matrix_gen (#c:_) (#m:pos) (#n:pos) (generator: matrix_generator c m n) 
  : (f: matrix_generator c n m { forall i j. f j i == generator i j }) 

val matrix_transpose_is_permutation (#c:_) (#m #n: pos) 
                                    (generator: matrix_generator c m n)
  : Lemma (SP.is_permutation (seq_of_matrix (init generator))
                             (seq_of_matrix (init (transposed_matrix_gen generator)))
                             (transpose_ji m n))
                             
val matrix_fold_equals_fold_of_transpose (#c:_) (#eq:_)
                                         (#m #n: pos) 
                                         (cm: CE.cm c eq) 
                                         (gen: matrix_generator c m n)
  : Lemma (foldm cm (init gen) `eq.eq`
           foldm cm (init (transposed_matrix_gen gen)))

(* The equivalence relation defined for matrices of given dimensions *)
val matrix_equiv : (#c: Type) ->
                   (eq:  CE.equiv c) ->
                   (m: pos) -> (n: pos) ->
                   CE.equiv (matrix c m n)                   

(* element-wise matrix equivalence lemma *)
val matrix_equiv_ijth (#c:_) (#m #n: pos) (eq: CE.equiv c) 
                      (ma mb: matrix c m n) (i: under m) (j: under n)
  : Lemma (requires (matrix_equiv eq m n).eq ma mb) 
          (ensures ijth ma i j `eq.eq` ijth mb i j) 

(* We can always establish matrix equivalence from element-wise equivalence *)
val matrix_equiv_from_element_eq (#c:_) (#m #n: pos) (eq: CE.equiv c) (ma mb: matrix c m n)
  : Lemma (requires (forall (i: under m) (j: under n). ijth ma i j `eq.eq` ijth mb i j))
          (ensures (matrix_equiv eq m n).eq ma mb)

(* 
   Notice that even though we can (and will) construct CommMonoid for matrix addition,
   we still publish the operations as well since as soon as we get to multiplication,
   results usually have different dimensions, so it would be convenient to have both
   the CommMonoid for matrix addition and the explicit addition function.

   This becomes the only way with non-square matrix multiplication, since these 
   would not constitute a monoid to begin with.
*)

(* This version of the lemma is useful if we don't want to invoke 
   Classical.forall_intro_2 in a big proof to conserve resources *)
let matrix_equiv_from_proof #c (#m #n: pos) (eq: CE.equiv c) (ma mb: matrix c m n)
  (proof: (i:under m) -> (j:under n) -> Lemma (eq.eq (ijth ma i j) (ijth mb i j)))
  : Lemma ((matrix_equiv eq m n).eq ma mb)
  = Classical.forall_intro_2 proof; 
    matrix_equiv_from_element_eq eq ma mb 

(* This one is the generator function for sum of matrices *)
let matrix_add_generator #c #eq (#m #n: pos) (add: CE.cm c eq) (ma mb: matrix c m n) 
  : matrix_generator c m n = fun i j -> add.mult (ijth ma i j) (ijth mb i j)

(* This is the matrix sum operation given the addition CommMonoid *)
let matrix_add #c #eq (#m #n: pos) (add: CE.cm c eq) (ma mb: matrix c m n) 
  : matrix_of (matrix_add_generator add ma mb)
  = init (matrix_add_generator add ma mb)  

(* Sum of matrices ijth element lemma *)
let matrix_add_ijth #c #eq (#m #n: pos) (add: CE.cm c eq) (ma mb: matrix c m n) (i: under m) (j: under n)
  : Lemma (ijth (matrix_add add ma mb) i j == add.mult (ijth ma i j) (ijth mb i j)) = ()

(* m*n-sized matrix addition CommMonoid *)
val matrix_add_comm_monoid : (#c:Type) -> 
                             (#eq:CE.equiv c) -> 
                             (add: CE.cm c eq) -> 
                             (m:pos) -> (n: pos) -> 
                             CE.cm (matrix c m n) (matrix_equiv eq m n)


(* Sometimes we want matrix rows and columns to be accessed as sequences *)
let col #c #m #n (mx: matrix c m n) (j: under n) = SB.init m (fun (i: under m) -> ijth mx i j) 

let row #c #m #n (mx: matrix c m n) (i: under m) = SB.init n (fun (j: under n) -> ijth mx i j) 

(* ijth-based and row/col-based element access methods are equivalent *)
val matrix_row_col_lemma (#c:_) (#m #n:pos) (mx: matrix c m n) (i: under m) (j: under n) 
  : Lemma (ijth mx i j == SB.index (row mx i) j /\ ijth mx i j == SB.index (col mx j) i)  

(* This transforms a seq X={Xi} into a seq X={Xi `op` c} *)
let seq_op_const #c #eq (cm: CE.cm c eq) (s: SB.seq c) (const: c) 
  = SB.init (SB.length s) (fun (i: under (SB.length s)) -> cm.mult (SB.index s i) const)

(* Well, technically it is the same thing as above, given cm is commutative. 
   We will still use prefix and postfix applications separately since
   sometimes provable equality (==) rather than `eq.eq` comes in handy  *)
let const_op_seq #c #eq (cm: CE.cm c eq) (const: c) (s: SB.seq c)                       
  = SB.init (SB.length s) (fun (i: under (SB.length s)) -> cm.mult const (SB.index s i))


(* We can get a sequence of products (or sums) from two sequences of equal length *)
let seq_of_products #c #eq (mul: CE.cm c eq) (s: SB.seq c) (t: SB.seq c {SB.length t == SB.length s})
  = SB.init (SB.length s) (fun (i: under (SB.length s)) -> SB.index s i `mul.mult` SB.index t i)

(* As trivial as it seems to be, sometimes this lemma proves to be useful, mostly because 
   lemma_eq_elim invocation is surprisingly costly resources-wise. *)
val seq_of_products_lemma (#c:_) (#eq:_) (mul: CE.cm c eq) 
                          (s: SB.seq c) (t: SB.seq c {SB.length t == SB.length s})
                          (r: SB.seq c { SB.equal r (SB.init (SB.length s) 
                                                             (fun (i: under (SB.length s)) -> 
                                                                    SB.index s i `mul.mult` SB.index t i))})
  : Lemma (seq_of_products mul s t == r)  

(* The usual dot product of two sequences of equal lengths *)
let dot #c #eq (add mul: CE.cm c eq) (s: SB.seq c) (t: SB.seq c{SB.length t == SB.length s}) 
  = SP.foldm_snoc add (seq_of_products mul s t) 

val dot_lemma (#c:_) (#eq:_) (add mul: CE.cm c eq) (s: SB.seq c) (t: SB.seq c{SB.length t == SB.length s}) 
  : Lemma (dot add mul s t == SP.foldm_snoc add (seq_of_products mul s t)) 

(* Of course, it would be best to define the matrix product as a convolution,
   but we don't have all the necessary framework for that level of generality yet. *)
val matrix_mul (#c:_) (#eq:_) (#m #n #p:pos) (add mul: CE.cm c eq) (mx: matrix c m n) (my: matrix c n p)  
  : matrix c m p

(* Both distributivity laws hold for matrices as shown below *)
let is_left_distributive #c #eq (mul add: CE.cm c eq) = 
  forall (x y z: c). mul.mult x (add.mult y z) `eq.eq` add.mult (mul.mult x y) (mul.mult x z)

let is_right_distributive #c #eq (mul add: CE.cm c eq) = 
  forall (x y z: c). mul.mult (add.mult x y) z `eq.eq` add.mult (mul.mult x z) (mul.mult y z)

let is_fully_distributive #c #eq (mul add: CE.cm c eq) = is_left_distributive mul add /\ is_right_distributive mul add

(* 
   This definition is of course far more general than matrices, and should rather 
   be a part of algebra core, as it is relevant to any magma. 
   
   In the process of development of F* abstract algebra framework, this definition
   will probably take its rightful place near the most basic of grouplike structures.

   Also note that this property is defined via forall. We would probably want
   to make such properties opaque to SMT in the future, to avoid verification performance
   issues.
*)
let is_absorber #c #eq (z:c) (op: CE.cm c eq) = 
  forall (x:c). op.mult z x `eq.eq` z /\ op.mult x z `eq.eq` z

(* 
   Similar lemmas to reason about matrix product elements 
   We're going to refactor these a bit, as some are clearly redundant.
   Might want to keep internal usages to one variant of the lemma and
   remove the rest.
*)
val matrix_mul_ijth (#c:_) (#eq:_) (#m #n #k:pos) (add mul: CE.cm c eq) 
                    (mx: matrix c m n) (my: matrix c n k) (i: under m) (h: under k)
  : Lemma (ijth (matrix_mul add mul mx my) i h == dot add mul (row mx i) (col my h))

val matrix_mul_ijth_as_sum (#c:_) (#eq:_) (#m #n #p:pos) (add mul: CE.cm c eq)  
                    (mx: matrix c m n) (my: matrix c n p) (i: under m) (k: under p) 
  : Lemma (ijth (matrix_mul add mul mx my) i k == 
           SP.foldm_snoc add (SB.init n (fun (j: under n) -> mul.mult (ijth mx i j) (ijth my j k))))  

val matrix_mul_ijth_eq_sum_of_seq (#c:_) (#eq:_) (#m #n #p:pos) (add: CE.cm c eq) 
                                  (mul: CE.cm c eq{is_fully_distributive mul add /\ is_absorber add.unit mul}) 
                                  (mx: matrix c m n) (my: matrix c n p) (i: under m) (k: under p)
                                  (r: SB.seq c{r `SB.equal` seq_of_products mul (row mx i) (col my k)})
  : Lemma (ijth (matrix_mul add mul mx my) i k == SP.foldm_snoc add r) 
  
val matrix_mul_ijth_eq_sum_of_seq_for_init (#c:_) (#eq:_) (#m #n #p:pos) (add mul: CE.cm c eq)  
    (mx: matrix c m n) (my: matrix c n p) (i: under m) (k: under p) 
    (f: under n -> c { SB.init n f `SB.equal` seq_of_products mul (row mx i) (col my k)})
  : Lemma (ijth (matrix_mul add mul mx my) i k == SP.foldm_snoc add (SB.init n f))


(* Basically, we prove that (XY)Z = X(YZ) for any matrices of compatible sizes *)
val matrix_mul_is_associative (#c:_) (#eq:_) (#m #n #p #q: pos) (add: CE.cm c eq) 
  (mul: CE.cm c eq{is_fully_distributive mul add /\ is_absorber add.unit mul}) 
  (mx: matrix c m n) (my: matrix c n p) (mz: matrix c p q)
  : Lemma ((matrix_equiv eq m q).eq ((matrix_mul add mul mx my) `matrix_mul add mul` mz)
                            (matrix_mul add mul mx (matrix_mul add mul my mz)))

(* Square identity matrix of size m*m *)
let matrix_mul_unit #c #eq (add mul: CE.cm c eq) m
  : matrix c m m = init (fun i j -> if i=j then mul.unit else add.unit)

(* Matrix multiplicative identity lemmas *)
val matrix_mul_right_identity (#c:_) (#eq:_) (#m: pos) (add: CE.cm c eq) 
                              (mul: CE.cm c eq{is_absorber add.unit mul}) 
                              (mx: matrix c m m)
  : Lemma (matrix_mul add mul mx (matrix_mul_unit add mul m) `(matrix_equiv eq m m).eq` mx)
  
val matrix_mul_left_identity (#c:_) (#eq:_) (#m: pos) (add: CE.cm c eq) 
                             (mul: CE.cm c eq{is_absorber add.unit mul}) 
                             (mx: matrix c m m)
  : Lemma (matrix_mul add mul (matrix_mul_unit add mul m) mx `(matrix_equiv eq m m).eq` mx)
  
val matrix_mul_identity (#c:_) (#eq:_) (#m: pos) (add: CE.cm c eq) 
                        (mul: CE.cm c eq{is_absorber add.unit mul}) 
                        (mx: matrix c m m)
  : Lemma (matrix_mul add mul mx (matrix_mul_unit add mul m) `(matrix_equiv eq m m).eq` mx /\
           matrix_mul add mul (matrix_mul_unit add mul m) mx `(matrix_equiv eq m m).eq` mx)

(* Matrix multiplication of course also respects matrix equivalence *)
val matrix_mul_congruence (#c:_) (#eq:_) (#m #n #p:pos) (add mul: CE.cm c eq)  
                          (mx: matrix c m n) (my: matrix c n p) 
                          (mz: matrix c m n) (mw: matrix c n p)
  : Lemma (requires (matrix_equiv eq m n).eq mx mz /\ (matrix_equiv eq n p).eq my mw)
          (ensures (matrix_equiv eq m p).eq (matrix_mul add mul mx my) 
                                            (matrix_mul add mul mz mw))

(* Both distributivities for matrices *)
val matrix_mul_is_left_distributive (#c:_) (#eq:_) (#m #n #p:pos) (add: CE.cm c eq)
                                    (mul: CE.cm c eq{is_fully_distributive mul add /\ is_absorber add.unit mul}) 
                                    (mx: matrix c m n) (my mz: matrix c n p)
  : Lemma (matrix_mul add mul mx (matrix_add add my mz) `(matrix_equiv eq m p).eq`
           matrix_add add (matrix_mul add mul mx my) (matrix_mul add mul mx mz))
            
val matrix_mul_is_right_distributive (#c:_) (#eq:_) (#m #n #p:pos) (add: CE.cm c eq)
                                    (mul: CE.cm c eq{is_fully_distributive mul add /\ is_absorber add.unit mul}) 
                                    (mx my: matrix c m n) (mz: matrix c n p)
  : Lemma (matrix_mul add mul (matrix_add add mx my) mz `(matrix_equiv eq m p).eq`
           matrix_add add (matrix_mul add mul mx mz) (matrix_mul add mul my mz))
