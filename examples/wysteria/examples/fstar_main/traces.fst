(*--build-config
    options:--admit_fsi FStar.Seq --admit_fsi FStar.Matrix2;
    other-files:seq.fsi matrix2.fsti
  --*)
module Traces
open FStar
open FStar.Matrix2

type mat (m:nat) (n:nat) (a:Type) = matrix2 m n a
type bmat m n = mat m n bool

let test (#m:nat) (#n:nat) (x:mat m n bool) (i:nat{i<m}) (j:nat{j<n}) =
  assert (index (upd x i j false) i j = false)

type ri (m:nat) = i:nat{i<m}
type cj (n:nat) = j:nat{j<n}

val update_row_suffix: #m:nat -> #n:nat -> x:mat m n 'a -> i:ri m -> j:cj n -> v:'a -> Tot (mat m n 'a)
let update_row_suffix #m #n x i j v = 
  let row_i = Matrix2.row x i in
  Matrix2.upd_row x i (Seq.append (Seq.slice row_i 0 (j + 1))
                                  (Seq.create (n - (j + 1)) v))

let test_row_suffix (#m:nat) (#n:nat) (x:mat m n bool) (i:ri m) (j:cj n) (k:nat{j < k /\ k < n}) = 
  assert (index (update_row_suffix x i j false) i k = false)

val update_col_suffix: #m:nat -> #n:nat -> x:mat m n 'a -> i:nat{i < m} -> j:nat{j < n} -> v:'a -> Tot (mat m n 'a)
let update_col_suffix #m #n x i j v = 
  let col_i = Matrix2.col x j in 
  Matrix2.upd_col x j (Seq.append (Seq.slice col_i 0 (i + 1))
                                  (Seq.create (m - (i + 1)) v))

let test_col_suffix (#m:nat) (#n:nat) (x:mat m n bool) (i:ri m) (j:cj n) (k:nat{i < k /\ k < m}) = 
  assert (index (update_col_suffix x i j false) k j = false)

val make_sparse: #m:nat -> #n:nat -> mat m n bool -> mat m n nat
	       -> i:nat{i <= m} -> j:nat{j <= n} -> Tot (mat m n nat)
  (decreases %[(m - i); (n - j)])
let rec make_sparse #m #n bs out i j = 
  if i = m      then out
  else if j = n then make_sparse bs out (i + 1) 0
  else if index bs i j 
  then let out = Matrix2.upd out i j 1 in 
       let out = update_row_suffix out i j 2 in
       let out = update_col_suffix out i j 2 in
       make_sparse bs out i (j + 1)
  else let out = Matrix2.upd out i j 0 in 
       make_sparse bs out i (j + 1)

type prod (a:Seq.seq int) (b:Seq.seq int) (t:Type) = mat (Seq.length a) (Seq.length b) t

val full_matrix :   a:Seq.seq int
		 -> b:Seq.seq int 
		 -> out:prod a b bool
		 -> i:nat{i <= Seq.length a}
		 -> j:nat{j <= Seq.length b}
		 -> Tot (prod a b bool)
  (decreases %[(Seq.length a - i); (Seq.length b - j)])
let rec full_matrix a b out i j = 
  if i = Seq.length a then out
  else if j = Seq.length b then full_matrix a b out (i + 1) 0
  else let out = Matrix2.upd out i j (Seq.index a i = Seq.index b j) in
       full_matrix a b out i (j + 1)

type ix (#a:Type) (x:Seq.seq a) = i:nat{i < Seq.length x}

val lemma_full_matrix_aux : a:Seq.seq int -> b:Seq.seq int -> out:prod a b bool
		      -> i:nat{i <= Seq.length a} -> j:nat{j <= Seq.length b}
                      -> (i':ix a) -> (j':ix b)
		      -> Lemma 
  (requires (True))
  (ensures (if (i' < i \/ (i'=i /\ j' < j))
            then index (full_matrix a b out i j) i' j' 
                 = index out i' j'
             else index (full_matrix a b out i j) i' j' 
                 = (Seq.index a i' = Seq.index b j')))
  (decreases %[Seq.length a - i; Seq.length b - j])
let rec lemma_full_matrix_aux a b out i j i' j'  = 
  if      i = Seq.length a then ()
  else if j = Seq.length b then lemma_full_matrix_aux a b out (i+1) 0 i' j'
  else begin
       let out = Matrix2.upd out i j (Seq.index a i = Seq.index b j) in
       lemma_full_matrix_aux a b out i (j + 1) i' j'
  end


val lemma_full_matrix: a:Seq.seq int -> b:Seq.seq int -> out:prod a b bool -> i:ix a -> j:ix b -> Lemma
  (requires True)
  (ensures (index (full_matrix a b out 0 0) i j = (Seq.index a i = Seq.index b j)))
  [SMTPat (index (full_matrix a b out 0 0) i j)]
let lemma_full_matrix a b out i j = lemma_full_matrix_aux a b out 0 0 i j   

val fast_product:  a:Seq.seq int 
                -> b:Seq.seq int
                -> out:prod a b nat  
                -> i:nat{i <= Seq.length a}
                -> j:nat{j <= Seq.length b}
                -> Tot (prod a b nat)
  (decreases %[(Seq.length a - i); (Seq.length b - j)])                
let rec fast_product a b out i j = 
  if i = Seq.length a then out
  else if j = Seq.length b then fast_product a b out (i + 1) 0
  else if index out i j = 2 then fast_product a b out i (j + 1) //skip, we've already eliminated it
  else let cmp = (Seq.index a i = Seq.index b j) in 
       if cmp
       then let out = Matrix2.upd out i j 1 in
            let out = update_row_suffix out i j 2 in 
            let out = update_col_suffix out i j 2 in
            fast_product a b out i (j + 1)
       else fast_product a b out i (j + 1)

let full a b = full_matrix a b (Matrix2.create (Seq.length a) (Seq.length b) false) 0 0 

let precedes (i, j) (i', j') = (i < i') || (i = i' && j < j')

opaque type eq_until (#m:nat) (#n:nat) (i:nat{i <= m}) (j:nat{j<=n}) (p:mat m n nat) (q:mat m n nat) = 
  forall (i':ri m) (j':cj n).{:pattern (index p i' j') \/ (index q i' j')}  
           precedes (i',j') (i,j)  ==>  index p i' j' = index q i' j'
           
           (* ((i' < i) \/ (i' = i /\ j' < j)) ==>  index p i' j' = index q i' j' *)

opaque type witness (#a:Type) (x:a) = True

opaque type two_is_ok (#m:nat) (#n:nat) (p:mat m n nat) (i:ri m) (j:cj n) = 
  index p i j = 2 ==> //if we have a 2 somewhere, then
           //we have a 1 in a previous column of the same row
          ((exists (c:cj n{c <= j}).{:pattern (witness c)} witness c /\ index p i c = 1)  
           //or, we have a 1 in a previous row of the same column
         \/ (exists (r:ri m{r <= i}).{:pattern (witness r)} witness r /\ index p r j = 1)) 
 
opaque type zero_or_two_from (#m:nat) (#n:nat) (i:nat{i <= m}) (j:nat{j <= n}) (p:mat m n nat) = 
   forall (i':ri m) (j':cj n).{:pattern (index p i' j')} 
     (precedes (i, j) (i', j') \/ (i,j)=(i',j'))
     ==> ((index p i' j' = 0 \/ index p i' j' = 2) //every element from i,j onwards is 0 or 2
         /\ two_is_ok p i' j')
        
opaque type prefix_correct (a:Seq.seq int) (b:Seq.seq int) (i:nat{i <= Seq.length a}) (j:nat{j <= Seq.length b}) (p:prod a b nat) = 
  forall (i':ix a) (j':ix b).{:pattern (index p i' j')}
    precedes (i',j') (i,j) ==>
    (* %[i';j'] << %[i;j] ==>  *)
         (if index p i' j' = 0
          then Seq.index a i' <> Seq.index b j'
          else if index p i' j' = 1
          then Seq.index a i' = Seq.index b j'
          else (index p i' j' = 2 /\ two_is_ok p i' j'))

opaque type zero_or_two_from_weak (#m:nat) (#n:nat) (i:nat{i <= m}) (j:nat{j <= n}) (p:mat m n nat) = 
   forall (i':ri m) (j':cj n).{:pattern (index p i' j')} 
     (precedes (i, j) (i', j') \/ (i,j)=(i',j'))
     ==> ((index p i' j' = 0 \/ index p i' j' = 2)) //every element from i,j onwards is 0 or 2
         (* /\ two_is_ok p i' j') *)

val fast_product_correct: a:Seq.seq int -> b:Seq.seq int -> p:prod a b nat 
                      -> i:nat{i <= Seq.length a} -> j:nat{j <= Seq.length b} -> Lemma
  (requires (prefix_correct a b i j p /\ zero_or_two_from i j p)) 
  (ensures (prefix_correct a b (Seq.length a) (Seq.length b) (fast_product a b p i j)))
  (decreases %[(Seq.length a - i); (Seq.length b - j)])
let rec fast_product_correct a b p i j = 
  if i = Seq.length a then ()
  else if j = Seq.length b then fast_product_correct a b p (i + 1) 0
  else if index p i j = 2 then fast_product_correct a b p i (j + 1)
  else let cmp = (Seq.index a i = Seq.index b j) in 
       if cmp
       then let out = Matrix2.upd p i j 1 in
            let out = update_row_suffix out i j 2 in 
            let out = update_col_suffix out i j 2 in
            assert (prefix_correct a b i (j + 1) out);
            assert (zero_or_two_from_weak i (j + 1) out);
            cut (witness i);
            cut (witness j);
            assert (zero_or_two_from i (j + 1) out);
            fast_product_correct a b out i (j + 1)
       else (assert (index p i j = 0);
             fast_product_correct a b p i (j + 1))
  
val fast_is_sparse_full: a:Seq.seq int -> b:Seq.seq int -> p:prod a b nat -> q:prod a b nat 
                      -> i:nat{i <= Seq.length a} -> j:nat{j <= Seq.length b} -> Lemma
  (requires (eq_until i j p q /\ zero_or_two_from i j p))
  (ensures (fast_product a b p i j
            = make_sparse (full a b) q i j))
let rec fast_is_sparse_full a b p q i j = 
  if i = Seq.length a 
  then begin
    cut (Matrix2.Eq p q)
  end
  else admit()

