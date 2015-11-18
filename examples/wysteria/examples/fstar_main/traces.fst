(*--build-config
    options:--admit_fsi FStar.Seq --admit_fsi FStar.Set;
    other-files:classical.fst set.fsi seq.fsi seqproperties.fst
  --*)
module Traces
open FStar.Seq
 
type vec (n:nat) (a:Type) = s:seq a{length s = n}
type matrix (m:nat) (n:nat) (a:Type) = vec m (vec n a) 
type bmat m n = matrix m n bool

val lookup : #m:_ -> #n:_ -> x:matrix m n 'a -> (i:nat{i < m}) -> (j:nat{j < n}) -> Tot 'a
let lookup (#a:Type) (#m:nat) (#n:nat) (x:matrix m n a) (i:nat{i < m}) (j:nat{j < n}) =
    Seq.index (Seq.index x i) j

val update : #a:Type -> #m:nat -> #n:nat -> =x:matrix m n a -> i:nat{i < m} -> j:nat{j < n} -> v:a -> Tot (matrix m n a)
let update (#a:Type) #m #n x i j v = Seq.upd x i (Seq.upd (Seq.index x i) j v)

let test (#m:nat) (#n:nat) (x:matrix m n bool) (i:nat{i<m}) (j:nat{j<n}) =
  assert (lookup #bool #m #n (update #bool #m #n x i j false) i j = false)

val update_row: #a:Type -> #m:nat -> #n:nat -> x:matrix m n a -> i:nat{i < m} -> j:nat{j < n} -> v:a -> Tot (matrix m n a)
let update_row (#a:Type) (#m:nat) (#n:nat) x i j v = 
  let row_i = Seq.index x i in
  Seq.upd x i (Seq.append (Seq.slice row_i 0 (j + 1)) (Seq.slice row_i (j + 1) n))

val update_col: #a:Type -> #m:nat -> #n:nat -> =x:matrix m n a -> i:nat{i < m} -> j:nat{j < n} -> v:a -> Tot (matrix m n a)
  (decreases (m - i))
let rec update_col (#a:Type) #m #n x i j v =
    if i + 1 = m then x
    else let x = update #a #m #n x (i + 1) j v in
         update_col #a #m #n x (i + 1) j v

val lemma_update_col: #a:Type -> #m:nat -> #n:nat -> =x:matrix m n a -> i:nat{i < m} -> j:nat{j < n} -> v:a -> i':nat{i' < m} -> j':nat{j' < n} -> 
  Lemma
  (requires (True))
  (ensures ( (j' <> j \/ i' <= i) ==> lookup #a #m #n (update_col #a #m #n x i j v) i' j' = lookup #a #m #n x i' j'
  	   /\ (j' = j /\ i' > i) ==> lookup #a #m #n (update_col #a #m #n x i j v) i' j' = v))
  (decreases (m - i))
  [SMTPat (lookup #a #m #n (update_col #a #m #n x i j v) i' j')]
let rec lemma_update_col (#a:Type) #m #n x i j v i' j' = 
    if i + 1 = m 
    then ()
    else lemma_update_col #a #m #n x (i + 1) j v i' j'

val make_sparse: #m:nat -> #n:nat -> matrix m n bool -> matrix m n nat
	       -> i:nat{i <= m} -> j:nat{j <= n} -> Tot (matrix m n nat)
  (decreases %[(m - i); (n - j)])
let rec make_sparse #m #n bs out i j = 
  if i = m      then out
  else if j = n then make_sparse #m #n bs out (i + 1) 0
  else if lookup #bool #m #n bs i j
  then let out = update #nat #m #n out i j 1 in 
       let out = update_row #nat #m #n out i j 2 in
       let out = update_col #nat #m #n out i j 2 in
       make_sparse #m #n bs out i (j + 1)
  else let out = update #nat #m #n out i j 0 in 
       make_sparse #m #n bs out i (j + 1)

val new_matrix : m:nat -> n:nat -> v:'a -> Tot (matrix m n 'a)
let new_matrix m n v = Seq.create m (Seq.create n v)
 
val full_matrix : #m:nat
		 -> #n:nat 
		 -> a:vec m int 
		 -> b:vec n int 
		 -> out:matrix m n bool
		 -> i:nat{i <= m}
		 -> j:nat{j <= n}
		 -> Tot (matrix m n bool)
  (decreases %[(m - i); (n - j)])
let rec full_matrix m n a b out i j = 
  if i = Seq.length a then out
  else if j = Seq.length b then full_matrix #m #n a b out (i + 1) 0
  else let out = update #bool #m #n out i j (Seq.index a i = Seq.index b j) in
       full_matrix #m #n a b out i (j + 1)

type prod (a:seq int) (b:seq int) = matrix (Seq.length a) (Seq.length b) bool

val lemma_full_matrix : #m:nat -> #n:nat -> a:vec m int -> b:vec n int -> out:matrix m n bool
		      -> i:nat -> j:nat{i <= Seq.length a /\ j <= Seq.length b} 
		      -> i':nat{i' < Seq.length a} -> j':nat{j' < Seq.length b}
		      -> Lemma 
  (requires (True))
  (ensures ((i <= i' /\ j <= j') ==> lookup #bool #m #n (full_matrix #m #n a b out i j) i' j' 
				  = (Seq.index a i = Seq.index b j)
	    /\ (%[i';j'] << %[i;j] ==> lookup #bool #m #n (full_matrix #m #n a b out i j) i' j' 
				    = lookup #bool #m #n out i' j')))
  (decreases %[m - i; n - j])
let rec lemma_full_matrix m n a b out i j i' j' = 
  if      i = Seq.length a then ()
  else if j = Seq.length b then lemma_full_matrix #m #n a b out (i + 1) 0 i' j'
  else begin
       let out = update #bool #m #n out i j false in // (Seq.index a i = Seq.index b j) in
       // assert (lookup #bool #m #n out i j = false); //(Seq.index a i = Seq.index b j)); 
       admit()
  end
       let result = full_matrix a b out i j in 
       lemma_full_matrix a b out i (j + 1) i' j';
       assert (lookup #a #(Seq.length a) #(Seq.length b) result i j = 
  end
	  
  
