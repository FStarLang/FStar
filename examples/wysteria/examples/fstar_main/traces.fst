(*--build-config
    options:--admit_fsi FStar.Seq --admit_fsi FStar.Matrix2 --z3timeout 10;
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


let full a b = full_matrix a b (Matrix2.create (Seq.length a) (Seq.length b) false) 0 0 

val full_is_correct: a:Seq.seq int -> b:Seq.seq int -> i:ix a -> j:ix b -> Lemma
  (requires True)
  (ensures (index (full a b) i j = (Seq.index a i = Seq.index b j)))
  [SMTPat (index (full a b) i j)]
let full_is_correct a b i j = 
  let init = Matrix2.create (Seq.length a) (Seq.length b) false in
  lemma_full_matrix_aux a b init 0 0 i j   


let elim (#m:nat) (#n:nat) (p:mat m n nat) (i:ri m) (j:cj n) = 
  let out = Matrix2.upd p i j 1 in
  let out = update_row_suffix out i j 2 in 
  update_col_suffix out i j 2

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
  else if Seq.index a i = Seq.index b j
       then fast_product a b (elim out i j) i (j + 1)
       else fast_product a b out i (j + 1)

let precedes (i, j) (i', j') = (i < i') || (i = i' && j < j')

opaque type eq_until (#m:nat) (#n:nat) (i:nat{i <= m}) (j:nat{j<=n}) (p:mat m n nat) (q:mat m n nat) = 
  forall (i':ri m) (j':cj n).{:pattern (index p i' j') \/ (index q i' j')}  
           precedes (i',j') (i,j)  ==>  index p i' j' = index q i' j'

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

val aux_elim_is_correct:  a:Seq.seq int -> b:Seq.seq int -> p:prod a b nat -> i:ix a -> j:ix b -> Lemma
  (requires (prefix_correct a b i j p 
            /\ zero_or_two_from i j p
            /\ (Seq.index a i = Seq.index b j)))
  (ensures (let out = elim p i j in
            prefix_correct a b i (j + 1) out
            /\ zero_or_two_from i (j + 1) out))
let aux_elim_is_correct a b p i j = cut (witness i /\ witness j)
 
val fast_product_correct: a:Seq.seq int -> b:Seq.seq int -> p:prod a b nat 
                      -> i:nat{i <= Seq.length a} -> j:nat{j <= Seq.length b} -> Lemma
  (requires (prefix_correct a b i j p /\ zero_or_two_from i j p)) 
  (ensures (prefix_correct a b (Seq.length a) (Seq.length b) (fast_product a b p i j)))
  (decreases %[(Seq.length a - i); (Seq.length b - j)])
let rec fast_product_correct a b p i j = 
  if i = Seq.length a then ()
  else if j = Seq.length b then fast_product_correct a b p (i + 1) 0
  else if index p i j = 2 then fast_product_correct a b p i (j + 1)
  else if Seq.index a i = Seq.index b j
       then (aux_elim_is_correct a b p i j;
             fast_product_correct a b (elim p i j) i (j + 1))
       else fast_product_correct a b p i (j + 1)

val make_sparse: #m:nat -> #n:nat -> mat m n bool -> mat m n nat
	       -> i:nat{i <= m} -> j:nat{j <= n} -> Tot (mat m n nat)
  (decreases %[(m - i); (n - j)])
let rec make_sparse #m #n bs out i j = 
  if i = m      then out
  else if j = n then make_sparse bs out (i + 1) 0
  else if index out i j = 2 then make_sparse bs out i (j + 1)
  else if index bs i j 
  then make_sparse bs (elim out i j) i (j + 1)
  else make_sparse bs out i (j + 1)

val fast_is_sparse_full: a:Seq.seq int -> b:Seq.seq int -> p:prod a b nat -> q:prod a b nat 
                      -> i:nat{i <= Seq.length a} -> j:nat{j <= Seq.length b} -> Lemma
  (requires (Matrix2.Eq p q
            /\ prefix_correct a b i j p
            /\ zero_or_two_from i j p))
  (ensures (Matrix2.Eq (fast_product a b p i j)
                      (make_sparse (full a b) q i j)))
  (decreases %[(Seq.length a - i); (Seq.length b - j)])                     
let rec fast_is_sparse_full a b p q i j = 
  if i = Seq.length a then ()
  else if j = Seq.length b then fast_is_sparse_full a b p q (i + 1) 0
  else if index p i j = 2 then fast_is_sparse_full a b p q i (j + 1)
  else if index (full a b) i j 
  then (aux_elim_is_correct a b p i j;
        fast_is_sparse_full a b (elim p i j) (elim q i j) i (j + 1))
  else fast_is_sparse_full a b p q i (j + 1)
       
type sparse (a:Seq.seq int) (b:Seq.seq int) = 
  p:prod a b nat{prefix_correct a b (Seq.length a) (Seq.length b) p}
   
val sparse_as_list: a:Seq.seq int -> b:Seq.seq int -> p:sparse a b 
                 -> i:nat{i<=Seq.length a} 
                 -> j:nat{j<=Seq.length b}
                 -> Tot (list bool)
  (decreases %[(Seq.length a - i); (Seq.length b - j)])
let rec sparse_as_list a b p i j = 
  if i=Seq.length a then []
  else if j=Seq.length b then sparse_as_list a b p (i + 1) 0
  else if index p i j = 0 then false :: sparse_as_list a b p i (j + 1)
  else if index p i j = 1 then true :: sparse_as_list a b p i (j + 1)
  else (assert (index p i j = 2);
        sparse_as_list a b p i (j + 1))

let remove (s:Seq.seq int) (i:ix s) = 
  Seq.append (Seq.slice s 0 i) (Seq.slice s (i + 1) (Seq.length s))

type bound (#a:Type) (s:Seq.seq a) = i:nat{i <= Seq.length s}

val elim_bob: s:Seq.seq (int * bool) -> i:bound s -> Tot (s':Seq.seq (int * bool){Seq.length s = Seq.length s'})
  (decreases (Seq.length s - i))
let rec elim_bob s i = 
  if i = Seq.length s 
  then s 
  else let x, _ = Seq.index s i in 
       let s = Seq.upd s i (x, false) in 
       elim_bob s (i + 1)

val lemma_elim_bob : s:Seq.seq (int * bool) -> i:bound s -> j:ix s -> Lemma
  (requires True)
  (ensures ( (j < i ==> Seq.index (elim_bob s i) j = Seq.index s j)
           /\ (i <= j ==> Seq.index (elim_bob s i) j = (fst (Seq.index s j), false)))) 
  (decreases (Seq.length s - i))
  [SMTPat (Seq.index (elim_bob s i) j)]
let rec lemma_elim_bob s i j = 
  if i = Seq.length s 
  then ()
  else let s' = Seq.upd s i (fst (Seq.index s i), false) in 
       lemma_elim_bob s' (i + 1) j

val check_bob : int -> sb:Seq.seq (int * bool) -> i:nat{i<=Seq.length sb} -> Tot (Seq.seq (int * bool) * bool)
 (decreases (Seq.length sb - i))
let rec check_bob a sb i = 
  if i = Seq.length sb 
  then sb, false
  else let b, elim = Seq.index sb i in 
       if elim then check_bob a sb (i + 1)
       else if a = b 
       then elim_bob sb i, true
       else check_bob a sb (i + 1)

val for_alice : sa:Seq.seq int -> sb:Seq.seq (int * bool) -> i:nat{i<=Seq.length sa} -> Tot (list bool)
 (decreases (Seq.length sa - i))
let rec for_alice sa sb i =
  if i = Seq.length sa 
  then []
  else let a = Seq.index sa i in 
       let sb, r = check_bob a sb 0 in 
       r::for_alice sa sb (i + 1)

val fst_bob_aux : s:Seq.seq (int * bool) 
             -> out:Seq.seq int{Seq.length out = Seq.length s}
             -> i:bound s
             -> Tot (t:Seq.seq int{Seq.length t = Seq.length s})
  (decreases (Seq.length s - i))
let rec fst_bob_aux s out i = 
  if i = Seq.length s then out
  else let out = Seq.upd out i (fst (Seq.index s i)) in
       fst_bob_aux s out (i + 1)

val lemma_fst_bob_aux: s:Seq.seq (int * bool) 
              -> out: Seq.seq int{Seq.length s = Seq.length out}
              -> i:bound s -> Lemma
  (requires (forall (j:nat{j < i}). Seq.index out j = fst (Seq.index s j)))
  (ensures (forall (j:ix out). Seq.index (fst_bob_aux s out i) j = fst (Seq.index s j)))
  (decreases (Seq.length s - i))
let rec lemma_fst_bob_aux s out i = 
  if i = Seq.length s then ()
  else let out = Seq.upd out i (fst (Seq.index s i)) in
       lemma_fst_bob_aux s out (i + 1)

let fst_bob s = fst_bob_aux s (Seq.create (Seq.length s) 0) 0
val lemma_fst_bob: s:Seq.seq (int * bool) -> j:ix s -> Lemma
  (requires True)
  (ensures (Seq.index (fst_bob s) j = fst (Seq.index s j)))
  [SMTPat (Seq.index (fst_bob s) j)]
let lemma_fst_bob s j = lemma_fst_bob_aux s (Seq.create (Seq.length s) 0) 0



val lemma_bob: sa:Seq.seq int
            -> sb:Seq.seq (int * bool) 
            -> ia:ix sa
            -> jb:bound sb 
            -> 

val lemma_alice: a:Seq.seq int -> b:Seq.seq int -> p:prod a b 
             -> 
let fast_prod

//main lemma
// for_alice oa ob sa sb 0  
// = sparse_as_list (fast_product oa ob (Matrix2.create _ _ 0) 0 0)

val for_alice : list int -> list int -> Tot (list bool)
val check_bob : int -> l:list int -> Tot (list int * bool)
let rec for_alice la lb = match la with 
  | [] -> []
  | a::rest -> 
    let lb, r = check_bob a lb in 
    r::for_alice rest lb
    
and check_bob a lb = match lb with 
  | [] -> [], false
  | b::rest -> 
    if a = b 
    then rest, true
    else let rest, r = check_bob a rest in 
         b::rest, r
