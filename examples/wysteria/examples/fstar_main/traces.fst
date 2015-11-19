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


let precedes (i, j) (i', j') = (i < i') || (i = i' && j < j')
type bound (#a:Type) (s:Seq.seq a) = i:nat{i <= Seq.length s}
opaque type witness (#a:Type) (x:a) = True

(* Shape invariant on the matrix 

   0 0 0 0 0 0 0
   0 0 0 1 2 2 2 
   0 0 0 2 0 + 3
   3 3 3 2 3 3 3
   3 3 3 2 3 3 3

   When considering element '+', everythign preceding it is a 0, 1, or 2
   Everything suceeding it is 2 or a 3.
   It gets set to either a 0 or a 1
   
   If it gets set to a 1, the rest of the row and column get set to 2

   There can be at most one 1 in each row or column.

   If (i,j) contains a 2, then (i', j) and (i, j') for, i' >= i and j' >= j are 2
   If (i,j) contains a 2, then there either must be some k <= i such that (k, j) is a 2
				     or  some k <= j such that (i, k) is a 2
 *)

type entry = 
  | NotEqual  //0
  | Equal     //1
  | Elim      //2
  | Unknown   //3

opaque type notequal_ok (#a:Seq.seq int) (#b:Seq.seq int) (p:prod a b entry) =
  forall (i:ix a) (j:ix b).{:pattern index p i j} 
          index p i j = NotEqual
          ==> ((Seq.index a i <> Seq.index b j)
	    /\ ((forall (j':ix b).{:pattern index p i j'} j' < j ==> (index p i j' = NotEqual \/ index p i j' = Elim))
             /\ (forall (i':ix a).{:pattern index p i' j} i' < i ==> (index p i' j = NotEqual \/ index p i' j = Elim))))

opaque type equal_ok (#a:Seq.seq int) (#b:Seq.seq int) (p:prod a b entry) =
  forall (i:ix a) (j:ix b).{:pattern index p i j} 
          index p i j = Equal
          ==> (Seq.index a i = Seq.index b j
	    /\ ((forall (j':ix b).{:pattern index p i j'} (j' < j ==> (index p i j' = NotEqual \/ index p i j' = Elim))
	    					 /\  (j < j' ==> index p i j' = Elim))
             /\ (forall (i':ix a).{:pattern index p i' j} (i' < i ==> (index p i' j = NotEqual \/ index p i' j = Elim))
	    				         /\  (i < i' ==> index p i' j = Elim))))

opaque type witness_row (i:nat) = True
opaque type witness_col (i:nat) = True

opaque type elim_ok (#a:Seq.seq int) (#b:Seq.seq int) (p:prod a b entry)  = 
  forall (i:ix a) (j:ix b). {:pattern (index p i j)}
  index p i j = Elim ==> //if we have an Elim at (i,j), then
           //we have an Equal in a previous column of the same row
          ((exists (c:ix b{c < j}).{:pattern (witness_col c)} witness_col c /\ index p i c = Equal)  
           //or, we have an Equal in a previous row of the same column
         \/ (exists (r:ix a{r < i}).{:pattern (witness_row r)} witness_row r /\ index p r j = Equal))

opaque type unknown_ok (#a:Seq.seq int) (#b:Seq.seq int) (p:prod a b entry) = 
  forall (i:ix a) (j:ix b). {:pattern (index p i j)}
    index p i j = Unknown ==>  //there should be no Equal entries in the same row or col
           ((forall (k:ix b). {:pattern (index p i k)} index p i k <> Equal)
	  /\ (forall (k:ix a). {:pattern (index p k j)} index p k j <> Equal))

opaque type prefix_ok (#a:Seq.seq int) (#b:Seq.seq int) (p:prod a b entry) (i:bound a) (j:bound b) = 
  forall (i':ix a) (j':ix b).{:pattern (index p i' j')}
    (precedes (i',j') (i,j) ==> index p i' j' <> Unknown)
  /\ ((i < Seq.length a /\ j' < j) ==> index p i j' <> Equal)

opaque type suffix_ok (#a:Seq.seq int) (#b:Seq.seq int) (p:prod a b entry) (i:bound a) (j:bound b) = 
   forall (i':ix a) (j':ix b).{:pattern (index p i' j')}  //every element from i,j onwards is elim or unknown
     (precedes (i, j) (i', j') \/ (i,j)=(i',j'))
     ==> ((index p i' j' = Elim \/ index p i' j' = Unknown))

opaque type prod_invariant (#a:Seq.seq int) (#b:Seq.seq int) (p:prod a b entry) (i:bound a) (j:bound b) = 
  notequal_ok p
  /\ equal_ok p
  /\ elim_ok p
  /\ unknown_ok p
  /\ prefix_ok p i j
  /\ suffix_ok p i j

let elim (#m:nat) (#n:nat) (p:mat m n entry) (i:ri m) (j:cj n) = 
  let out = Matrix2.upd p i j Equal in
  let out = update_row_suffix out i j Elim in 
  update_col_suffix out i j Elim

val elim_is_ok:  #a:Seq.seq int -> #b:Seq.seq int -> p:prod a b entry -> i:ix a -> j:ix b -> Lemma
  (requires (prod_invariant p i j
            /\ index p i j = Unknown
            /\ Seq.index a i = Seq.index b j))
  (ensures (prod_invariant (elim p i j) (i + 1) 0))
let elim_is_ok a b p i j = 
  cut (witness_row i);
  cut (witness_col j)

let set_neq (#m:nat) (#n:nat) (p:mat m n entry) (i:ri m) (j:cj n) = 
  Matrix2.upd p i j NotEqual

val set_neq_is_ok:  #a:Seq.seq int -> #b:Seq.seq int -> p:prod a b entry -> i:ix a -> j:ix b -> Lemma
  (requires (prod_invariant p i j
            /\ index p i j = Unknown
            /\ Seq.index a i <> Seq.index b j))
  (ensures (prod_invariant (set_neq p i j) i (j + 1)))
let set_neq_is_ok a b p i j = ()

val fast_product: a:Seq.seq int 
                -> b:Seq.seq int
                -> out:prod a b entry
                -> i:nat{i <= Seq.length a}
                -> j:nat{j <= Seq.length b}
                -> Tot (prod a b entry)
  (decreases %[(Seq.length a - i); (Seq.length b - j)])                
let rec fast_product a b out i j = 
  if i = Seq.length a then out
  else if j = Seq.length b then fast_product a b out (i + 1) 0
  else if index out i j = Elim then fast_product a b out i (j + 1) //skip, we've already eliminated it
  else if Seq.index a i = Seq.index b j 
       then fast_product a b (elim out i j) (i + 1) 0
       else fast_product a b (set_neq out i j) i (j + 1)

val fast_product_correct: a:Seq.seq int -> b:Seq.seq int -> p:prod a b entry
                      -> i:nat{i <= Seq.length a} -> j:nat{j <= Seq.length b} -> Lemma
  (requires (prod_invariant p i j))
  (ensures (prod_invariant (fast_product a b p i j) (Seq.length a) (Seq.length b)))
  (decreases %[(Seq.length a - i); (Seq.length b - j)])
let rec fast_product_correct a b p i j = 
  if i = Seq.length a then ()
  else if j = Seq.length b then fast_product_correct a b p (i + 1) 0
  else if index p i j = Elim then fast_product_correct a b p i (j + 1)
  else if Seq.index a i = Seq.index b j
       then (elim_is_ok p i j;
             fast_product_correct a b (elim p i j) (i + 1) 0)
       else (set_neq_is_ok p i j;
	    fast_product_correct a b (set_neq p i j) i (j + 1))

val make_sparse: #m:nat -> #n:nat -> mat m n bool -> mat m n entry
	       -> i:nat{i <= m} -> j:nat{j <= n} -> Tot (mat m n entry)
  (decreases %[(m - i); (n - j)])
let rec make_sparse #m #n bs out i j = 
  if i = m      then out
  else if j = n then make_sparse bs out (i + 1) 0
  else if index out i j = Elim then make_sparse bs out i (j + 1)
  else if index bs i j 
  then make_sparse bs (elim out i j) (i + 1) 0
  else make_sparse bs (set_neq out i j) i (j + 1)

val fast_is_sparse_full: a:Seq.seq int -> b:Seq.seq int -> p:prod a b entry -> q:prod a b entry
                      -> i:nat{i <= Seq.length a} -> j:nat{j <= Seq.length b} -> Lemma
  (requires (Matrix2.Eq p q
            /\ prod_invariant p i j))
  (ensures (Matrix2.Eq (fast_product a b p i j)
                       (make_sparse (full a b) q i j)))
  (decreases %[(Seq.length a - i); (Seq.length b - j)])                     
let rec fast_is_sparse_full a b p q i j = 
  if i = Seq.length a then ()
  else if j = Seq.length b then fast_is_sparse_full a b p q (i + 1) 0
  else if index p i j = Elim then fast_is_sparse_full a b p q i (j + 1)
  else if index (full a b) i j 
  then (elim_is_ok p i j;
        fast_is_sparse_full a b (elim p i j) (elim q i j) (i + 1) 0)
  else fast_is_sparse_full a b (set_neq p i j) (set_neq q i j) i (j + 1)
       
type sparse (a:Seq.seq int) (b:Seq.seq int) = 
  p:prod a b entry{prod_invariant p (Seq.length a) (Seq.length b)}
   
// val sparse_as_list: a:Seq.seq int -> b:Seq.seq int -> p:sparse a b 
//                  -> i:nat{i<=Seq.length a} 
//                  -> j:nat{j<=Seq.length b}
//                  -> Tot (list bool)
//   (decreases %[(Seq.length a - i); (Seq.length b - j)])
// let rec sparse_as_list a b p i j = 
//   if i=Seq.length a then []
//   else if j=Seq.length b then sparse_as_list a b p (i + 1) 0
//   else if index p i j = 0 then false :: sparse_as_list a b p i (j + 1)
//   else if index p i j = 1 then true :: sparse_as_list a b p i (j + 1)
//   else (assert (index p i j = 2);
//         sparse_as_list a b p i (j + 1))

// let remove (s:Seq.seq int) (i:ix s) = 
//   Seq.append (Seq.slice s 0 i) (Seq.slice s (i + 1) (Seq.length s))


val ith_row_until: #a:Seq.seq int -> #b:Seq.seq int -> p:prod a b entry -> i:ix a -> k:bound b -> j:bound b{j <= k} -> Tot bool
  (decreases (k - j))
let rec ith_row_until #a #b p i k j = 
  if j = k                    then false
  else if index p i j = Equal then true
  else ith_row_until p i k (j + 1)

val lemma_ith_row: #a:Seq.seq int -> #b:Seq.seq int -> p:prod a b entry -> row:ix a -> stop_col:bound b -> cur:bound b{cur <= stop_col} 
    -> w:ix b{cur <= w && w < stop_col} 
    -> Lemma (requires (index p row w = Equal))
	    (ensures (ith_row_until p row stop_col cur = true))
	    (decreases (stop_col - cur))
let rec lemma_ith_row #a #b p row stop_col cur w = 
  if index p row cur <> Equal then lemma_ith_row p row stop_col (cur + 1) w

let ith_row #a #b (p:prod a b entry) i = ith_row_until p i (Seq.length b) 0
type seq 'a = Seq.seq 'a

val proj_fst : #a:seq int -> list (int * ix a) -> Tot (list int)
let rec proj_fst #a l = match l with
  | [] -> []
  | hd::tl -> fst hd :: proj_fst #a tl

val row_as_list: sb:seq int -> r:seq entry{Seq.length r = Seq.length sb} -> i:bound sb -> Tot (list int)
  (decreases (Seq.length sb - i))
let rec row_as_list sb r i = 
  if i = Seq.length sb
  then []
  else if Seq.index r i = Elim
  then row_as_list sb r (i + 1)
  else Seq.index sb i :: row_as_list sb r (i + 1)
 
val lemma_next_row_aux: #a:seq int -> #b:seq int -> i:ix a -> j:ix b  
      -> p:prod a b entry{prod_invariant p i j /\ index p i j = Unknown} 
      -> q:prod a b entry{prod_invariant q (i + 1) 0 /\ Seq.index a i = Seq.index b j}
      -> r:prod a b entry{prod_invariant p i (j + 1)}
      -> Lemma 
  (requires True)
  (ensures (index q i j = Equal 
	    /\ (i + 1 < Seq.length a
	       ==> row_as_list b (Matrix2.row q (i + 1)) j
  		   = Cons.tl (row_as_list b (Matrix2.row p i) j))))
let lemma_next_row_aux #a #b i j p q r = ()

val lemma_next_row: #a:seq int -> #b:seq int -> i:ix a -> j:ix b  
      -> p:prod a b entry{prod_invariant p i j /\ index p i j = Unknown} 
      -> q:prod a b entry{prod_invariant q (i + 1) 0 /\ Seq.index a i = Seq.index b j}
      -> Lemma 
  (requires True)
  (ensures (index q i j = Equal 
	    /\ (i + 1 < Seq.length a
	       ==> row_as_list b (Matrix2.row q (i + 1)) j
  		   = Cons.tl (row_as_list b (Matrix2.row p i) j))))
let lemma_next_row #a #b i j p q  = 
  let r = magic () in //TODO: remove this
  lemma_next_row_aux i j p q r

assume val advance:  sa:Seq.seq int -> sb:Seq.seq int -> i:ix sa -> j:ix sb
	    -> p:prod sa sb entry{prod_invariant p i j}
	    -> q:prod sa sb entry{prod_invariant q (i + 1) 0}
	    -> lb:list int{is_Cons lb}
	    -> Pure (bound sb * prod sa sb entry)
  (requires (lb=row_as_list sb (Matrix2.row p i) j /\ Seq.index sa i <> Seq.index sb j))
  (ensures (fun (r:(bound sb * prod sa sb entry)) -> 
	           fst r > j
	         /\ prod_invariant (snd r) i (fst r)
		 /\ ith_row_until (snd r) i (fst r) 0 = false
		 /\ (fst r < Seq.length sb ==> index (snd r) i (fst r) <> Elim)
		 /\ Cons.tl lb=row_as_list sb (Matrix2.row (snd r) i) (fst r)
		 /\ (i + 1 < Seq.length sa 
		     ==> row_as_list sb (Matrix2.row q (i + 1)) j
		         = Cons.hd lb::row_as_list sb (Matrix2.row q (i + 1)) (fst r))))


val check_bob: a:int -> lb:list int -> Tot (list int * bool)
let rec check_bob a lb =
  match lb with
   | [] -> [], false
   | hd::tl ->
     if hd=a
     then tl, true
     else let tl, r = check_bob a tl in
          hd::tl, r

val lemma_bob: sa:Seq.seq int -> sb:Seq.seq int -> i:ix sa -> j:bound sb 
	       -> p:prod sa sb entry{prod_invariant p i j}
	       -> q:prod sa sb entry{prod_invariant q (i + 1) 0}
	       -> a:int -> lb:list int -> Lemma
  (requires (lb=row_as_list sb (Matrix2.row p i) j
	     /\ a=Seq.index sa i
	     /\ ith_row_until p i j 0 = false
	     /\ ith_row_until q i j 0 = false
	     /\ (j < Seq.length sb ==> index p i j <> Elim)))
  (ensures (let br = check_bob a lb in
	    (i + 1 < Seq.length sa  
	     ==>  fst br = row_as_list sb (Matrix2.row q (i + 1)) j)
          /\ snd br = ith_row q i))
  (decreases lb)
let rec lemma_bob sa sb i j p q a lb = match lb with 
  | [] -> ()
  | hd::tl ->  
    if hd=a
    then (lemma_next_row i j p q; 
	  lemma_ith_row q i (Seq.length sb) 0 j)
    else (let j', p' = advance sa sb i j p q lb in 
	  assume (ith_row_until q i j' 0 = false);
	  lemma_bob sa sb i j' p' q a tl)

 

val for_alice : list int -> list int -> Tot (list bool)
let rec for_alice la lb = match la with 
  | [] -> []
  | a::rest -> 
    let lb, r = check_bob a lb in 
    r::for_alice rest lb
