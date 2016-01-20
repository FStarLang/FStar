(*--build-config
    options:--admit_fsi FStar.Seq --admit_fsi FStar.Matrix2 --z3timeout 10;
    other-files:seq.fsi FStar.Matrix2.fsti
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
   0 0 0 1 3 3 3 
   0 0 0 2 1 3 3
   0 0 1 2 2 3 3
   0 + 2 2 2 3 3

   When considering element '+', everything preceding it is a 0, 1, 2, or 3
   Everything suceeding it is 2 or 3 

   It gets set to either a 0 or a 1
   
   If it gets set to a 1, the rest of the row and column get set to 2

   There can be at most one 1 in each row or column.

   If (i,j) contains a 2, then the rest of the column contains a 2
		          and a preceding row in the same column contains a 1

   If (i,j) contains a 3, then the rest of the row contains a 3
		          and a preceding row in the same column contains a 1

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
   	  //we have an Equal in a previous row of the same column
	    ((exists (r:ix a{r < i}).{:pattern (witness_row r)} witness_row r /\ index p r j = Equal)
          //or, we have an Equal in a previous column of the same row
	   \/ (exists (c:ix b{c < j}).{:pattern (witness_col c)} witness_col c /\ index p i c = Equal))

opaque type unknown_ok (#a:Seq.seq int) (#b:Seq.seq int) (p:prod a b entry) = 
  forall (i:ix a) (j:ix b). {:pattern (index p i j)}
    index p i j = Unknown ==>  //there should be no Equal entries in the same row or col
           ((forall (k:ix b). {:pattern (index p i k)} index p i k <> Equal)
	  /\ (forall (k:ix a). {:pattern (index p k j)} index p k j <> Equal))

opaque type prefix_ok (#a:Seq.seq int) (#b:Seq.seq int) (p:prod a b entry) (i:bound a) (j:bound b) = 
  forall (i':ix a) (j':ix b).{:pattern (index p i' j')}
    (precedes (i',j') (i,j) ==> index p i' j' <> Unknown)
  /\ ((i < Seq.length a /\ j < Seq.length b /\ j' < j /\ index p i j' = Equal)
     ==> (index p i j = Elim))

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

type seq 'a = Seq.seq 'a

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

val elim_is_ok2:  #a:Seq.seq int -> #b:Seq.seq int -> p:prod a b entry -> i:ix a -> j:ix b -> Lemma
  (requires (prod_invariant p i j
            /\ index p i j = Unknown
            /\ Seq.index a i = Seq.index b j))
  (ensures (prod_invariant (elim p i j) i (j + 1)))
let elim_is_ok2 a b p i j = 
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

val prod_until: #a:Seq.seq int 
                -> #b:Seq.seq int
                -> out:prod a b entry
		-> r:bound a 
		-> c:bound b
                -> i:bound a
                -> j:bound b{precedes (i,j) (r,c) || (i,j)=(r,c)}
                -> Tot (prod a b entry)
  (decreases %[(Seq.length a - i); (Seq.length b - j)])                
let rec prod_until a b out r c i j = 
  if (i,j) = (r,c) || i = Seq.length a then out
  else if j = Seq.length b then prod_until out r c (i + 1) 0
  else if index out i j = Elim then prod_until out r c i (j + 1) //skip, we've already eliminated it
  else if Seq.index a i = Seq.index b j 
       then prod_until (elim out i j) r c i (j + 1) //keep moving along this row, even though it is eliminated, so that we stop at r, c
       else prod_until (set_neq out i j) r c i (j + 1)

let init a b = Matrix2.create (Seq.length a) (Seq.length b) Unknown
let init_ok a b = assert (prod_invariant (init a b) 0 0)

let prec_eq (i, j) (i', j') = precedes (i, j) (i', j') || (i,j) = (i',j')

val prod_until_invariant: a:Seq.seq int -> b:Seq.seq int -> p:prod a b entry 
	      -> r:bound a -> c:bound b -> i:bound a -> j:bound b{prec_eq (i,j) (r,c)}
	      -> Lemma
  (requires (prod_invariant p i j))
  (ensures (prod_invariant (prod_until p r c i j) r c))
  (decreases %[(Seq.length a - i); (Seq.length b - j)])
let rec prod_until_invariant a b p r c i j = 
  if (i,j) = (r,c) || i = Seq.length a then ()
  else if j = Seq.length b then prod_until_invariant a b p r c (i + 1) 0
  else if index p i j = Elim then prod_until_invariant a b p r c i (j + 1)
  else if Seq.index a i = Seq.index b j
       then (elim_is_ok2 p i j;
             prod_until_invariant a b (elim p i j) r c i (j + 1))
       else (set_neq_is_ok p i j;
	     prod_until_invariant a b (set_neq p i j) r c i (j + 1))
 
val iter_i_j: a:seq int -> b:seq int -> i:bound a -> j:bound b -> Tot (p:prod a b entry{prod_invariant p i j}) 
let iter_i_j a b i j = 
    let x = prod_until (init a b) i j 0 0 in
    prod_until_invariant a b (init a b) i j 0 0;
    x

type iter a b i j = p:prod a b entry {p = iter_i_j a b i j}

type sparse (a:Seq.seq int) (b:Seq.seq int) = 
  p:prod a b entry{prod_invariant p (Seq.length a) (Seq.length b)}

let sparse_product a b = iter_i_j a b (Seq.length a) (Seq.length b)

val prod_until_frame: #a:_ -> #b:_ -> p:prod a b entry 
		      -> r:bound a -> c:bound b -> i:bound a -> j:bound b{prec_eq (i,j) (r,c)}
		      -> i':ix a -> j':ix b{precedes (i',j') (i, j)}
		      -> Lemma
  (requires True) 
  (ensures (index p i' j' = index (prod_until p r c i j) i' j'))
  (decreases %[Seq.length a - i; Seq.length b - j])
let rec prod_until_frame #a #b p r c i j i' j' = 
  if (i,j) = (r,c) || i=Seq.length a then ()
  else if j = Seq.length b   then prod_until_frame p r c (i + 1) 0 i' j'
  else if index p i j = Elim then prod_until_frame p r c i (j + 1) i' j'
  else if Seq.index a i = Seq.index b j 
  then let q = elim p i j in 
       prod_until_frame q r c i (j + 1) i' j'
  else let q = set_neq p i j in 
       prod_until_frame q r c i (j + 1) i' j'

val prod_until_extends: #a:_ -> #b:_ -> p:prod a b entry 
			-> r:bound a -> c:bound b 
			-> r':bound a -> c':bound b{prec_eq (r',c') (r,c)}
			-> i:bound a -> j:bound b{prec_eq (i,j) (r',c')}
			-> Lemma
  (requires True)
  (ensures (prod_until p r c i j
	    = prod_until (prod_until p r' c' i j) r c r' c'))
  (decreases %[Seq.length a - i; Seq.length b - j])
//Case Elim:
// prod_until p r c i j
// = prod_until p r c i (j + 1)                                                (case analysis)
// = prod_until (prod_until p r' c' i (j + 1)) r c r' c              '         (IH)
// = prod_until (prod_until p r' c' i j) r c r' c'                             (case analysis)

//Case NotEqual
// prod_until p r c i j
// = prod_until (set_neq p i j) r c i (j + 1)                                  (case analysis)
// = prod_until (prod_until (set_neq p i j) r' c' i (j + 1)) r c r' c'         (IH)
// = prod_until (prod_until p r' c' i j) r c r' c'                             (case analysis)

//Case Equal
// prod_until p r c i j
// = prod_until (elim p i j) r c i (j + 1)                                     (case analysis)
// = prod_until (prod_until (elim p i j) r' c' i (j + 1)) r c r' c'            (IH)
// = prod_until (prod_until p r' c' i j) r c r' c'                             (case analysis)
let rec prod_until_extends #a #b p r c r' c' i j = 
  if (i,j) = (r, c) 
  || (i,j) = (r',c')
  || i = Seq.length a 
  then ()
  else if j = Seq.length b 
  then prod_until_extends p r c r' c' (i+1) 0
  else if index p i j = Elim 
  then prod_until_extends p r c r' c' i (j + 1)
  else if Seq.index a i = Seq.index b j 
  then let q = elim p i j in
       prod_until_extends q r c r' c' i (j + 1)
  else let q = set_neq p i j in
       prod_until_extends q r c r' c' i (j + 1)

val lemma_iters_agree: #a:_ -> #b:_ -> i:bound a -> j:bound b -> i':bound a -> j':bound b{prec_eq (i,j) (i',j')}
		     -> x:ix a -> y:ix b{precedes (x,y) (i,j)}
		     -> Lemma
  (requires True)
  (ensures (index (iter_i_j a b i j) x y = index (iter_i_j a b i' j') x y))
let lemma_iters_agree #a #b i j i' j' x y = 
  prod_until_extends (init a b) i' j' i j 0 0;
  prod_until_frame (iter_i_j a b i j) i' j' i j x y

val make_sparse: #m:nat -> #n:nat -> mat m n bool -> mat m n entry
	       -> i:nat{i <= m} -> j:nat{j <= n} -> Tot (mat m n entry)
  (decreases %[(m - i); (n - j)])
let rec make_sparse #m #n bs out i j = 
  if i = m      then out
  else if j = n then make_sparse bs out (i + 1) 0
  else if index out i j = Elim then make_sparse bs out i (j + 1)
  else if index bs i j 
  then make_sparse bs (elim out i j) i (j + 1)
  else make_sparse bs (set_neq out i j) i (j + 1)

val fast_is_sparse_full: a:Seq.seq int -> b:Seq.seq int -> p:prod a b entry -> q:prod a b entry
                      -> i:bound a -> j:bound b -> Lemma
  (requires (Matrix2.Eq p q
            /\ prod_invariant p i j))
  (ensures (Matrix2.Eq (prod_until p (Seq.length a) (Seq.length b) i j)
                       (make_sparse (full a b) q i j)))
  (decreases %[(Seq.length a - i); (Seq.length b - j)])                     
let rec fast_is_sparse_full a b p q i j = 
  if i = Seq.length a then ()
  else if j = Seq.length b then fast_is_sparse_full a b p q (i + 1) 0
  else if index p i j = Elim then fast_is_sparse_full a b p q i (j + 1)
  else if index (full a b) i j 
  then (elim_is_ok2 p i j;
        fast_is_sparse_full a b (elim p i j) (elim q i j) i (j + 1))
  else fast_is_sparse_full a b (set_neq p i j) (set_neq q i j) i (j + 1)
       

val ith_row_from: #a:Seq.seq int -> #b:Seq.seq int -> p:prod a b entry -> i:ix a -> from:bound b -> Tot (list bool)
  (decreases (Seq.length b - from))
let rec ith_row_from #a #b p i from = 
    if from=Seq.length b then []
    else if index p i from=Equal then [true]
    else if index p i from=NotEqual then false::ith_row_from p i (from + 1)
    else ith_row_from p i (from + 1)

let ith_row #a #b (p:prod a b entry) i = ith_row_from p i 0

val row_as_list_from_to: sb:seq int -> r:seq entry{Seq.length r = Seq.length sb} -> i:bound sb -> j:bound sb{i <= j} -> Tot (list int)
  (decreases (Seq.length sb - i))
let rec row_as_list_from_to sb r i j = 
  if i = j
  then []
  else if Seq.index r i = Elim
  then row_as_list_from_to sb r (i + 1) j
  else Seq.index sb i :: row_as_list_from_to sb r (i + 1) j
 
val row_as_list: sb:seq int -> r:seq entry{Seq.length r = Seq.length sb} -> i:bound sb -> Tot (list int)
let row_as_list sb r i = row_as_list_from_to sb r i (Seq.length sb)

val row_as_list_eq: sb:seq int 
		  -> r1:seq entry{Seq.length r1 = Seq.length sb}
		  -> r2:seq entry{Seq.length r2 = Seq.length sb}
		  -> i:bound sb
		  -> j:bound sb{i <= j /\ (forall (x:ix sb). i <= x /\ x < j ==> Seq.index r1 x = Seq.index r2 x)}
		  -> Lemma (row_as_list_from_to sb r1 i j  = row_as_list_from_to sb r2 i j)
   (decreases (Seq.length sb - i))
let rec row_as_list_eq sb r1 r2 i j  =
    if i = j
    then ()
    else row_as_list_eq sb r1 r2 (i + 1) j
 
val iter_extends: a:_ -> b:_ 
		-> i':bound a -> j':bound b
		-> i:bound a -> j:bound b {prec_eq (i',j') (i,j)}
		-> Lemma
  (requires True)
  (ensures (iter_i_j a b i j
	    = prod_until (iter_i_j a b i' j') i j i' j'))
let iter_extends #a #b i' j' i j = 
  prod_until_extends (init a b) i j i' j' 0 0

 
val frame_iter: a:_ -> b:_ -> i:bound a -> j:bound b -> i':bound a -> j':bound b{prec_eq (i,j) (i',j')}
		-> x:ix a -> y:ix b{precedes (x, y) (i, j)}
  	        -> Lemma
  (requires True) 
  (ensures (index (iter_i_j a b i j) x y = index (iter_i_j a b i' j') x y))
  [SMTPat (index (iter_i_j a b i j) x y);
   SMTPat (index (iter_i_j a b i' j') x y)]
let frame_iter a b i j i' j' x y = lemma_iters_agree #a #b i j i' j' x y
 
val iter_step: a:seq int ->  b:seq int -> i:ix a -> j:ix b -> i':bound a -> j':bound b{precedes (i, j) (i', j')}
      -> p:iter a b i j{index p i j = Unknown}
      -> q:iter a b i' j'
      -> Lemma 
  (requires True)
  (ensures ((Seq.index a i = Seq.index b j ==> index q i j = Equal)
          /\ (Seq.index a i <> Seq.index b j ==> index q i j = NotEqual)))
let iter_step a b i j i' j' p q = 
  let r = iter_i_j a b i (j + 1) in 
  iter_extends #a #b i j i (j + 1);
  cut (index r i j == index r i j)//for the pattern to fire
 
val next_row_wraparound: #a:seq int -> #b:seq int -> i:ix a -> 
  Lemma (ensures (iter_i_j a b i (Seq.length b) 
		  = iter_i_j a b (i + 1) 0))
let next_row_wraparound a b i = iter_extends a b i (Seq.length b) (i + 1) 0

val lemma_next_row_unchanged: #a:seq int -> #b:seq int -> i:ix a{i+1 < Seq.length a} -> j:ix b -> k:bound b 
  -> p:iter a b i j
  -> q:iter a b i k
  -> Lemma (requires (index p i j = Unknown /\ j < k /\ Seq.index a i = Seq.index b j))
	  (ensures (forall (x:ix b{j < x}). (index q (i + 1) x = index p i x) 
				       /\ index q (i + 1) j = Elim 
				       /\ index q i x = Elim))
          (decreases k)
let rec lemma_next_row_unchanged #a #b i j k p q = 
  if j+1=k 
  then iter_extends a b i j i k
  else let q' = iter_i_j a b i (k - 1) in
       let _ = lemma_next_row_unchanged #a #b i j (k - 1) p q' in
       iter_extends a b i (k - 1) i k

val lemma_next_row_aux: #a:seq int -> #b:seq int -> i:ix a -> j:ix b  
      -> p:iter a b i j{index p i j = Unknown} 
      -> q:iter a b (i + 1) 0{Seq.index a i = Seq.index b j}
      -> Lemma 
      (index q i j = Equal 
	    /\ (i + 1 < Seq.length a 
 	       ==> (index q (i + 1) j = Elim
  	           /\ (forall (k:ix b{j < k}). index q (i + 1) k = index p i k))))
let lemma_next_row_aux #a #b i j p q = 
    iter_step a b i j (i + 1) 0 p q;
    next_row_wraparound #a #b i; 
    if i + 1 < Seq.length a
    then lemma_next_row_unchanged #a #b i j (Seq.length b) p q

val lemma_next_row: #a:seq int -> #b:seq int -> i:ix a -> j:ix b  
      -> p:iter a b i j{index p i j = Unknown} 
      -> q:iter a b (i + 1) 0{Seq.index a i = Seq.index b j}
      -> Lemma 
  (requires True)
  (ensures (index q i j = Equal 
	    /\ (i + 1 < Seq.length a 
 	       ==> (index q (i + 1) j = Elim 
  	           /\ row_as_list b (row q (i + 1)) j
  	    	      = Cons.tl (row_as_list b (row p i) j)))))
let lemma_next_row #a #b i j p q = 
      lemma_next_row_aux #a #b i j p q; 
      if (i + 1 < Seq.length a)
      then row_as_list_eq b (row p i) (row q (i + 1)) (j + 1) (Seq.length b)

opaque type elim_streak row (j:bound row) (j':bound row) =
  (forall k. {:pattern (Seq.index row k)} (j <= k && k < j') ==> Seq.index row k = Elim)
 
val frame_elim_streak_aux:  a:_ -> b:_ -> i:ix a -> j:bound b -> j':bound b {j < j'} 
			-> p:iter a b i j'{elim_streak (row p i) j j'}
			-> q:iter a b (i + 1) 0
			-> k:ix b{j<=k && k < j'}
			-> Lemma (Seq.index (row q i) k = Elim)
let frame_elim_streak_aux a b i j j' p q k =
  assert (Seq.index (row p i) k = index p i k);
  assert (Seq.index (row q i) k = index q i k);
  assert (index q i k = Elim)
 
val frame_elim_streak:  a:_ -> b:_ -> i:ix a -> j:bound b -> j':bound b {j < j'} 
			-> p:iter a b i j'
			-> q:iter a b (i + 1) 0
			-> Lemma (requires (elim_streak (row p i) j j'))
				(ensures  (elim_streak (row q i) j j'))
let frame_elim_streak a b i j j' p q =
  qintro (frame_elim_streak_aux a b i j j' p q)

val lemma_row_all_elims: b:seq int -> row:seq entry{Seq.length row = Seq.length b} 
		    -> i:bound b -> j:bound b{i <= j}
		    -> Lemma
  (requires (elim_streak row i j))
  (ensures (row_as_list_from_to b row i j = []))
  (decreases (j - i))
let rec lemma_row_all_elims b row i j = 
  if i=j then ()
  else lemma_row_all_elims b row (i + 1) j

val lemma_row_elim_some: b:seq int -> s:seq entry{Seq.length s = Seq.length b} -> j0:bound s -> j:bound s{j0 <= j} -> 
    Lemma (requires (elim_streak s j0 j))
          (ensures (row_as_list b s j0
	            = row_as_list b s j))
	  (decreases (j - j0))
let rec lemma_row_elim_some b s j0 j = 
    if j0=j then ()
    else lemma_row_elim_some b s (j0 + 1) j

val lemma_row_elims_until: b:seq int -> row:seq entry{Seq.length row = Seq.length b} -> l:list int{is_Cons l}
			   -> i:bound b -> j:ix b{i < j}
			   -> Lemma 
  (requires (l = row_as_list b row i 
	    /\ elim_streak row (i + 1) j
	    /\ Seq.index row i <> Elim
	    /\ Seq.index row j <> Elim))
  (ensures (Cons.tl l = row_as_list b row j /\ is_Cons (Cons.tl l)))
let lemma_row_elims_until b row l i j = 
    lemma_row_elim_some b row (i + 1) j

val lemma_elim_tail: b:seq int -> row:seq entry{Seq.length row = Seq.length b} -> l:list int{is_Cons l} 
		    -> j:ix b 
		    -> Lemma
  (requires (l=row_as_list b row j
	     /\ elim_streak row (j + 1) (Seq.length b)))
  (ensures (Cons.tl l = []))
let lemma_elim_tail b row l j = lemma_row_all_elims b row (j + 1) (Seq.length b)

val lemma_ith_row_elim: #a:seq int -> #b:seq int -> i:ix a -> j:bound b -> j':bound b{j <= j'} -> p:iter a b (i + 1) 0
			-> Lemma
  (requires (elim_streak (row p i) j j'))
  (ensures (ith_row_from p i j = ith_row_from p i j'))
  (decreases (j' - j))
let rec lemma_ith_row_elim #a #b i j j' p = 
  if j=j' then ()
  else (assert (index p i j = Seq.index (row p i) j);
        lemma_ith_row_elim #a #b i (j+1) j' p)

val ith_row_from_false: a:seq int -> b:seq int -> i:ix a -> j:bound b -> j':bound b{j < j'}
			-> p:iter a b (i + 1) 0
			-> Lemma
  (requires (elim_streak (row p i) (j + 1) j' 
	     /\ index p i j = NotEqual))
  (ensures (ith_row_from p i j =
	         false::ith_row_from p i j'))
let ith_row_from_false a b i j j' p = 
  lemma_ith_row_elim i (j + 1) j' p
 			  
val next_ith_row_from_false:  a:_ -> b:_ -> i:ix a -> j:ix b -> j':bound b {j < j'} 
			    -> p:iter a b i j' 
			    -> q:iter a b (i + 1) 0
			    -> Lemma
        (requires (index p i j = NotEqual
		  /\ elim_streak (row p i) (j + 1) j'))
        (ensures (ith_row_from q i j 
		  = false::ith_row_from q i j'))
let next_ith_row_from_false a b i j j' p q = 
  assert (index q i j = NotEqual);
  if (j + 1 = j')
  then ()
  else (frame_elim_streak a b i (j + 1) j' p q;
        ith_row_from_false a b i j j' q)

val advance:  a:Seq.seq int -> b:Seq.seq int -> i:ix a -> j:ix b -> j':bound b{j<j'}
	    -> p:iter a b i j' -> q:iter a b (i + 1) 0
	    -> lb:list int{is_Cons lb}
	    -> Pure (bound b)
  (requires (lb=row_as_list b (Matrix2.row p i) j 
	    /\ index p i j = NotEqual 
	    /\ elim_streak (row p i) (j + 1) j'))
  (ensures (fun j' -> 
	      let p' = iter_i_j a b i j' in
  	         j < j'
	      /\  lb=row_as_list b (row p' i) j
    	      /\  elim_streak (row p' i) (j + 1) j'
	      /\  (j' < Seq.length b ==> index p' i j' = Unknown)
 	      /\  Cons.tl lb=row_as_list b (Matrix2.row p' i) j'
 	      /\  (Cons.tl lb=[] ==> j'=Seq.length b)))
  (decreases (Seq.length b - j'))
let rec advance a b i j j' p q lb =
  if j' = Seq.length b  
  then (lemma_elim_tail b (row p i) lb j; j')
  else if index p i j' = Elim
  then (let p' = iter_i_j a b i (j' + 1) in
        iter_extends a b i j' i (j' + 1);
        advance a b i j (j' + 1) p' q lb)
  else (lemma_row_elims_until b (row p i) lb j j';
	j')
 
opaque type elim_streak' (#a:seq int) (#b:seq int) (p:prod a b entry) row from until = 
  forall (k:ix b).{:pattern (index p row k)} (from <= k && k < until) ==> index p row k = Elim

val convert_elim_streak' : #a:_ -> #b:_ -> p:prod a b entry -> r:ix a -> from:ix b -> until:bound b 
      -> Lemma (requires (elim_streak' p r from until)) 
	      (ensures (elim_streak (row p r) from until))
	      [SMTPatT (elim_streak' p r from until)]
let convert_elim_streak' #a #b p r from until = ()

val convert_elim_streak_aux : #a:_ -> #b:_ -> r:ix a -> from:ix b -> until:bound b 
      -> p:prod a b entry{elim_streak (row p r) from until}
      -> k:ix b{from <= k && k < until}
      -> Lemma (index p r k  = Elim)
let convert_elim_streak_aux #a #b r from until p k = cut (Seq.index (row p r) k == index p r k)

val convert_elim_streak : #a:_ -> #b:_ -> r:ix a -> from:ix b -> until:bound b 
      -> p:prod a b entry{elim_streak (row p r) from until}
      -> Lemma (requires True)
	      (ensures (elim_streak' p r from until))
	      [SMTPatT (elim_streak (row p r) from until)]
let convert_elim_streak #a #b r from until p = 
  qintro (convert_elim_streak_aux #a #b r from until p)
    
val move_elim_streak_aux : a:_ -> b:_ -> i:ix a{i + 1 < Seq.length a} -> j:ix b -> j':bound b {j + 1 < j'}
		     -> q:iter a b (i + 1) 0{elim_streak' q i (j + 1) j' /\ index q i j = NotEqual}
		     -> k:ix b{j + 1 <= k && k < j'}
		     -> Lemma (index q (i + 1) k = Elim)
let move_elim_streak_aux a b i j j' q k = 
  assert (index q i j = NotEqual); 
  assert (index q i k = Elim);
  cut (exists (i':ix a). i' < i /\ index q i' k = Equal)

val move_elim_streak' : a:_ -> b:_ -> i:ix a{i + 1 < Seq.length a} -> j:ix b -> j':bound b {j + 1 < j'} 
		     -> q:iter a b (i + 1) 0
		     -> Lemma
        (requires (index q i j = NotEqual
		  /\ elim_streak' q i (j + 1) j'))
	(ensures (elim_streak' q (i + 1) (j + 1) j'))
let move_elim_streak' a b i j j' q = 
  qintro (move_elim_streak_aux a b i j j' q)

val move_elim_streak : a:_ -> b:_ -> i:ix a{i + 1 < Seq.length a} -> j:ix b -> j':bound b {j + 1 < j'} 
		     -> p:iter a b i j' 
		     -> q:iter a b (i + 1) 0
		     -> Lemma
        (requires (index p i j = NotEqual
		  /\ elim_streak (row p i) (j + 1) j'
		  /\ elim_streak (row q i) (j + 1) j'))
	(ensures (elim_streak (row q (i + 1)) (j + 1) j'))
let move_elim_streak a b i j j' p q = 
  move_elim_streak' a b i j j' q

val next_row_elements: a:_ -> b:_ -> i:ix a{i + 1 < Seq.length a} -> j:ix b -> j':bound b {j < j'} 
		     -> lb:list int{is_Cons lb}
		     -> p:iter a b i j' 
		     -> q:iter a b (i + 1) 0
		     -> Lemma
        (requires (index p i j = NotEqual
		  /\ lb=row_as_list b (row p i) j
		  /\ elim_streak (row p i) (j + 1) j'))
        (ensures (row_as_list b (row q (i + 1)) j
	      	         = Cons.hd lb::row_as_list b (row q (i + 1)) j'))
let next_row_elements a b i j j' lb p q = 
  assert (index q i j = NotEqual);
  assert (index q (i + 1) j = Unknown);
  assert (is_Cons (row_as_list b (row q (i + 1)) j));
  assert (Cons.hd (row_as_list b (row q (i + 1)) j) = Cons.hd lb);
  if j + 1 = j'
  then ()
  else (frame_elim_streak a b i (j + 1) j' p q;
        assert (index q i (j + 1) = Elim);
	move_elim_streak a b i j j' p q;
	lemma_row_elim_some b (row q (i + 1)) (j + 1) j')

val advance':  a:Seq.seq int -> b:Seq.seq int -> i:ix a -> j:ix b -> j':bound b{j<j'}
	    -> p:iter a b i j' -> q:iter a b (i + 1) 0
	    -> lb:list int{is_Cons lb}
	    -> Pure (bound b)
  (requires (lb=row_as_list b (Matrix2.row p i) j 
	    /\ index p i j = NotEqual 
	    /\ elim_streak (row p i) (j + 1) j'))
  (ensures (fun j' -> 
	      let p' = iter_i_j a b i j' in
  	         j < j'
     	      /\  elim_streak (row p' i) (j + 1) j'
	      /\  (j' < Seq.length b ==> index p' i j' = Unknown)
 	      /\  Cons.tl lb=row_as_list b (Matrix2.row p' i) j'
 	      /\  (Cons.tl lb=[] ==> j'=Seq.length b)
	      /\  (ith_row_from q i j =
 	            false::ith_row_from q i j')
 	      /\  (i + 1 < Seq.length a 
	      	     ==> row_as_list b (row q (i + 1)) j
	      	         = Cons.hd lb::row_as_list b (row q (i + 1)) j')))
let advance' a b i j j' p q lb = 
      let j'' = advance a b i j j' p q lb  in
      let p' = iter_i_j a b i j'' in
      next_ith_row_from_false a b i j j'' p' q;  
      if (i + 1 < Seq.length a) then next_row_elements a b i j j'' lb p' q;
      j''

val check_bob: a:int -> lb:list int -> Tot (list int * list bool)
let rec check_bob a lb =
  match lb with
   | [] -> [], []
   | hd::tl ->
     if hd=a
     then tl, [true]
     else let tl, r = check_bob a tl in
          hd::tl, false::r

val lemma_pnext: sa:Seq.seq int -> sb:Seq.seq int -> i:ix sa -> j:ix sb 
	       -> p:iter sa sb i j
	       -> pnext:iter sa sb i (j + 1)
	       -> Lemma 
  (requires (index p i j = Unknown
	     /\ index pnext i j = NotEqual))
  (ensures (row_as_list sb (row p i) j
	    = row_as_list sb (row pnext i) j))
let lemma_pnext sa sb i j p pnext = 
    iter_extends sa sb i j i (j + 1);
    assert (pnext = set_neq p i j);
    row_as_list_eq sb (row p i) (row pnext i) (j + 1) (Seq.length sb)

val lemma_bob: sa:Seq.seq int -> sb:Seq.seq int -> i:ix sa -> j:bound sb 
	       -> p:iter sa sb i j
	       -> q:iter sa sb (i + 1) 0
	       -> a:int -> lb:list int -> Lemma
  (requires (lb=row_as_list sb (Matrix2.row p i) j
	     /\ a=Seq.index sa i
	     /\ (lb=[] ==> j=Seq.length sb)
	     /\ (j < Seq.length sb ==> index p i j=Unknown)))
  (ensures (let br = check_bob a lb in
	    (i + 1 < Seq.length sa  
	     ==>  fst br = row_as_list sb (Matrix2.row q (i + 1)) j)
           /\ snd br = ith_row_from q i j))
  (decreases lb)
let rec lemma_bob sa sb i j p q a lb = match lb with 
  | [] -> ()
  | hd::tl ->
    iter_step sa sb i j (i + 1) 0 p q;
    let pnext = iter_i_j sa sb i (j + 1) in
    iter_step sa sb i j i (j + 1) p pnext;
    iter_extends sa sb i j i (j + 1);
    if hd=a
    then lemma_next_row i j p q
    else (lemma_pnext sa sb i j p pnext;
          let j' = advance' sa sb i j (j + 1) pnext q lb in
  	  let p' = iter_i_j sa sb i j' in
	  lemma_bob sa sb i j' p' q a tl)

val for_alice : list int -> list int -> Tot (list (list bool))
let rec for_alice la lb = match la with 
  | [] -> []
  | a::rest -> 
    let lb, r = check_bob a lb in 
    r::for_alice rest lb

val as_list : s:seq int -> i:bound s -> Tot (list int)
  (decreases (Seq.length s - i))
let rec as_list s i = 
  if i = Seq.length s then []
  else Seq.index s i :: as_list s (i + 1)

val rows_from : #a:seq int -> #b:seq int -> prod a b entry -> i:bound a -> Tot (list (list bool))
  (decreases (Seq.length a - i))
let rec rows_from #a #b p i = 
  if i = Seq.length a then []
  else ith_row p i :: rows_from p (i + 1)

type all_iters a b = iter a b (Seq.length a) (Seq.length b)

val ith_row_eq:  #a:seq int -> #b:seq int -> r:bound a
		 -> p:iter a b r 0 
		 -> s:all_iters a b
		 -> i:ix a{i < r}
		 -> j:bound b
		 -> Lemma
  (requires True)
  (ensures (ith_row_from p i j = ith_row_from s i j))
  (decreases (Seq.length b - j))
let rec ith_row_eq #a #b r p s i j = 
  if j = Seq.length b then ()
  else ith_row_eq r p s i (j + 1)
  
val lemma_sub_all_iters: #a:seq int -> #b:seq int -> r:bound a
		      -> p:iter a b r 0 
		      -> s:all_iters a b
		      -> i:ix a{i < r}
		      -> Lemma
  (ensures (ith_row p i = ith_row s i)) 
let lemma_sub_all_iters #a #b r p s i = ith_row_eq r p s i 0

val elim_streak_down_aux: a:_ -> b:_ -> i:ix a{i + 1 < Seq.length a} -> j:bound b
		      -> p:iter a b i j{elim_streak' p i 0 j}
		      -> q:iter a b (i + 1) 0
		      -> k:ix b{k < j}
		      -> Lemma
   (index q (i + 1) k = Elim)
let elim_streak_down_aux a b i j p q k = 
  assert (index p i k = Elim);
  cut (exists (i':ix a). i' < i /\ index p i' k = Equal /\ index q i' k = Equal)

val elim_streak_down: a:_ -> b:_ -> i:ix a{i + 1 < Seq.length a} -> j:bound b
		      -> p:iter a b i j
		      -> q:iter a b (i + 1) 0
		      -> Lemma
  (requires (elim_streak' p i 0 j))
  (ensures (elim_streak' q (i + 1) 0 j))
let elim_streak_down a b i j p q = 
  qintro (elim_streak_down_aux a b i j p q)
 
val next_row_elements_alice: a:_ -> b:_ -> i:ix a -> j:bound b
		     -> p:iter a b i j
		     -> q:iter a b (i + 1) 0
		     -> Lemma
        (requires (elim_streak' p i 0 j))
        (ensures (i + 1 < Seq.length a
		    ==>  row_as_list b (row q (i + 1)) 0
	      	         = row_as_list b (row q (i + 1)) j))
let next_row_elements_alice a b i j p q = 
    if (i + 1 < Seq.length a)
    then (elim_streak_down a b i j p q;
          lemma_row_elim_some b (row q (i + 1)) 0 j)
 
val skip_elims: sa:seq int -> sb:seq int -> i:ix sa -> j:bound sb -> p:iter sa sb i j -> q:iter sa sb (i + 1) 0 -> 
	 Pure (bound sb)
	      (requires (elim_streak' p i 0 j))
	      (ensures (fun j -> 
			  let p' = iter_i_j sa sb i j in
			    p = p'
			  /\ elim_streak' p' i 0 j
			  /\ (j < Seq.length sb ==> index p' i j <> Elim)))
	      (decreases (Seq.length sb - j))
let rec skip_elims sa sb i j p q = 
  if j = Seq.length sb 
  then j
  else match index p i j with 
 	  | Unknown -> j
	  | Elim -> 
 	    let j' = j + 1 in 
	    let p' = iter_i_j sa sb i j' in
	    iter_extends sa sb i j i j';
	    skip_elims sa sb i (j + 1) p' q

val ith_row_elim_prefix: #a:_ -> #b:_ -> p:prod a b entry -> i:ix a -> j:bound b
			 -> Lemma
  (requires (elim_streak (row p i) 0 j))
  (ensures  (ith_row_from p i 0 = ith_row_from p i j))
  (decreases j)
let rec ith_row_elim_prefix #a #b p i j = 
  if j=0 
  then ()
  else (cut (Seq.index (row p i) (j - 1) == Elim);
        ith_row_elim_prefix #a #b p i (j - 1))

        
val first_iteration_index: sa:seq int -> sb:seq int -> i:ix sa -> p:iter sa sb i 0 -> q:iter sa sb (i + 1) 0 -> 
	 Pure (bound sb)
	      (requires True)
	      (ensures (fun j -> 
			  let p' = iter_i_j sa sb i j in
			  (row_as_list sb (row p i) 0 
			    = row_as_list sb (row p' i) j
			    /\  (i + 1 < Seq.length sa 
			         ==> (row_as_list sb (row q (i + 1)) 0 
			              = row_as_list sb (row q (i + 1)) j))
			     /\ (j < Seq.length sb ==> index p' i j <> Elim)
			     /\ ith_row p' i = ith_row_from p' i j
			     /\ ith_row q i  = ith_row_from q  i j
)))
let first_iteration_index sa sb i p q = 
   let j = skip_elims sa sb i 0 p q in
  let p' = iter_i_j sa sb i j in
  lemma_row_elim_some sb (row p i) 0 j;
  next_row_elements_alice sa sb i j p' q;
  if j<>0
  then (frame_elim_streak sa sb i 0 j p' q;
        ith_row_elim_prefix q i j; 
	ith_row_elim_prefix p' i j);
  j

 
val lemma_alice: sa:Seq.seq int -> sb:Seq.seq int -> i:bound sa 
	       -> p:iter sa sb i 0
	       -> t:all_iters sa sb 
	       -> la:list int -> lb:list int -> Lemma
  (requires ((i < Seq.length sa ==> lb=row_as_list sb (row p i) 0)
	     /\ la=as_list sa i))
  (ensures (for_alice la lb = rows_from t i))
  (decreases la)
let rec lemma_alice sa sb i p t la lb = match la with 
  | [] -> ()
  | hd::tl -> 
    begin
      let q = iter_i_j sa sb (i + 1) 0 in 
      let j = first_iteration_index sa sb i p q in 
      let p = iter_i_j sa sb i j in
      lemma_bob sa sb i j p q hd lb;
      let lb', r = check_bob hd lb in
      lemma_sub_all_iters (i + 1) q t i;
      lemma_alice sa sb (i + 1) q t tl lb'
    end

let all_iterations a b = iter_i_j a b (Seq.length a) (Seq.length b)

val as_list_init_b: a:Seq.seq int{Seq.length a <> 0} 
		  -> b:Seq.seq int 
		  -> i:bound b
		  -> Lemma  
  (ensures (row_as_list b (row (init a b) 0) i
	    = as_list b i))
  (decreases (Seq.length b - i))
let rec as_list_init_b a b i = 
    if i = Seq.length b then ()
    else as_list_init_b a b (i + 1)

//TODO: change rows_from's first two arguments to be nats corresponding to
// the lengths of the sequences, rather than the sequences themselves.
// that makes it evident that we can compute the (for_alice la lb) trace from
// the public parameters only.
//
// We'd like the ensures clause to be:
// for_alice la lb = rows_from' (length la) (length lb) (make_sparse (full a b) (init' (length la) (length lb)) 0 0) 0
// 1. rows_from to be changes to rows_from'  (so that it depends only on the lengths, not on the seqs themselves)
// 2. to make use of the fast_is_sparse_full lemma to prove that
//    all_iterations sa sb = (make_sparse (full a b) (init' (length la) (length lb)) 0 0)
//  Maybe need to use extensional equality? 
val thm : sa:Seq.seq int -> sb:Seq.seq int -> la:list int -> lb:list int -> Lemma 
    (requires (la = as_list sa 0 /\ lb = as_list sb 0))
    (ensures (for_alice la lb = rows_from (all_iterations sa sb) 0))
let thm sa sb la lb = 
  if Seq.length sa <> 0 then as_list_init_b sa sb 0;
  lemma_alice sa sb 0 (iter_i_j sa sb 0 0) (all_iterations sa sb) la lb

