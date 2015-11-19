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


val map_fst_aux : s:Seq.seq (int * bool) 
              -> out:Seq.seq int{Seq.length out = Seq.length s}
              ->   i:bound s
              -> Tot (t:Seq.seq int{Seq.length t = Seq.length s})
  (decreases (Seq.length s - i))
let rec map_fst_aux s out i = 
  if i = Seq.length s then out
  else let out = Seq.upd out i (fst (Seq.index s i)) in
       map_fst_aux s out (i + 1)

val lemma_map_fst_aux: s:Seq.seq (int * bool) 
                   -> out: Seq.seq int{Seq.length s = Seq.length out}
                   ->   i:bound s 
		  -> Lemma
  (requires (forall (j:nat{j < i}). Seq.index out j = fst (Seq.index s j)))
  (ensures (forall (j:ix out). Seq.index (map_fst_aux s out i) j = fst (Seq.index s j)))
  (decreases (Seq.length s - i))
let rec lemma_map_fst_aux s out i = 
  if i = Seq.length s then ()
  else let out = Seq.upd out i (fst (Seq.index s i)) in
       lemma_map_fst_aux s out (i + 1)

let map_fst s = map_fst_aux s (Seq.create (Seq.length s) 0) 0
val lemma_map_fst: s:Seq.seq (int * bool) -> j:ix s -> Lemma
  (requires True)
  (ensures (Seq.index (map_fst s) j = fst (Seq.index s j)))
  [SMTPat (Seq.index (map_fst s) j)]
let lemma_map_fst s j = lemma_map_fst_aux s (Seq.create (Seq.length s) 0) 0

type seq 'a = Seq.seq 'a
val filter_snd_aux: s:seq (int * bool) -> i:bound s -> Tot (list (int * ix s))
  (decreases (Seq.length s - i))
let rec filter_snd_aux s i = 
  if i=Seq.length s 
  then []
  else let (x, keep) = Seq.index s i in 
       if keep then (x, i) :: filter_snd_aux s (i + 1)
       else  filter_snd_aux s (i + 1)

val filter_snd : s:seq (int * bool) -> Tot (list (int * ix s))
let filter_snd s = filter_snd_aux s 0

val mark_elim : a:seq int -> s:seq (int * bool){map_fst s = a} -> i:ix a -> Tot (s:seq (int * bool){map_fst s = a})
let mark_elim a s i = 
  let r = Seq.upd s i (fst (Seq.index s i), false) in 
  cut (Seq.Eq (map_fst r) a);
  r

val check_bob: a:int -> lb:list int -> Tot (list int * bool)
let rec check_bob a lb =
  match lb with
   | [] -> [], false
   | hd::tl -> 
     if hd=a
     then tl, true
     else let tl, r = check_bob a tl in
	  hd::tl, r
 
(* 
  Computes what remains of bob's set after m iterations of alice's loop
   ... only the elements in the resulting sequence with the flag set to true
*) 
val eliminate_rows: #a:Seq.seq int -> #b:Seq.seq int -> p:sparse a b 
		   -> m:bound a -> i:bound a{i <= m} -> j:bound b 
 		   -> lb:seq (int * bool){map_fst lb = b}
  	           -> Tot (x:seq (int * bool){map_fst x = b})
  (decreases %[(m - i); (Seq.length b - j)])
let rec eliminate_rows #a #b p m i j lb = 
  if i = m 
  then lb
  else if j = Seq.length b then eliminate_rows p m (i + 1) 0 lb
  else if index p i j=Elim then eliminate_rows p m i (j + 1) (mark_elim b lb j)
  else eliminate_rows p m i (j + 1) lb

(* 
  Given Bob's set lb in the mth round, 
  this computes what remains of Bob's set after j abstract iterations of his loop.
*)
val eliminate_col: #b:Seq.seq int -> lb:seq (int * bool){map_fst lb = b} -> n:bound b -> j:bound b{j <= n} -> Tot (option (list (int * ix b)))
  (decreases (n - j))
let rec eliminate_col #b lb n j = 
  if j = Seq.length b                 //no more iterations left
  then Some []
  else if j=n && snd (Seq.index lb j) //we've reached the spot; the element had better be still retained by Bob
  then Some (filter_snd lb)
  else if j < n 
  then eliminate_col #b (mark_elim b lb j) n (j + 1)
  else None

assume val lemma_filter_snd_cons: lb:seq (int * bool) -> j:ix lb -> Lemma
  (requires (snd (Seq.index lb j)))
  (ensures (is_Cons (filter_snd lb)))

val lemma_eliminate_col_nil: #b:seq int -> lb:seq (int * bool){map_fst lb =b} -> n:bound b -> j:bound b{j <= n} -> 
    Lemma (requires (eliminate_col #b lb n j = Some []))
	  (ensures (n = Seq.length b))
	  (decreases (n - j))
let rec lemma_eliminate_col_nil #b lb n j = 
  if j = Seq.length b
  then ()
  else if j=n && snd (Seq.index lb j)
  then lemma_filter_snd_cons lb j
  else if j < n
  then lemma_eliminate_col_nil #b (mark_elim b lb j) n (j + 1)
  else ()

assume val zip_with_true : s:seq int -> Tot (seq (int * bool))
assume val lemma_zip_with_true : s:seq int -> Lemma 
       (requires True)
       (ensures  ((map_fst (zip_with_true s) = s 
		 /\ (forall (i:ix s).{:pattern (Seq.index (zip_with_true s) i)} snd (Seq.index (zip_with_true s) i) = true))))
       [SMTPat (zip_with_true s)]
  
let eliminate #a #b (p:sparse a b) (m:bound a) (n:bound b)  =
  eliminate_col #b (eliminate_rows p m 0 0 (zip_with_true b)) n 0

assume val lemma_eliminate_nil: #a:seq int -> #b:seq int -> p:sparse a b -> i:bound a -> j:bound b -> 
    Lemma (requires (eliminate p i j = Some []))
	  (ensures (j = Seq.length b))

val ith_row_bool: #a:Seq.seq int -> #b:Seq.seq int -> p:prod a b entry -> i:ix a -> j:bound b -> Tot bool
  (decreases (Seq.length b - j))
let rec ith_row_bool #a #b p i j = 
  if j = Seq.length b         then false
  else if index p i j = Equal then true
  else ith_row_bool p i (j + 1)

val proj_fst : #a:seq int -> list (int * ix a) -> Tot (list int)
let rec proj_fst #a l = match l with
  | [] -> []
  | hd::tl -> fst hd :: proj_fst #a tl

val lemma_bob: sa:Seq.seq int -> sb:Seq.seq int -> p:sparse sa sb -> i:ix sa -> j:ix sb 
	       -> a:int -> lb:list int -> Lemma
  (requires (is_Some(eliminate p i j)
	    /\ proj_fst #sb (Some.v (eliminate p i j)) = lb 
	    /\ a=Seq.index sa i))
  (ensures (let br = check_bob a lb in 
	    is_Some (eliminate p (i + 1) j)
	  /\ fst br = proj_fst #sb (Some.v (eliminate p (i + 1) j))
          /\ snd br = ith_row_bool p i 0))
  (decreases lb)
let rec lemma_bob sa sb p i j a lb = match lb with 
  | [] -> 
    lemma_eliminate_nil p i j;
    assert (j = Seq.length sb);
    admit()
  | _ -> admit()
  


  if k = Seq.length sb 
  then B p sb false
  else if Seq.index sb k = a //found it
  then let p = elim p i j in
       let sb = remove sb k in 
       B p sb true
  else let p, j' = move_index_to p sb (k + 1) in 
       check_bob oa ob p i j' a sb (k + 1)

int -> sb:Seq.seq (int * bool) -> i:nat{i<=Seq.length sb} -> Tot (Seq.seq (int * bool) * bool)
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


assume val sparse_jth_row: a:seq int -> b:seq int -> s:sparse a b -> r:ix a -> Tot bool

val lemma_bob: a:Seq.seq int
            -> b:Seq.seq (int * bool) 
            -> ia:ix sa
            -> jb:bound sb 
            -> p:sparse a (fst_bob b)
            -> Lemma
              (requires (elims_correspond 
              (let b = fst (check_bob (Seq.index a ia) b) in 
               let r = snd (check_bob (Seq.index a ia) b) in 
               r = 
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
