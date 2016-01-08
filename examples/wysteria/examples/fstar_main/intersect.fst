(*--build-config
    options:--admit_fsi FStar.Seq --admit_fsi FStar.Matrix2 --admit_fsi Matrix --admit_fsi FStar.Set --z3timeout 10;
    other-files:set.fsi seq.fsi FStar.Matrix2.fsti matrix.fsti traces.fst
  --*)
module Matrix
open FStar
open FStar.Matrix2
open Traces
type all_iters a b = iter a b (Seq.length a) (Seq.length b)
open FStar.Set
type seq 'a = Seq.seq 'a
 
val seq_as_set: a:seq int -> i:bound a -> Tot (set int)
  (decreases (Seq.length a - i))
let rec seq_as_set a i = 
  if i = Seq.length a then Set.empty
  else Set.union (Set.singleton (Seq.index a i))
		 (seq_as_set a (i + 1))

let as_set s = seq_as_set s 0
open FStar.Set

opaque type sound (a:seq int) (b:seq int) (i:bound a) (j:bound b) (s:set int) = 
  forall x. mem x s ==> (exists (i':ix a) (j':ix b).{:pattern (witness_row i'); (witness_col j')} 
				   witness_row i' 
				   /\ witness_col j'
				   /\ precedes (i', j') (i, j) 
				   /\ Seq.index a i' = Seq.index b j')


opaque type complete (a:seq int) (b:seq int) (i:bound a) (j:bound b) (s:set int) = 
  forall x.{:pattern (mem x s)} (exists (i':ix a) (j':ix b).{:pattern (witness_row i'); (witness_col j')}
				   witness_row i' 
				   /\ witness_col j'
				   /\ precedes (i', j') (i, j) 
				   /\ Seq.index a i' = Seq.index b j')
  ==> mem x s

type isect (a:seq int) (b:seq int) (i:bound a) (j:bound b) =
  s:set int{forall x. mem x s <==> (exists (i':ix a) (j':ix b).
				   witness_row i' 
				   /\ witness_col j'
				   /\ precedes (i', j') (i, j) 
				   /\ Seq.index a i' = Seq.index b j')}

type full_isect (a:seq int) (b:seq int)  = isect a  b (Seq.length a) (Seq.length b)

assume val qintro2  : #a:Type -> #b:Type -> #p:(a -> b -> Type) -> =f:(x:a -> y:b -> Lemma (p x y)) -> Lemma (forall (x:a) (y:b). p x y)

val lemma_complete_aux: a:seq int -> b:seq int -> i:ix a -> j:ix b -> s:isect a b i j -> i':ix a -> j':ix b -> 
		    Lemma ((precedes (i', j') (i, (j + 1)) /\ Seq.index a i' = Seq.index b j')
			   ==> (mem (Seq.index a i') (union (singleton (Seq.index a i')) s)))
let lemma_complete_aux a b i j s i' j' = cut (witness_row i'); cut (witness_col j')

//TODO: 3 .. get rid of this admit, either by staring more at the triggers
///      or, moving to squash proofs        
val lemma_complete: a:seq int -> b:seq int -> i:ix a -> j:ix b -> s:isect a b i j -> 
		    Lemma (requires (Seq.index a i = Seq.index b j))
		          (ensures (complete a b i (j + 1) (union (singleton (Seq.index a i)) s)))
let lemma_complete a b i j s =  admit() //this really is just a restatement of lemma_complete_aux ... but the triggers fail to fire properly
  // cut (witness_row i);
  // cut (witness_col j);
  // let y = Seq.index a i in
  // cut (forall x. mem x (union (singleton y) s) ==> x=y || mem x s);
  // qintro2 (lemma_complete_aux a b i j s)

val intersect: a:seq int -> b:seq int -> p:all_iters a b -> i:bound a -> j:bound b -> s:isect a b i j -> Tot (full_isect a b)
  (decreases %[Seq.length a - i; Seq.length b - j])
let rec intersect a b p i j s = 
  if i = Seq.length a then s 
  else if j = Seq.length b then intersect a b p (i + 1) 0 s
  else if index p i j = Equal then (cut (witness_row i); 
				    cut (witness_col j);
				    let s' = Set.union (singleton (Seq.index a i)) s in
				    lemma_complete a b i j s;
			            intersect a b p i (j + 1) s')
  else if index p i j = NotEqual then intersect a b p i (j + 1) s
  else (assert (index p i j = Elim);
        intersect a b p i (j + 1) s)

//TODO 4. build_matrix : la:nat -> lb:bat -> list (list bool) -> mat la lb entry
///    5. Lemma: build_matrix la lb (for_alice a b) = make_sparse (full a b)
//     6. intersect' a b bools = intersect a b (make_sparse (full a b)) 0 0 emp
//     7. for_alice_is_correct: a:seq Z -> b:seq Z -> Lemma (intersect' a b (for_alice (as_list a) (as_list b)) = full_isect a b)
//     

