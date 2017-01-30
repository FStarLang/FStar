module FStar.StackArray

//#set-options "--max_fuel 0 --initial_fuel 0 --initial_ifuel 0 --max_ifuel 0" ... NEED TO MAKE THIS as_ref, as_ref, as_rref, ... a bit simpler

open FStar.Seq
open FStar.HyperStack
open FStar.HST
open FStar.UInt32

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

let u32 = UInt32.t

type bounded_seq (t:Type) = s:seq t{length s <= UInt.max_int n}
type array (t:Type) = stackref (bounded_seq t)//NS: TODO if I change this to stacked, then I get unification failures elsewhere. seems like a bug

let as_stackref (#t:Type) (a:array t) : GTot (stackref (bounded_seq t)) = a

(* Commented for as long as not specified *)
// assume val op_At_Bar: #a:Type -> array a -> array a -> St (array a)

val of_seq: #a:Type -> s:bounded_seq a -> ST (array a)
  (requires (fun h -> True))
  (ensures  (fun s0 x s1 -> (~(contains s0 x) /\ contains s1 x /\ x.id = s0.tip /\ s1=HS.upd s0 x s)))
let of_seq #a s = salloc s

val to_seq: #a:Type -> s:array a -> STL (seq a)
  (requires (fun h -> contains h s))
  (ensures  (fun h0 x h1 -> sel h0 s=x /\ h0=h1))
let to_seq #a s = !s
  
val create : #a:Type -> n:u32 -> init:a -> ST (array a)
  (requires (fun h -> True))
  (ensures  (fun h0 x h1 -> ~(contains h0 x) /\ contains h1 x /\ x.id = h0.tip
			  /\ h1 = HS.upd h0 x (Seq.create (v n) init) ))
let create #a n init = salloc (Seq.create (v n) init)

val index : #a:Type -> x:array a -> n:u32 -> STL a
  (requires (fun h -> contains h x /\ v n < Seq.length (sel h x)))
  (ensures  (fun h0 res h1 -> h0 = h1 /\ v n < Seq.length (sel h0 x) /\ res=Seq.index (sel h0 x) (v n)))
let index #a x n = 
  let s = to_seq x in Seq.index s (v n) //TODO: Seem to need this eta nonsense ... if we get rid of the let binding, type inference fails

val upd : #a:Type -> x:array a -> n:u32 -> z:a -> STL unit
  (requires (fun h -> contains h x /\ v n < Seq.length (sel h x)))
  (ensures  (fun h0 _ h1 -> (contains h0 x /\ contains h1 x /\ v n < Seq.length (sel h0 x)
			   /\ h1=HS.upd h0 x (Seq.upd (sel h0 x) (v n) z)) ))
let upd #a x n z = 
  let s = to_seq x in
  let s = Seq.upd s (v n) z in
  x := s

val length: #a:Type -> x:array a -> STL u32
  (requires (fun h -> contains h x))
  (ensures  (fun h0 y h1 -> v y=length (sel h0 x) /\ h0==h1))
let length #a x = uint_to_t (Seq.length (to_seq x))
  
val swap: #a:Type -> x:array a -> i:u32 -> j:u32{v i <= v j} -> STL unit 
  (requires (fun s -> contains s x /\ v j < Seq.length (sel s x)))
  (ensures (fun s0 _u s1 -> contains s0 x /\ contains s1 x /\ v j < Seq.length (sel s0 x)
    /\ modifies (Set.singleton (frameOf x)) s0 s1
    /\ modifies_ref (frameOf x) !{as_ref x} s0 s1
    /\ Seq.equal (HS.sel s1 x) (Seq.swap (sel s0 x) (v i) (v j))))
let swap #a x i j =
  let tmpi = index x i in
  let tmpj = index x j in
  upd x j tmpi;
  upd x i tmpj
	 
let rec copy_aux: #a:Type -> s:array a -> cpy:array a -> ctr:u32 -> STL unit
    (requires (fun h -> contains h s /\ contains h cpy /\ s <> cpy
	       /\ Seq.length (sel h cpy) = Seq.length (sel h s)
	       /\ v ctr <= Seq.length (sel h cpy)
	       /\ (forall (i:nat). i < v ctr ==> Seq.index (sel h s) i = Seq.index (sel h cpy) i)))
    (ensures (fun h0 u h1 -> contains h1 s /\ contains h1 cpy /\ s <> cpy 
	            /\ modifies (Set.singleton (frameOf cpy)) h0 h1
		    /\ modifies_ref (frameOf cpy) !{as_ref cpy} h0 h1
		    /\ Seq.equal (sel h1 cpy) (sel h0 s) ))
  = fun #a s cpy ctr -> 
    if (eq (length cpy) ctr) then ()
    else (upd cpy ctr (index s ctr);
	  copy_aux #a s cpy (ctr +^ (uint_to_t 1)))

val copy:
  #a:Type -> s:array a ->
  ST (array a) 
     (requires (fun h -> contains h s
			 /\ Seq.length (sel h s) > 0))
     (ensures (fun h0 r h1 -> ~(contains h0 r) /\ contains h1 r /\ frameOf r = h0.tip
			    /\ modifies (Set.singleton h0.tip) h0 h1
			    /\ modifies_ref h0.tip !{} h0 h1
			    /\ (Seq.equal (sel h1 r) (sel h0 s)) ))
let copy #a s =
  let cpy = create (length s) (index s (uint_to_t 0)) in
  copy_aux s cpy (uint_to_t 0);
  cpy

val blit_aux:
  #a:Type -> s:array a -> s_idx:u32 -> t:array a -> t_idx:u32 -> len:u32 -> ctr:u32 -> STL unit
     (requires (fun h -> contains h s /\ contains h t /\ s <> t
		/\ Seq.length (sel h s) >= v s_idx + v len
		/\ Seq.length (sel h t) >= v t_idx + v len
		/\ v ctr <= v len
		/\ (forall (i:nat). i < v ctr 
		     ==> Seq.index (sel h s) (v s_idx+i) = Seq.index (sel h t) (v t_idx+i))))
     (ensures (fun h0 u h1 -> contains h1 s /\ contains h1 t /\ s <> t
               /\ modifies_one (frameOf t) h0 h1
	       /\ (modifies_ref (frameOf t) !{as_ref t} h0 h1)
	       /\ (Seq.length (sel h1 s) >= v s_idx + v len)
	       /\ (Seq.length (sel h1 t) >= v t_idx + v len)
	       /\ (Seq.length (sel h0 s) = Seq.length (sel h1 s))
	       /\ (Seq.length (sel h0 t) = Seq.length (sel h1 t))
	       /\ (forall (i:nat). i < v len 
		   ==> Seq.index (sel h1 s) (v s_idx+i) = Seq.index (sel h1 t) (v t_idx+i))
	       /\ (forall (i:nat). (i < Seq.length (sel h1 t) /\ (i < v t_idx \/ i >= v t_idx + v len)) 
		   ==> Seq.index (sel h1 t) i = Seq.index (sel h0 t) i) ))
let rec blit_aux #a s s_idx t t_idx len ctr =
  let h0 = HST.get() in
  if (len -^ ctr) =^ (uint_to_t 0) then ()
  else 
    begin 
      upd t (t_idx +^ ctr) (index s (s_idx +^ ctr));
      let h = HST.get() in
      blit_aux s s_idx t t_idx len (ctr+^(uint_to_t 1));
      let h'= get() in
      cut (modifies_ref (frameOf t) !{as_ref t} h h') (* Necessary *)
    end

val blit:
  #a:Type -> s:array a -> s_idx:u32 -> t:array a -> t_idx:u32 -> len:u32 -> STL unit
     (requires (fun h -> contains h s /\ contains h t /\ s <> t
		/\ Seq.length (sel h s) >= v s_idx + v len
		/\ Seq.length (sel h t) >= v t_idx + v len ))
     (ensures (fun h0 u h1 -> contains h1 s /\ contains h1 t /\ s <> t
	       /\ Seq.length (sel h1 s) >= v s_idx + v len
	       /\ Seq.length (sel h1 t) >= v t_idx + v len
	       /\ Seq.length (sel h0 s) = Seq.length (sel h1 s)
	       /\ Seq.length (sel h0 t) = Seq.length (sel h1 t)
	       /\ modifies_one (frameOf t) h0 h1
	       /\ modifies_ref (frameOf t) !{as_ref t} h0 h1
	       /\ (forall (i:nat). i < v len 
		   ==> Seq.index (sel h1 s) (v s_idx+i) = Seq.index (sel h1 t) (v t_idx+i))
	       /\ (forall (i:nat). (i < Seq.length (sel h1 t) /\ (i < v t_idx \/ i >= v t_idx + v len))
		   ==> Seq.index (sel h1 t) i = Seq.index (sel h0 t) i) ))
let rec blit #a s s_idx t t_idx len =
  blit_aux s s_idx t t_idx len (uint_to_t 0)

val sub: #a:Type -> s:array a -> idx:u32 -> len:u32 -> ST (array a)
    (requires (fun h -> contains h s 
      /\ Seq.length (sel h s) > 0 
      /\ v idx + v len <= Seq.length (sel h s) ))
    (ensures (fun h0 t h1 -> contains h1 t /\ contains h0 s /\ ~(contains h0 t) /\ t.id = h0.tip
      /\ v idx + v len <= Seq.length (sel h0 s)
      /\ h1=HS.upd h0 t (Seq.slice (sel h0 s) (v idx) (v idx+v len)) ))
let sub #a s idx len =
  let s = to_seq s in
  let s = Seq.slice s (v idx) (v idx+v len) in
  of_seq s
  
(* (\* JK: assuming the following because 'a <> a ==> seq a' <> seq a does cannot be proven *)
(*    by the solver *\) *)
(* let lemma_array_ineq_1 (#a:Type) (#a':Type) (x:array a) (y:array a') *)
(*   : Lemma (requires (a <> a')) *)
(* 	  (ensures (as_ref x =!= as_ref y)) *)
(* 	  [SMTPat (a <> a')] *)
(*   = admit() // TODO *)
