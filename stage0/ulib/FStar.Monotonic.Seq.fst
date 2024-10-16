(*
   Copyright 2008-2018 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStar.Monotonic.Seq

open FStar.Seq
open FStar.Classical
module HS   = FStar.HyperStack
module HST  = FStar.HyperStack.ST

open FStar.HyperStack
open FStar.HyperStack.ST

(* 2016-11-22: The following is meant to override the fact that the
   enclosing namespace of the current module (here FStar.Monotonic) is
   automatically opened, which makes Seq resolve into
   FStar.Monotonic.Seq instead of FStar.Seq. *)
module Seq = FStar.Seq

////////////////////////////////////////////////////////////////////////////////

(*
 * 12/08
 * AR: writing this in terms of length and index
 *     earlier it was written in terms of an exists s3. Seq.equal (append s1 s3) s2
 *     that meant going through many hoops to prove simple things like transitivity of grows
 *     so far this seems to work better.
 *)
let grows_aux (#a:Type) :Preorder.preorder (seq a)
  = fun (s1:seq a) (s2:seq a) ->
    length s1 <= length s2 /\
    (forall (i:nat).{:pattern (Seq.index s1 i) \/ (Seq.index s2 i)} i < length s1 ==> index s1 i == index s2 i)

[@@"opaque_to_smt"]
let grows #a = grows_aux #a

type rid = HST.erid

let snoc (s:seq 'a) (x:'a) 
  : Tot (seq 'a) 
  = Seq.append s (Seq.create 1 x)

let lemma_snoc_extends (#a:Type) (s:seq a) (x:a)
  : Lemma (requires True)
	  (ensures (grows s (Seq.snoc s x)))
	  [SMTPat (grows s (Seq.snoc s x))]
  = reveal_opaque (`%grows) (grows #a)

let alloc_mref_seq (#a:Type) (r:rid) (init:seq a)
  : ST (m_rref r (seq a) grows)
       (requires (fun _ -> HST.witnessed (region_contains_pred r)))
       (ensures (fun h0 m h1 ->
	 HS.contains h1 m /\
	 HS.sel h1 m == init /\
	 HST.ralloc_post r init h0 m h1))
  = ralloc r init

(*
 * AR: changing rids below to rid which is eternal regions.
 *)
let at_least (#a:Type) (#i:rid) (n:nat) (x:a) (r:m_rref i (seq a) grows) (h:mem) =
    Seq.length (HS.sel h r) > n
  /\ Seq.index (HS.sel h r) n == x

let at_least_is_stable (#a:Type) (#i:rid) (n:nat) (x:a) (r:m_rref i (seq a) grows)
  : Lemma (ensures stable_on_t r (at_least n x r))
  = reveal_opaque (`%grows) (grows #a)

(** extending a stored sequence, witnessing its new entry for convenience. *)
let write_at_end (#a:Type) (#i:rid) (r:m_rref i (seq a) grows) (x:a)
  : ST unit
       (requires (fun h -> True))
       (ensures (fun h0 _ h1 ->
	               contains h1 r
		     /\ modifies_one i h0 h1
		     /\ modifies_ref i (Set.singleton (HS.as_addr r)) h0 h1
		     /\ HS.sel h1 r == Seq.snoc (HS.sel h0 r) x
		     /\ witnessed (at_least (Seq.length (HS.sel h0 r)) x r)))
  =
    recall r;
    let s0 = !r in
    let n = Seq.length s0 in
    r := Seq.snoc s0 x;
    at_least_is_stable n x r;
    Seq.contains_snoc s0 x;
    mr_witness r (at_least n x r)

////////////////////////////////////////////////////////////////////////////////
//Monotone sequences with a (stateless) invariant of the whole sequence
////////////////////////////////////////////////////////////////////////////////

let grows_p (#a:Type) (p:seq a -> Type) :Preorder.preorder (s:seq a{p s}) =
  fun s1 s2 -> grows s1 s2

let i_seq (r:rid) (a:Type) (p:seq a -> Type) = m_rref r (s:seq a{p s}) (grows_p p)

let alloc_mref_iseq (#a:Type) (p:seq a -> Type) (r:rid) (init:seq a{p init})
  : ST (i_seq r a p)
       (requires (fun _ -> HST.witnessed (region_contains_pred r)))
       (ensures (fun h0 m h1 -> HST.ralloc_post r init h0 m h1))
  = ralloc r init

let i_at_least (#r:rid) (#a:Type) (#p:(seq a -> Type)) (n:nat) (x:a) (m:i_seq r a p) (h:mem) =
        Seq.length (HS.sel h m) > n
      /\ Seq.index (HS.sel h m) n == x

let i_at_least_is_stable (#r:rid) (#a:Type) (#p:seq a -> Type) (n:nat) (x:a) (m:i_seq r a p)
  : Lemma (ensures stable_on_t m (i_at_least n x m))
  = reveal_opaque (`%grows) (grows #a)

let int_at_most #r #a #p (x:int) (is:i_seq r a p) (h:mem) : Type0 =
  x < Seq.length (HS.sel h is)

let int_at_most_is_stable (#r:rid) (#a:Type) (#p:seq a -> Type) (is:i_seq r a p) (k:int)
  : Lemma (ensures stable_on_t is (int_at_most k is))
  = reveal_opaque (`%grows) (grows #a)

let i_sel (#r:rid) (#a:Type) (#p:seq a -> Type) (h:mem) (m:i_seq r a p)
  : GTot (s:seq a{p s})
  = HS.sel h m

let i_read (#a:Type) (#p:Seq.seq a -> Type) (#r:rid) (m:i_seq r a p)
  : ST (s:seq a{p s})
       (requires (fun h -> True))
       (ensures (fun h0 x h1 -> h0==h1 /\ x == i_sel h0 m))
  = !m

let i_contains (#r:rid) (#a:Type) (#p:seq a -> Type) (m:i_seq r a p) (h:mem)
  : GTot Type0
  = HS.contains h m

let i_write_at_end (#a:Type) (#p:seq a -> Type) (#rgn:rid) (r:i_seq rgn a p) (x:a)
  : ST unit
       (requires (fun h -> p (Seq.snoc (i_sel h r) x)))
       (ensures (fun h0 _ h1 ->
	               i_contains r h1
		     /\ modifies_one rgn h0 h1
		     /\ modifies_ref rgn (Set.singleton (HS.as_addr r)) h0 h1
		     /\ i_sel h1 r == Seq.snoc (i_sel h0 r) x
		     /\ witnessed (i_at_least (Seq.length (i_sel h0 r)) x r)))
  =
    recall r;
    let s0 = !r in
    let n = Seq.length s0 in
    r := Seq.snoc s0 x;
    i_at_least_is_stable n x r;
    contains_snoc s0 x;
    mr_witness r (i_at_least n x r)

////////////////////////////////////////////////////////////////////////////////
//Testing invariant sequences
////////////////////////////////////////////////////////////////////////////////
private let invariant (s:seq nat) = 
  forall (i:nat) (j:nat). i < Seq.length s /\ j < Seq.length s /\ i<>j 
		 ==> Seq.index s i <> Seq.index s j
  
private val test0: r:rid -> a:m_rref r (seq nat) grows -> k:nat -> ST unit
  (requires (fun h -> k < Seq.length (HS.sel h a)))
  (ensures (fun h0 result h1 -> True))
let test0 r a k =
  let h0 = HST.get() in
  let _ = 
    let s = HS.sel h0 a in 
    at_least_is_stable k (Seq.index (HS.sel h0 a) k) a;
    Seq.contains_intro s k (Seq.index s k) in
  mr_witness a (at_least k (Seq.index (HS.sel h0 a) k) a)
  
private val itest: r:rid -> a:i_seq r nat invariant -> k:nat -> ST unit
  (requires (fun h -> k < Seq.length (i_sel h a)))
  (ensures (fun h0 result h1 -> True))
let itest r a k =
  let h0 = HST.get() in
  i_at_least_is_stable k (Seq.index (i_sel h0 a) k) a;
  mr_witness a (i_at_least k (Seq.index (i_sel h0 a) k) a)


////////////////////////////////////////////////////////////////////////////////
//Mapping functions over monotone sequences
////////////////////////////////////////////////////////////////////////////////
val un_snoc: #a: Type -> s:seq a {Seq.length s > 0} -> Tot(seq a & a)
let un_snoc #a s =
  let last = Seq.length s - 1 in
  Seq.slice s 0 last, Seq.index s last

val map: ('a -> Tot 'b) -> s:seq 'a -> Tot (seq 'b)
    (decreases (Seq.length s))
let rec map f s =
  if Seq.length s = 0 then Seq.empty
  else let prefix, last = un_snoc s in
       Seq.snoc (map f prefix) (f last)

val map_snoc: f:('a -> Tot 'b) -> s:seq 'a -> a:'a -> Lemma
  (map f (Seq.snoc s a) == Seq.snoc (map f s) (f a))
let map_snoc f s a =
  let prefix, last = un_snoc (Seq.snoc s a) in
  cut (Seq.equal prefix s)

private let op_At s1 s2 = Seq.append s1 s2

val map_append: f:('a -> Tot 'b) -> s1:seq 'a -> s2:seq 'a -> Lemma
  (requires True)
  (ensures (map f (s1@s2) == (map f s1 @ map f s2)))
  (decreases (Seq.length s2))
#reset-options "--z3rlimit 10 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"
let rec map_append f s_1 s_2 =
  if Seq.length s_2 = 0
  then (cut (Seq.equal (s_1@s_2) s_1);
        cut (Seq.equal (map f s_1 @ map f s_2) (map f s_1)))
  else (let prefix_2, last = un_snoc s_2 in
        let m_s_1 = map f s_1 in
  	let m_p_2 = map f prefix_2 in
  	let flast = f last in
  	cut (Seq.equal (s_1@s_2) (Seq.snoc (s_1@prefix_2) last));         //map f (s1@s2) = map f (snoc (s1@p) last)
  	map_snoc f (Seq.append s_1 prefix_2) last;                       //              = snoc (map f (s1@p)) (f last)
        map_append f s_1 prefix_2;                                       //              = snoc (map f s_1 @ map f p) (f last)
  	cut (Seq.equal (Seq.snoc (m_s_1 @ m_p_2) flast)
  		       (m_s_1 @ Seq.snoc m_p_2 flast));                 //              = map f s1 @ (snoc (map f p) (f last))
        map_snoc f prefix_2 last)                                       //              = map f s1 @ map f (snoc p last)

#reset-options "--z3rlimit 5"

val map_length: f:('a -> Tot 'b) -> s1:seq 'a -> Lemma
  (requires True)
  (ensures (Seq.length s1 = Seq.length (map f s1)))
  (decreases (length s1))
  [SMTPat (Seq.length (map f s1))]
let rec map_length f s1 =
  if Seq.length s1 = 0 then ()
  else let prefix, last = un_snoc s1 in
       map_length f prefix

val map_index: f:('a -> Tot 'b) -> s:seq 'a -> i:nat{i<Seq.length s} -> Lemma
  (requires True)
  (ensures (Seq.index (map f s) i == f (Seq.index s i)))
  (decreases (Seq.length s))
  [SMTPat (Seq.index (map f s) i)]
let rec map_index f s i =
  if i = Seq.length s - 1
  then ()
  else let prefix, last = un_snoc s in
       map_index f prefix i

//17-01-05 all the stuff above should go to Seq.Properties! 

let map_grows (#a:Type) (#b:Type) (f:a -> Tot b)
	      (s1:seq a) (s3:seq a)
  : Lemma (grows s1 s3
	   ==> grows (map f s1) (map f s3))
  = reveal_opaque (`%grows) (grows #a);
    reveal_opaque (`%grows) (grows #b)

let map_prefix (#a:Type) (#b:Type) (#i:rid)
	       (r:m_rref i (seq a) grows)
	       (f:a -> Tot b)
	       (bs:seq b)
	       (h:mem) =
  grows bs (map f (HS.sel h r))

//17-01-05  this applies to log_t's defined below. 
let map_prefix_stable (#a:Type) (#b:Type) (#i:rid) (r:m_rref i (seq a) grows) (f:a -> Tot b) (bs:seq b)
  :Lemma (stable_on_t r (map_prefix r f bs))
  = reveal_opaque (`%grows) (grows #a);
    reveal_opaque (`%grows) (grows #b)

let map_has_at_index (#a:Type) (#b:Type) (#i:rid)
		     (r:m_rref i (seq a) grows)
		     (f:a -> Tot b)
		     (n:nat) (v:b) (h:mem) =
    let s = HS.sel h r in
    n < Seq.length s
  /\ Seq.index (map f s) n == v

let map_has_at_index_stable (#a:Type) (#b:Type) (#i:rid)
			    (r:m_rref i (seq a) grows)
			    (f:a -> Tot b) (n:nat) (v:b)
  : Lemma (stable_on_t r (map_has_at_index r f n v))
  = reveal_opaque (`%grows) (grows #a)
		     

////////////////////////////////////////////////////////////////////////////////
//Collecting monotone sequences
////////////////////////////////////////////////////////////////////////////////

(** yields the concatenation of all sequences returned by f applied to the sequence elements *)
val collect: ('a -> Tot (seq 'b)) -> s:seq 'a -> Tot (seq 'b)
    (decreases (Seq.length s))
let rec collect f s =
  if Seq.length s = 0 then Seq.empty
  else let prefix, last = un_snoc s in
       Seq.append (collect f prefix) (f last)

val collect_snoc: f:('a -> Tot (seq 'b)) -> s:seq 'a -> a:'a -> Lemma
  (collect f (Seq.snoc s a) == Seq.append (collect f s) (f a))
let collect_snoc f s a =
  let prefix, last = un_snoc (Seq.snoc s a) in
  cut (Seq.equal prefix s)

#reset-options "--z3rlimit 20 --initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"

let collect_grows (f:'a -> Tot (seq 'b))
		  (s1:seq 'a) (s2:seq 'a)
  : Lemma (grows s1 s2 ==> grows (collect f s1) (collect f s2))
  = reveal_opaque (`%grows) (grows #'a);
    reveal_opaque (`%grows) (grows #'b);
    let rec collect_grows_aux (f:'a -> Tot (seq 'b)) (s1:seq 'a) (s2:seq 'a)
      :Lemma (requires (grows s1 s2)) (ensures (grows (collect f s1) (collect f s2)))
             (decreases (Seq.length s2))
      = if length s1 = length s2 then assert (Seq.equal s1 s2)
        else
          let s2_prefix, s2_last = un_snoc s2 in
          collect_grows_aux f s1 s2_prefix
    in
    Classical.arrow_to_impl #(grows s1 s2) #(grows (collect f s1) (collect f s2)) (fun _ -> collect_grows_aux f s1 s2)
  
let collect_prefix (#a:Type) (#b:Type) (#i:rid)
		   (r:m_rref i (seq a) grows)
		   (f:a -> Tot (seq b))
		   (bs:seq b)
		   (h:mem) =
  grows bs (collect f (HS.sel h r))

let collect_prefix_stable (#a:Type) (#b:Type) (#i:rid) (r:m_rref i (seq a) grows) (f:a -> Tot (seq b)) (bs:seq b)
  : Lemma (stable_on_t r (collect_prefix r f bs))
  = let aux : h0:mem -> h1:mem -> Lemma
      (collect_prefix r f bs h0
       /\ grows (HS.sel h0 r) (HS.sel h1 r)
       ==> collect_prefix r f bs h1) =
      fun h0 h1 ->
	  let s1 = HS.sel h0 r in
	  let s3 = HS.sel h1 r in
	  collect_grows f s1 s3
    in
    forall_intro_2 aux

let collect_has_at_index (#a:Type) (#b:Type) (#i:rid)
			 (r:m_rref i (seq a) grows)
			 (f:a -> Tot (seq b))
			 (n:nat) (v:b) (h:mem) =
    let s = HS.sel h r in
    n < Seq.length (collect f s)
  /\ Seq.index (collect f s) n == v

let collect_has_at_index_stable (#a:Type) (#b:Type) (#i:rid)
				(r:m_rref i (seq a) grows)
				(f:a -> Tot (seq b)) (n:nat) (v:b)
  : Lemma (stable_on_t r (collect_has_at_index r f n v))
  = reveal_opaque (`%grows) (grows #b);
    Classical.forall_intro_2 (collect_grows f)

////////////////////////////////////////////////////////////////////////////////
//Monotonic sequence numbers, bounded by the length of a log
////////////////////////////////////////////////////////////////////////////////
//17-01-05 the simpler variant, with an historic name; consider using uniform names below. 
type log_t (i:rid) (a:Type) = m_rref i (seq a) grows

let increases (x:int) (y:int) = b2t (x <= y)

let at_most_log_len (#l:rid) (#a:Type) (x:nat) (log:log_t l a)
    : mem -> GTot Type0
    = fun h -> x <= Seq.length (HS.sel h log)

//Note: we may want int seqn, instead of nat seqn
//because the handshake uses an initial value of -1
type seqn_val (#l:rid) (#a:Type) (i:rid) (log:log_t l a) (max:nat) =
     (x:nat{x <= max /\ witnessed (at_most_log_len x log)}) //never more than the length of the log
	 
type seqn (#l:rid) (#a:Type) (i:rid) (log:log_t l a) (max:nat) =
  m_rref i  //counter in region i
         (seqn_val i log max) //never more than the length of the log
	 increases //increasing

let at_most_log_len_stable (#l:rid) (#a:Type) (x:nat) (log:log_t l a)
  : Lemma (stable_on_t log (at_most_log_len x log))
  = reveal_opaque (`%grows) (grows #a)

let new_seqn (#a:Type) (#l:rid) (#max:nat)
  	     (i:rid) (init:nat) (log:log_t l a)
  : ST (seqn i log max)
       (requires (fun h ->
           HST.witnessed (region_contains_pred i) /\
	   init <= max /\
	   init <= Seq.length (HS.sel h log)))
       (ensures (fun h0 c h1 -> //17-01-05 unify with ralloc_post? 
		   modifies_one i h0 h1 /\
		   modifies_ref i Set.empty h0 h1 /\
		   fresh_ref c h0 h1 /\
		   HS.sel h1 c = init /\
		   FStar.Map.contains (HS.get_hmap h1) i))
  = reveal_opaque (`%grows) (grows #a);
    recall log; recall_region i;
    mr_witness log (at_most_log_len init log);
    ralloc i init

let increment_seqn (#a:Type) (#l:rid) (#max:nat)
	           (#i:rid) (#log:log_t l a) ($c:seqn i log max)
  : ST unit
       (requires (fun h ->
	  let log = HS.sel h log in
	  let n = HS.sel h c in
	  n < Seq.length log  /\
	  n + 1 <= max))
       (ensures (fun h0 _ h1 ->
	  modifies_one i h0 h1 /\
	  modifies_ref i (Set.singleton (HS.as_addr c)) h0 h1 /\
	  HS.sel h1 c = HS.sel h0 c + 1))
  = reveal_opaque (`%grows) (grows #a);
    recall c; recall log;
    let n = !c + 1 in
    mr_witness log (at_most_log_len n log);
    c := n

let testify_seqn (#a:Type0) (#i:rid) (#l:rid) (#log:log_t l a) (#max:nat) (ctr:seqn i log max)
  : ST unit
       (requires (fun h -> True))
       (ensures (fun h0 _ h1 ->
	   h0==h1 /\
	   at_most_log_len (HS.sel h1 ctr) log h1))
  = let n = !ctr in
    testify (at_most_log_len n log)

private let test (i:rid) (l:rid) (a:Type0) (log:log_t l a) //(p:(nat -> Type))
         (r:seqn i log 8) (h:mem)
  = assert (HS.sel h r = Heap.sel (FStar.Map.sel (HS.get_hmap h) i) (HS.as_ref r))
