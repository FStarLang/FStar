module FStar.Monotonic.Seq

open FStar.Seq
open FStar.SeqProperties
module HH   = FStar.HyperHeap
module MR   = FStar.Monotonic.RRef
module SeqP = FStar.SeqProperties

let forall_intro (#a:Type) (#p:(x:a -> GTot Type0)) ($f:(x:a -> Lemma (p x)))
  : Lemma (forall (x:a). p x)
  = FStar.Classical.forall_intro f

(* Some basic stuff, should be moved to FStar.Squash, probably *)
let forall_intro_2 (#a:Type) (#b:(a -> Type)) (#p:(x:a -> b x -> GTot Type0))
                  ($f: (x:a -> y:b x -> Lemma (p x y)))
  : Lemma (forall (x:a) (y:b x). p x y)
  = let g : x:a -> Lemma (forall (y:b x). p x y) = fun x -> forall_intro (f x) in
    forall_intro g

let forall_intro_3 (#a:Type) (#b:(a -> Type)) (#c:(x:a -> y:b x -> Type)) (#p:(x:a -> y:b x -> z:c x y -> Type0))
		  ($f: (x:a -> y:b x -> z:c x y -> Lemma (p x y z)))
  : Lemma (forall (x:a) (y:b x) (z:c x y). p x y z)
  = let g : x:a -> Lemma (forall (y:b x) (z:c x y). p x y z) = fun x -> forall_intro_2 (f x) in
    forall_intro g

let exists_intro (#a:Type) (p:(a -> Type)) (witness:a)
  : Lemma (requires (p witness))
	  (ensures (exists (x:a). p x))
  = ()

let exists_elim (#a:Type) (#p:(a -> Type)) (#r:Type) ($f:(x:a -> Lemma (p x ==> r)))
  : Lemma ((exists (x:a). p x) ==> r)
  = forall_intro f

let exists_elim_2 (#a:Type) (#p:(a -> Type)) (#b:Type) (#q:(b -> Type)) (#r:Type) 
		 ($f:(x:a -> y:b -> Lemma ((p x /\ q y) ==> r)))
  : Lemma (((exists (x:a). p x) /\ (exists (y:b). q y)) ==> r)
  = forall_intro_2 f

////////////////////////////////////////////////////////////////////////////////

abstract let seq_extension (#a:Type) (s1:seq a) (s2:seq a) (s3:seq a) =
  equal s3 (append s1 s2)
  
abstract let grows (#a:Type) (s1:seq a) (s3:seq a) =
  exists (s2:seq a). seq_extension s1 s2 s3
  
let seq_extension_reflexive (#a:Type) (s:seq a) 
  : Lemma (ensures (grows s s)) 
  = exists_intro (fun w -> seq_extension s w s) (Seq.createEmpty #a)

let seq_extension_transitive (s1:seq 'a) (s2:seq 'a) (s3:seq 'a) (s1':seq 'a) (s2':seq 'a) 
  : Lemma ((seq_extension s1 s1' s2 /\ seq_extension s2 s2' s3)
            ==> seq_extension s1 (Seq.append s1' s2') s3) 
  = ()

let seq_extends_to_transitive_aux (s1:seq 'a) (s2:seq 'a) (s3:seq 'a) (s1':seq 'a) (s2':seq 'a)
  : Lemma ((seq_extension s1 s1' s2 /\ seq_extension s2 s2' s3)
            ==> grows s1 s3) 
  = seq_extension_transitive s1 s2 s3 s1' s2'

let grows_transitive (s1:seq 'a) (s2:seq 'a) (s3:seq 'a)
  : Lemma ((grows s1 s2 /\ grows s2 s3)
           ==> grows s1 s3) 
  = exists_elim_2 (seq_extends_to_transitive_aux s1 s2 s3)

open FStar.Monotonic.RRef
open FStar.HyperHeap

let lemma_grows_monotone (#a:Type)
  : Lemma (monotonic (seq a) (grows #a))
  = forall_intro (seq_extension_reflexive #a);
    forall_intro_3 (grows_transitive #a)

let snoc (s:seq 'a) (x:'a) 
  : Tot (seq 'a) 
  = Seq.append s (Seq.create 1 x)

let lemma_snoc_extends (s:seq 'a) (x:'a)
  : Lemma (requires True)
	  (ensures (grows s (SeqP.snoc s x)))
	  [SMTPat (grows s (SeqP.snoc s x))]
  = ()

let lemma_mem_snoc (#a:eqtype) (s:seq a) (x:a)
  : Lemma (ensures (SeqProperties.mem x (SeqP.snoc s x)))
  = SeqProperties.lemma_append_count s (Seq.create 1 x)

let alloc_mref_seq (#a:Type) (r:FStar.HyperHeap.rid) (init:seq a)
  : ST (m_rref r (seq a) grows)
       (requires (fun _ -> True))
       (ensures (fun h0 m h1 ->
	 m_contains m h1 /\
	 m_sel h1 m == init /\
	 FStar.ST.ralloc_post r init h0 (as_rref m) h1))
  = lemma_grows_monotone #a;
    FStar.Monotonic.RRef.m_alloc r init

let mem (#a:eqtype) (#i:rid) (x:a) (r:m_rref i (seq a) grows) (h:t)
  : GTot Type0
  = b2t (SeqProperties.mem x (m_sel h r))

let at_least (#a:eqtype) (#i:rid) (n:nat) (x:a) (r:m_rref i (seq a) grows) (h:t) =
      mem x r h
      /\ Seq.length (m_sel h r) > n
      /\ Seq.index (m_sel h r) n = x

let at_least_is_stable (#a:eqtype) (#i:rid) (n:nat) (x:a) (r:m_rref i (seq a) grows)
  : Lemma (ensures stable_on_t r (at_least n x r))
  = let at_least_is_stable_aux:
		     h0:t
		   -> h1:t
		   -> Lemma ((at_least n x r h0
			    /\ grows (m_sel h0 r) (m_sel h1 r))
			    ==> at_least n x r h1) =
       fun h0 h1 -> forall_intro_2 (lemma_mem_append #a) in
    forall_intro_2 at_least_is_stable_aux

let write_at_end (#a:eqtype) (#i:rid) (r:m_rref i (seq a) grows) (x:a)
  : ST unit
       (requires (fun h -> True))
       (ensures (fun h0 _ h1 ->
	               m_contains r h1
		     /\ modifies_one i h0 h1
		     /\ modifies_rref i !{as_ref (as_rref r)} h0 h1
		     /\ m_sel h1 r == SeqP.snoc (m_sel h0 r) x
		     /\ witnessed (at_least (Seq.length (m_sel h0 r)) x r)))
  =
    m_recall r;
    let s0 = m_read r in
    let n = Seq.length s0 in
    m_write r (SeqP.snoc s0 x);
    at_least_is_stable n x r;
    lemma_mem_snoc s0 x;
    witness r (at_least n x r)

////////////////////////////////////////////////////////////////////////////////
//Monotone sequences with invariants
////////////////////////////////////////////////////////////////////////////////

let i_seq (r:rid) (a:Type) (p:seq a -> Type) = m_rref r (s:seq a{p s}) grows

let alloc_mref_iseq (#a:Type) (p:seq a -> Type) (r:FStar.HyperHeap.rid) (init:seq a{p init})
  : ST (i_seq r a p)
       (requires (fun _ -> True))
       (ensures (fun h0 m h1 -> FStar.ST.ralloc_post r init h0 (as_rref m) h1))
  = lemma_grows_monotone #a;
    FStar.Monotonic.RRef.m_alloc r init

let i_mem (#r:rid) (#a:eqtype) (#p:(seq a -> Type)) (x:a) (m:i_seq r a p) (h:t)
  : GTot Type0
  = b2t (SeqProperties.mem x (m_sel h m))

let i_at_least (#r:rid) (#a:eqtype) (#p:(seq a -> Type)) (n:nat) (x:a) (m:i_seq r a p) (h:t) =
      i_mem x m h
      /\ Seq.length (m_sel h m) > n
      /\ Seq.index (m_sel h m) n = x

let i_at_least_is_stable (#r:rid) (#a:eqtype) (#p:seq a -> Type) (n:nat) (x:a) (m:i_seq r a p)
  : Lemma (ensures stable_on_t m (i_at_least n x m))
  = let at_least_is_stable_aux:
		     h0:t
		   -> h1:t
		   -> Lemma ((i_at_least n x m h0
			    /\ grows (m_sel h0 m) (m_sel h1 m))
			    ==> i_at_least n x m h1) =
       fun h0 h1 -> forall_intro_2 (lemma_mem_append #a) in
    forall_intro_2 at_least_is_stable_aux

let int_at_most #r #a #p (x:int) (is:i_seq r a p) (h:HH.t) =
  b2t (x < Seq.length (m_sel h is))

let int_at_most_is_stable (#r:rid) (#a:Type) (#p:seq a -> Type) (is:i_seq r a p) (k:int)
  : Lemma (ensures stable_on_t is (int_at_most k is))
  = ()

let i_sel (#r:rid) (#a:Type) (#p:seq a -> Type) (h:HH.t) (m:i_seq r a p)
  : GTot (s:seq a{p s})
  = m_sel h m

let i_read (#r:rid) (#a:Type) (#p:Seq.seq a -> Type) (m:i_seq r a p)
  : ST (s:seq a{p s})
       (requires (fun h -> True))
       (ensures (fun h0 x h1 -> h0==h1 /\ x == i_sel h0 m))
  = MR.m_read m

let i_contains (#r:rid) (#a:Type) (#p:seq a -> Type) (m:i_seq r a p) (h:HH.t)
  : GTot bool
  = m_contains m h

let i_write_at_end (#rgn:rid) (#a:eqtype) (#p:seq a -> Type) (r:i_seq rgn a p) (x:a)
  : ST unit
       (requires (fun h -> p (SeqP.snoc (i_sel h r) x)))
       (ensures (fun h0 _ h1 ->
	               i_contains r h1
		     /\ modifies_one rgn h0 h1
		     /\ modifies_rref rgn !{as_ref (as_rref r)} h0 h1
		     /\ i_sel h1 r == SeqP.snoc (i_sel h0 r) x
		     /\ witnessed (i_at_least (Seq.length (i_sel h0 r)) x r)))
  =
    m_recall r;
    let s0 = m_read r in
    let n = Seq.length s0 in
    m_write r (SeqP.snoc s0 x);
    i_at_least_is_stable n x r;
    lemma_mem_snoc s0 x;
    witness r (i_at_least n x r)

////////////////////////////////////////////////////////////////////////////////
//Testing invariant sequences
////////////////////////////////////////////////////////////////////////////////
let invariant (s:seq nat) = 
  forall (i:nat) (j:nat). i < Seq.length s /\ j < Seq.length s /\ i<>j 
		 ==> Seq.index s i <> Seq.index s j
  
val test0: r:rid -> a:m_rref r (seq nat) grows -> k:nat -> ST unit
  (requires (fun h -> k < Seq.length (m_sel h a)))
  (ensures (fun h0 result h1 -> True))
let test0 r a k =
  let h0 = ST.get() in
  at_least_is_stable k (Seq.index (m_sel h0 a) k) a;
  MR.witness a (at_least k (Seq.index (m_sel h0 a) k) a)
  
val itest: r:rid -> a:i_seq r nat invariant -> k:nat -> ST unit
  (requires (fun h -> k < Seq.length (i_sel h a)))
  (ensures (fun h0 result h1 -> True))
let itest r a k =
  let h0 = ST.get() in
  i_at_least_is_stable k (Seq.index (i_sel h0 a) k) a;
  MR.witness a (i_at_least k (Seq.index (i_sel h0 a) k) a)

(* let test_alloc (#a:Type0) (p:seq a -> Type) (r:FStar.HyperHeap.rid) (init:seq a{p init}) =  *)
(*   let is = alloc_mref_iseq p r init in *)
(*   let h = get () in  *)
(*   assert (i_sel h is == init) *)

////////////////////////////////////////////////////////////////////////////////
//Mapping functions over monotone sequences
////////////////////////////////////////////////////////////////////////////////
val un_snoc: #a: Type -> s:seq a {Seq.length s > 0} -> Tot(seq a * a)
let un_snoc #a s =
  let last = Seq.length s - 1 in
  Seq.slice s 0 last, Seq.index s last

val map: ('a -> Tot 'b) -> s:seq 'a -> Tot (seq 'b)
    (decreases (Seq.length s))
let rec map f s =
  if Seq.length s = 0 then Seq.createEmpty
  else let prefix, last = un_snoc s in
       SeqP.snoc (map f prefix) (f last)

val map_snoc: f:('a -> Tot 'b) -> s:seq 'a -> a:'a -> Lemma
  (map f (SeqP.snoc s a) == SeqP.snoc (map f s) (f a))
let map_snoc f s a =
  let prefix, last = un_snoc (SeqP.snoc s a) in
  cut (Seq.equal prefix s)

private let op_At s1 s2 = Seq.append s1 s2

val map_append: f:('a -> Tot 'b) -> s1:seq 'a -> s2:seq 'a -> Lemma
  (requires True)
  (ensures (map f (s1@s2) == (map f s1 @ map f s2)))
  (decreases (Seq.length s2))
#reset-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"
let rec map_append f s_1 s_2 =
  if Seq.length s_2 = 0
  then (cut (Seq.equal (s_1@s_2) s_1);
        cut (Seq.equal (map f s_1 @ map f s_2) (map f s_1)))
  else (let prefix_2, last = un_snoc s_2 in
        let m_s_1 = map f s_1 in
  	let m_p_2 = map f prefix_2 in
  	let flast = f last in
  	cut (Seq.equal (s_1@s_2) (SeqP.snoc (s_1@prefix_2) last));         //map f (s1@s2) = map f (snoc (s1@p) last)
  	map_snoc f (Seq.append s_1 prefix_2) last;                       //              = snoc (map f (s1@p)) (f last)
        map_append f s_1 prefix_2;                                       //              = snoc (map f s_1 @ map f p) (f last)
  	cut (Seq.equal (SeqP.snoc (m_s_1 @ m_p_2) flast)
  		       (m_s_1 @ SeqP.snoc m_p_2 flast));                 //              = map f s1 @ (snoc (map f p) (f last))
        map_snoc f prefix_2 last)                                       //              = map f s1 @ map f (snoc p last)

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
       
let map_grows (f:'a -> Tot 'b)
	      (s1:seq 'a) (s3:seq 'a) (s2:seq 'a)
  : Lemma (seq_extension s1 s2 s3
	   ==> grows (map f s1) (map f s3))
  = map_append f s1 s2

let map_prefix (#a:Type) (#b:Type) (#i:rid)
	       (r:m_rref i (seq a) grows)
	       (f:a -> Tot b)
	       (bs:seq b)
	       (h:HH.t) =
  grows bs (map f (MR.m_sel h r))

let map_prefix_stable (#a:Type) (#b:Type) (#i:rid) (r:m_rref i (seq a) grows) (f:a -> Tot b) (bs:seq b)
  : Lemma (MR.stable_on_t r (map_prefix r f bs))
  = let aux : h0:HH.t -> h1:HH.t -> Lemma
      (map_prefix r f bs h0
       /\ grows (MR.m_sel h0 r) (MR.m_sel h1 r)
       ==> map_prefix r f bs h1) =
      fun h0 h1 ->
	  let s1 = MR.m_sel h0 r in
	  let s3 = MR.m_sel h1 r in
	  exists_elim (map_grows f s1 s3);
	  grows_transitive bs (map f s1) (map f s3) in
    forall_intro_2 aux

let map_has_at_index (#a:Type) (#b:Type) (#i:rid)
		     (r:m_rref i (seq a) grows)
		     (f:a -> Tot b)
		     (n:nat) (v:b) (h:HH.t) =
    let s = MR.m_sel h r in
    n < Seq.length s
  /\ Seq.index (map f s) n == v

let map_has_at_index_stable (#a:Type) (#b:Type) (#i:rid)
			    (r:m_rref i (seq a) grows)
			    (f:a -> Tot b) (n:nat) (v:b)
  : Lemma (MR.stable_on_t r (map_has_at_index r f n v))
  = ()
		     

////////////////////////////////////////////////////////////////////////////////
//Collecting monotone sequences
////////////////////////////////////////////////////////////////////////////////

val collect: ('a -> Tot (seq 'b)) -> s:seq 'a -> Tot (seq 'b)
    (decreases (Seq.length s))
let rec collect f s =
  if Seq.length s = 0 then Seq.createEmpty
  else let prefix, last = un_snoc s in
       Seq.append (collect f prefix) (f last)

val collect_snoc: f:('a -> Tot (seq 'b)) -> s:seq 'a -> a:'a -> Lemma
  (collect f (SeqP.snoc s a) == Seq.append (collect f s) (f a))
let collect_snoc f s a =
  let prefix, last = un_snoc (SeqP.snoc s a) in
  cut (Seq.equal prefix s)

val collect_append: f:('a -> Tot (seq 'b)) -> s1:seq 'a -> s2:seq 'a -> Lemma
  (requires True)
  (ensures (collect f (s1@s2) == (collect f s1 @ collect f s2)))
  (decreases (Seq.length s2))
#reset-options "--initial_fuel 1 --max_fuel 1 --initial_ifuel 1 --max_ifuel 1"
let rec collect_append f s_1 s_2 =
  if Seq.length s_2 = 0
  then (cut (Seq.equal (s_1@s_2) s_1);
        cut (Seq.equal (collect f s_1 @ collect f s_2) (collect f s_1)))
  else (let prefix_2, last = un_snoc s_2 in
        let m_s_1 = collect f s_1 in
  	let m_p_2 = collect f prefix_2 in
  	let flast = f last in
  	cut (Seq.equal (s_1@s_2) (SeqP.snoc (s_1@prefix_2) last));         //map f (s1@s2) = map f (snoc (s1@p) last)
  	collect_snoc f (Seq.append s_1 prefix_2) last;                       //              = snoc (map f (s1@p)) (f last)
        collect_append f s_1 prefix_2;                                       //              = snoc (map f s_1 @ map f p) (f last)
  	cut (Seq.equal ((m_s_1 @ m_p_2) @ flast)
  		       (m_s_1 @ (m_p_2 @ flast)));                 //              = map f s1 @ (snoc (map f p) (f last))
        collect_snoc f prefix_2 last)                                       //              = map f s1 @ map f (snoc p last)

let collect_grows_aux (f:'a -> Tot (seq 'b))
		  (s1:seq 'a) (s3:seq 'a) (s2:seq 'a)
  : Lemma (seq_extension s1 s2 s3
	   ==> grows (collect f s1) (collect f s3))
  = collect_append f s1 s2

let collect_grows (f:'a -> Tot (seq 'b))
		  (s1:seq 'a) (s2:seq 'a)
  : Lemma (grows s1 s2 ==> grows (collect f s1) (collect f s2))
  = exists_elim (collect_grows_aux f s1 s2)
  
let collect_prefix (#a:Type) (#b:Type) (#i:rid)
		   (r:m_rref i (seq a) grows)
		   (f:a -> Tot (seq b))
		   (bs:seq b)
		   (h:HH.t) =
  grows bs (collect f (MR.m_sel h r))

let collect_prefix_stable (#a:Type) (#b:Type) (#i:rid) (r:m_rref i (seq a) grows) (f:a -> Tot (seq b)) (bs:seq b)
  : Lemma (MR.stable_on_t r (collect_prefix r f bs))
  = let aux : h0:HH.t -> h1:HH.t -> Lemma
      (collect_prefix r f bs h0
       /\ grows (MR.m_sel h0 r) (MR.m_sel h1 r)
       ==> collect_prefix r f bs h1) =
      fun h0 h1 ->
	  let s1 = MR.m_sel h0 r in
	  let s3 = MR.m_sel h1 r in
	  collect_grows f s1 s3;
	  grows_transitive bs (collect f s1) (collect f s3) in
    forall_intro_2 aux


let collect_has_at_index (#a:Type) (#b:Type) (#i:rid)
			 (r:m_rref i (seq a) grows)
			 (f:a -> Tot (seq b))
			 (n:nat) (v:b) (h:HH.t) =
    let s = MR.m_sel h r in
    n < Seq.length (collect f s)
  /\ Seq.index (collect f s) n == v

let collect_has_at_index_stable (#a:Type) (#b:Type) (#i:rid)
				(r:m_rref i (seq a) grows)
				(f:a -> Tot (seq b)) (n:nat) (v:b)
  : Lemma (MR.stable_on_t r (collect_has_at_index r f n v))
  = let aux : h0:HH.t -> h1:HH.t -> Lemma
      (collect_has_at_index r f n v h0
       /\ grows (MR.m_sel h0 r) (MR.m_sel h1 r)
       ==> collect_has_at_index r f n v h1) =
      fun h0 h1 ->
	  let s1 = MR.m_sel h0 r in
	  let s3 = MR.m_sel h1 r in
	  let aux2 : s2:seq a -> Lemma ((s1@s2 == s3 /\ collect_has_at_index r f n v h0)
				       ==> collect_has_at_index r f n v h1)
	      = fun s2 -> collect_append f s1 s2 in
	  exists_elim aux2 in
    forall_intro_2 aux


////////////////////////////////////////////////////////////////////////////////
//Monotonic sequence numbers, bounded by the length of a log
////////////////////////////////////////////////////////////////////////////////

//16-09-12 aliased to i_seq, so that we can refine the whole log contents and have sequence numbers. 
type log_t (r:rid) (a:Type) = i_seq r a (fun (s:seq a) -> True) 

let increases (x:int) (y:int) = b2t (x <= y)

let at_most_log_len (#l:rid) (#a:Type) (#p:seq a -> Type) (x:nat) (log:i_seq l a p)
    : HyperHeap.t -> GTot Type0
    = fun h -> x <= Seq.length (m_sel h log)

//Note: we may want int seqn, instead of nat seqn
//because the handshake uses an initial value of -1
type seqn_val (#l:rid) (#a:Type) (#p:seq a -> Type) (i:rid) (log:i_seq l a p) (max:nat) =
     (x:nat{x <= max /\ witnessed (at_most_log_len x log)}) //never more than the length of the log
	 
type seqn (#l:rid) (#a:Type) (#p:seq a -> Type) (i:rid) (log:i_seq l a p) (max:nat) =
  m_rref i  //counter in region i
         (seqn_val i log max) //never more than the length of the log
	 increases //increasing

let monotonic_increases (x:unit)
  : Lemma (monotonic int increases)
  = ()

let at_most_log_len_stable (#l:rid) (#a:Type) (#p:seq a -> Type) (x:nat) (l:i_seq l a p)
  : Lemma (stable_on_t l (at_most_log_len x l))
  = ()

(* assume val gcut : f:(unit -> GTot Type){f ()} -> Tot unit *)

let new_seqn (#l:rid) (#a:Type) (#p:seq a -> Type) (i:rid) (init:nat) (max:nat) (log:i_seq l a p)
  : ST (seqn i log max)
       (requires (fun h ->
	   init <= max /\
	   init <= Seq.length (m_sel h log)))
       (ensures (fun h0 c h1 ->
		   modifies_one i h0 h1 /\
		   modifies_rref i TSet.empty h0 h1 /\
		   m_fresh c h0 h1 /\
		   m_sel h1 c = init /\
		   Map.contains h1 i))
  =
    m_recall log; recall_region i;
    witness log (at_most_log_len init log);
    m_alloc i init

//16-09-13 failed to make p implicit at callsite.
let increment_seqn (#l:rid) (#a:Type) (p:seq a -> Type) (#max:nat)
		   (#i:rid) (#log:i_seq l a p) ($c:seqn i log max)
  : ST unit
       (requires (fun h ->
	  let log = m_sel h log in
	  let n = m_sel h c in
	  n < Seq.length log  /\
	  n + 1 <= max))
       (ensures (fun h0 _ h1 ->
	  modifies_one i h0 h1 /\
	  modifies_rref i !{as_ref (as_rref c)} h0 h1 /\
	  m_sel h1 c = m_sel h0 c + 1))
  = m_recall c; m_recall log;
    let n = m_read c + 1 in
    witness log (at_most_log_len n log);
    m_write c n

let testify_seqn (#i:rid) (#l:rid) (#a:Type0) (#p:seq a -> Type) (#log:i_seq l a p) (#max:nat) (ctr:seqn i log max)
  : ST unit
       (requires (fun h -> True))
       (ensures (fun h0 _ h1 ->
	   h0==h1 /\
	   at_most_log_len (m_sel h1 ctr) log h1))
  = let n = m_read ctr in
    testify (at_most_log_len n log)

let test (i:rid) (l:rid) (a:Type0) (log:log_t l a) //(p:(nat -> Type))
         (r:seqn i log 8) (h:HyperHeap.t)
  = //assert (m_sel2 h r = HyperHeap.sel h (as_rref r));
    assert (m_sel h r = HyperHeap.sel h (as_rref r));
    assert (m_sel #_ #(seqn_val i log 8) #_ h r = HyperHeap.sel h (as_rref r))


(* TODO: this fails with a silly inconsistent qualifier error *)
(* logic val mem_index: #a:Type -> #i:rid -> n:nat -> x:a -> r:m_rref i (seq a) grows -> t -> GTot Type0 *)
(* logic let mem_index #a #i n x r h =  *)
(*       mem x r h *)
(*       /\ Seq.length (m_sel h r) > n *)
(*       /\ Seq.index (m_sel h r) n = x *)
