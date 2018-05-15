module LowStar.Buffer

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module U32 = FStar.UInt32
module G = FStar.Ghost
module Seq = FStar.Seq

val buffer (a: Type0) : Tot Type0

(* Null pointer *)

val g_is_null (#a: Type) (b: buffer a) : GTot bool

val null (#a: Type) : Tot (b: buffer a { g_is_null b } )

val null_unique (#a: Type) (b: buffer a) : Lemma
  (g_is_null b <==> b == null)

(* Memory safety *)

val unused_in (#a: Type) (b: buffer a) (h: HS.mem) : GTot Type0

val live (#a: Type) (h: HS.mem) (b: buffer a) : GTot Type0

val live_null (a: Type) (h: HS.mem) : Lemma
  (live h (null #a))

let live_is_null (#a: Type) (h: HS.mem) (b: buffer a) : Lemma
  (requires (g_is_null b == true))
  (ensures (live h b))
  [SMTPat (live h b)]
= null_unique b;
  live_null a h

val live_not_unused_in (#a: Type) (h: HS.mem) (b: buffer a) : Lemma
  (requires (live h b /\ b `unused_in` h))
  (ensures False)

(* necessary to isolate the pattern because of unification *)
let live_not_unused_in' (#a: Type) (h: HS.mem) (b: buffer a) : Lemma
  (requires (live h b /\ b `unused_in` h))
  (ensures False)
  [SMTPat (live h b); SMTPat (b `unused_in` h)]
= live_not_unused_in h b

(* Regions and addresses, for allocation purposes *)

val frameOf (#a: Type) (b: buffer a) : GTot HS.rid

val as_addr (#a: Type) (b: buffer a) : GTot nat

val unused_in_equiv (#a: Type) (b: buffer a) (h: HS.mem) : Lemma
  (ensures (unused_in b h <==> (HS.live_region h (frameOf b) ==> as_addr b `Heap.addr_unused_in` (Map.sel h.HS.h (frameOf b)))))

val live_region_frameOf (#a: Type) (h: HS.mem) (b: buffer a) : Lemma
  (requires (live h b))
  (ensures (HS.live_region h (frameOf b)))
  [SMTPatOr [
    [SMTPat (live h b)];
    [SMTPat (HS.live_region h (frameOf b))];
  ]]

(* Contents *)

val len (#a: Type) (b: buffer a) : GTot U32.t

let length (#a: Type) (b: buffer a) : GTot nat = U32.v (len b)

val len_null (a: Type) : Lemma
  (len (null #a) == 0ul)

let length_null_1 (#a: Type) (b: buffer a) : Lemma
  (requires (length b <> 0))
  (ensures (g_is_null b == false))
  [SMTPat (length b)]
= len_null a;
  null_unique b

let length_null_2 (#a: Type) (b: buffer a) : Lemma
  (requires (g_is_null b == true))
  (ensures (length b == 0))
  [SMTPat (g_is_null b)]
= len_null a;
  null_unique b

val as_seq (#a: Type) (h: HS.mem) (b: buffer a) : GTot (Seq.seq a)

val length_as_seq (#a: Type) (h: HS.mem) (b: buffer a) : Lemma
  (Seq.length (as_seq h b) == length b)
  [SMTPat (Seq.length (as_seq h b))]

(* Inclusion *)

val includes (#a: Type) (larger smaller: buffer a) : GTot Type0

val includes_live (#a: Type) (h: HS.mem) (larger smaller: buffer a) : Lemma
  (requires (larger `includes` smaller))
  (ensures (live h larger <==> live h smaller))

val includes_as_seq (#a: Type) (h1 h2: HS.mem) (larger smaller: buffer a) : Lemma
  (requires (larger `includes` smaller /\ as_seq h1 larger == as_seq h2 larger))
  (ensures (as_seq h1 smaller == as_seq h2 smaller))

val includes_refl (#a: Type) (x: buffer a) : Lemma
  (includes x x)

val includes_trans (#a: Type) (x y z: buffer a) : Lemma
  (requires (x `includes` y /\ y `includes` z))
  (ensures (x `includes` z))
  [SMTPatOr [
    [SMTPat (x `includes` y); SMTPat (y `includes` z)];
    [SMTPat (x `includes` y); SMTPat (x `includes` z)];
    [SMTPat (y `includes` z); SMTPat (x `includes` z)];
  ]]

val includes_frameOf_as_addr (#a: Type) (larger smaller: buffer a) : Lemma
  (requires (larger `includes` smaller))
  (ensures (g_is_null larger == g_is_null smaller /\ frameOf larger == frameOf smaller /\ as_addr larger == as_addr smaller))
  [SMTPat (larger `includes` smaller)]

(* Sub-buffers *)

val gsub (#a: Type) (b: buffer a) (i: U32.t) (len: U32.t) : Ghost (buffer a)
  (requires (U32.v i + U32.v len <= length b))
  (ensures (fun y -> True))

val live_gsub (#a: Type) (h: HS.mem) (b: buffer a) (i: U32.t) (len: U32.t) : Lemma
  (requires (U32.v i + U32.v len <= length b))
  (ensures (live h (gsub b i len) <==> live h b))
  [SMTPat (live h (gsub b i len))]

val includes_gsub (#a: Type) (b: buffer a) (i: U32.t) (len: U32.t) : Lemma
  (requires (U32.v i + U32.v len <= length b))
  (ensures (b `includes` gsub b i len))
  [SMTPat (gsub b i len)]

val len_gsub (#a: Type) (b: buffer a) (i: U32.t) (len': U32.t) : Lemma
  (requires (U32.v i + U32.v len' <= length b))
  (ensures (len (gsub b i len') == len'))
  [SMTPatOr [
    [SMTPat (len (gsub b i len'))];
    [SMTPat (length (gsub b i len'))];
  ]]

val gsub_gsub (#a: Type) (b: buffer a) (i1: U32.t) (len1: U32.t) (i2: U32.t) (len2: U32.t) : Lemma
  (requires (U32.v i1 + U32.v len1 <= length b /\ U32.v i2 + U32.v len2 <= U32.v len1))
  (ensures (
    U32.v i1 + U32.v len1 <= length b /\ U32.v i2 + U32.v len2 <= U32.v len1 /\
    gsub (gsub b i1 len1) i2 len2 == gsub b (U32.add i1 i2) len2
  ))
  [SMTPat (gsub (gsub b i1 len1) i2 len2)]

val gsub_zero_length (#a: Type) (b: buffer a) : Lemma
  (b == gsub b 0ul (len b))

val as_seq_gsub (#a: Type) (h: HS.mem) (b: buffer a) (i: U32.t) (len: U32.t) : Lemma
  (requires (U32.v i + U32.v len <= length b))
  (ensures (as_seq h (gsub b i len) == Seq.slice (as_seq h b) (U32.v i) (U32.v i + U32.v len)))
  [SMTPat (as_seq h (gsub b i len))]

(* Disjointness *)

val disjoint (#a1 #a2: Type) (b1: buffer a1) (b2: buffer a2) : GTot Type0

val disjoint_sym (#a1 #a2: Type) (b1: buffer a1) (b2: buffer a2) : Lemma
  (disjoint b1 b2 <==> disjoint b2 b1)
  [SMTPat (disjoint b1 b2)]

val disjoint_includes_l (#a1 #a2: Type) (b1 b1' : buffer a1) (b2: buffer a2) : Lemma
  (requires (includes b1 b1' /\ disjoint b1 b2))
  (ensures (disjoint b1' b2))
  [SMTPat (disjoint b1' b2); SMTPat (includes b1 b1')] 

val disjoint_includes_r (#a1 #a2: Type) (b1 : buffer a1) (b2 b2': buffer a2) : Lemma
  (requires (includes b2 b2' /\ disjoint b1 b2))
  (ensures (disjoint b1 b2'))
  [SMTPat (disjoint b1 b2'); SMTPat (includes b2 b2')] 

val live_unused_in_disjoint (#a1 #a2: Type) (h: HS.mem) (b1: buffer a1) (b2: buffer a2) : Lemma
  (requires (live h b1 /\ (unused_in b2 h)))
  (ensures (disjoint b1 b2))
  [SMTPatOr [
    [SMTPat (live h b1); SMTPat (disjoint b1 b2)];
    [SMTPat (live h b1); SMTPat (unused_in b2 h)];
    [SMTPat (unused_in b2 h); SMTPat (disjoint b1 b2)];
  ]]

val as_addr_disjoint (#a1 #a2: Type) (b1: buffer a1) (b2: buffer a2) : Lemma
  (requires (frameOf b1 <> frameOf b2 \/ as_addr b1 <> as_addr b2))
  (ensures (disjoint b1 b2))
  [SMTPatOr [
    [SMTPat (disjoint b1 b2)];
    [SMTPat (frameOf b1); SMTPat (frameOf b2)];
    [SMTPat (as_addr b1); SMTPat (as_addr b2)];
  ]]

val gsub_disjoint (#a: Type) (b: buffer a) (i1 len1 i2 len2: U32.t) : Lemma
  (requires (
    U32.v i1 + U32.v len1 <= length b /\
    U32.v i2 + U32.v len2 <= length b /\
    (U32.v i1 + U32.v len1 <= U32.v i2 \/ U32.v i2 + U32.v len2 <= U32.v i1)
  ))
  (ensures (disjoint (gsub b i1 len1) (gsub b i2 len2)))
  [SMTPat (disjoint (gsub b i1 len1) (gsub b i2 len2))]

val pointer_distinct_sel_disjoint
  (#a: Type)
  (b1: buffer a)
  (b2: buffer a)
  (h: HS.mem)
: Lemma
  (requires (
    live h b1 /\
    live h b2 /\
    length b1 == 1 /\
    length b2 == 1 /\
    Seq.index (as_seq h b1) 0 =!= Seq.index (as_seq h b2) 0
  ))
  (ensures (
    disjoint b1 b2
  ))


(* Untyped view of buffers, used only to implement the generic modifies clause. DO NOT USE in client code. *)

val abuffer' (region: HS.rid) (addr: nat) : Tot Type0

inline_for_extraction
let abuffer (region: HS.rid) (addr: nat) : Tot Type0 = G.erased (abuffer' region addr)

val abuffer_preserved (#r: HS.rid) (#a: nat) (b: abuffer r a) (h h' : HS.mem) : GTot Type0

val abuffer_preserved_refl (#r: HS.rid) (#a: nat) (b: abuffer r a) (h : HS.mem) : Lemma
  (abuffer_preserved b h h)

val abuffer_preserved_trans (#r: HS.rid) (#a: nat) (b: abuffer r a) (h1 h2 h3 : HS.mem) : Lemma
  (requires (abuffer_preserved b h1 h2 /\ abuffer_preserved b h2 h3))
  (ensures (abuffer_preserved b h1 h3))

val same_mreference_abuffer_preserved
  (#r: HS.rid)
  (#a: nat)
  (b: abuffer r a)
  (h1 h2: HS.mem)
  (f: (
    (a' : Type) ->
    (pre: Preorder.preorder a') ->
    (r': HS.mreference a' pre) ->
    Lemma
    (requires (h1 `HS.contains` r' /\ r == HS.frameOf r' /\ a == HS.as_addr r'))
    (ensures (h2 `HS.contains` r' /\ h1 `HS.sel` r' == h2 `HS.sel` r'))
  ))
: Lemma
  (abuffer_preserved b h1 h2)

val addr_unused_in_abuffer_preserved
  (#r: HS.rid)
  (#a: nat)
  (b: abuffer r a)
  (h1 h2: HS.mem)
: Lemma
  (requires (HS.live_region h1 r ==> a `Heap.addr_unused_in` (Map.sel h1.HS.h r)))
  (ensures (abuffer_preserved b h1 h2))

val abuffer_of_buffer (#t: Type) (b: buffer t) : Tot (abuffer (frameOf b) (as_addr b))

val abuffer_preserved_elim (#t: Type) (b: buffer t) (h h' : HS.mem) : Lemma
  (requires (abuffer_preserved #(frameOf b) #(as_addr b) (abuffer_of_buffer b) h h' /\ live h b /\ length b > 0))
  (ensures (live h' b /\ as_seq h b == as_seq h' b))

let unused_in_abuffer_preserved
  (#t: Type)
  (b: buffer t)
  (h h' : HS.mem)
: Lemma
  (requires (b `unused_in` h))
  (ensures (abuffer_preserved #(frameOf b) #(as_addr b) (abuffer_of_buffer b) h h'))
= Classical.move_requires (fun b -> live_not_unused_in #t h b) b;
  live_null t h;
  null_unique b;
  unused_in_equiv b h;
  addr_unused_in_abuffer_preserved #(frameOf b) #(as_addr b) (abuffer_of_buffer b) h h'

val abuffer_includes (#r: HS.rid) (#a: nat) (larger smaller: abuffer r a) : GTot Type0

val abuffer_includes_refl (#r: HS.rid) (#a: nat) (b: abuffer r a) : Lemma
  (b `abuffer_includes` b)

val abuffer_includes_trans (#r: HS.rid) (#a: nat) (b1 b2 b3: abuffer r a) : Lemma
  (requires (b1 `abuffer_includes` b2 /\ b2 `abuffer_includes` b3))
  (ensures (b1 `abuffer_includes` b3))

val abuffer_includes_abuffer_preserved (#r: HS.rid) (#a: nat) (larger smaller: abuffer r a) (h1 h2: HS.mem) : Lemma
  (requires (larger `abuffer_includes` smaller /\ abuffer_preserved larger h1 h2))
  (ensures (abuffer_preserved smaller h1 h2))

val abuffer_includes_intro (#t: Type) (larger smaller: buffer t) : Lemma
  (requires (larger `includes` smaller))
  (ensures (
    let r = frameOf larger in
    let a = as_addr larger in
    abuffer_includes #r #a (abuffer_of_buffer larger) (abuffer_of_buffer smaller)
  ))

val abuffer_disjoint (#r: HS.rid) (#a: nat) (b1 b2: abuffer r a) : GTot Type0

val abuffer_disjoint_sym (#r: HS.rid) (#a: nat) (b1 b2: abuffer r a) : Lemma
  (abuffer_disjoint b1 b2 <==> abuffer_disjoint b2 b1)

val abuffer_disjoint_includes (#r: HS.rid) (#a: nat) (larger1 larger2: abuffer r a) (smaller1 smaller2: abuffer r a) : Lemma
  (requires (abuffer_disjoint larger1 larger2 /\ larger1 `abuffer_includes` smaller1 /\ larger2 `abuffer_includes` smaller2))
  (ensures (abuffer_disjoint smaller1 smaller2))

val abuffer_disjoint_intro (#t1 #t2: Type) (b1: buffer t1) (b2: buffer t2) : Lemma
  (requires (disjoint b1 b2 /\ frameOf b1 == frameOf b2 /\ as_addr b1 == as_addr b2))
  (ensures (
    let r = frameOf b1 in
    let a = as_addr b1 in
    abuffer_disjoint #r #a (abuffer_of_buffer b1) (abuffer_of_buffer b2)
  ))

(* It is too much to ask that a buffer not be disjoint from itself,
   but if so, then it should be always preserved. (Actually, it should
   be zero-length; not sure if we need such a strong result.) *)

val abuffer_disjoint_self_preserved (#r: HS.rid) (#a: nat) (b: abuffer r a) (h1 h2: HS.mem) : Lemma
  (requires (abuffer_disjoint b b))
  (ensures (abuffer_preserved b h1 h2))


(* Basic, non-compositional modifies clauses, used only to implement the generic modifies clause. DO NOT USE in client code *)

val modifies_0 (h1 h2: HS.mem) : GTot Type0

val modifies_0_live_region (h1 h2: HS.mem) (r: HS.rid) : Lemma
  (requires (modifies_0 h1 h2 /\ HS.live_region h1 r))
  (ensures (HS.live_region h2 r))

val modifies_0_mreference (#a: Type) (#pre: Preorder.preorder a) (h1 h2: HS.mem) (r: HS.mreference a pre) : Lemma
  (requires (modifies_0 h1 h2 /\ h1 `HS.contains` r))
  (ensures (h2 `HS.contains` r /\ h1 `HS.sel` r == h2 `HS.sel` r))

let modifies_0_abuffer
  (#r: HS.rid)
  (#a: nat)
  (b: abuffer r a)
  (h1 h2: HS.mem)
: Lemma
  (requires (modifies_0 h1 h2))
  (ensures (abuffer_preserved b h1 h2))
= same_mreference_abuffer_preserved b h1 h2 (fun a' pre r' -> modifies_0_mreference h1 h2 r')

val modifies_1 (#a: Type) (b: buffer a) (h1 h2: HS.mem) : GTot Type0

val modifies_1_live_region (#a: Type) (b: buffer a) (h1 h2: HS.mem) (r: HS.rid) : Lemma
  (requires (modifies_1 b h1 h2 /\ HS.live_region h1 r))
  (ensures (HS.live_region h2 r))

val modifies_1_mreference
  (#a: Type) (b: buffer a)
  (h1 h2: HS.mem)
  (#a': Type) (#pre: Preorder.preorder a') (r' : HS.mreference a' pre)
: Lemma
  (requires (modifies_1 b h1 h2 /\ (frameOf b <> HS.frameOf r' \/ as_addr b <> HS.as_addr r') /\ h1 `HS.contains` r'))
  (ensures (h2 `HS.contains` r' /\ h1 `HS.sel` r' == h2 `HS.sel` r'))

val modifies_1_abuffer
  (#a: Type) (b : buffer a)
  (h1 h2: HS.mem)
  (b' : abuffer (frameOf b) (as_addr b))
: Lemma
  (requires (modifies_1 b h1 h2 /\ abuffer_disjoint #(frameOf b) #(as_addr b) (abuffer_of_buffer b) b'))
  (ensures (abuffer_preserved #(frameOf b) #(as_addr b) b' h1 h2))

val modifies_1_null
  (#a: Type) (b: buffer a)
  (h1 h2: HS.mem)
: Lemma
  (requires (modifies_1 b h1 h2 /\ g_is_null b))
  (ensures (modifies_0 h1 h2))

(* Basic stateful operations *)

val is_null (#a: Type) (b: buffer a) : HST.Stack bool
  (requires (fun h -> live h b))
  (ensures (fun h y h' -> h == h' /\ y == g_is_null b))

val sub (#a: Type) (b: buffer a) (i: U32.t) (len: U32.t) : HST.Stack (buffer a)
  (requires (fun h -> U32.v i + U32.v len < length b /\ live h b))
  (ensures (fun h y h' -> h == h' /\ y == gsub b i len))

val offset (#a: Type) (b: buffer a) (i: U32.t) : HST.Stack (buffer a)
  (requires (fun h -> U32.v i < length b /\ live h b))
  (ensures (fun h y h' -> h == h' /\ y == gsub b i (U32.sub (len b) i)))

val index (#a: Type) (b: buffer a) (i: U32.t) : HST.Stack a
  (requires (fun h -> live h b /\ U32.v i < length b))
  (ensures (fun h y h' -> h == h' /\ y == Seq.index (as_seq h b) (U32.v i)))

(* Update *)

val upd
  (#a: Type)
  (b: buffer a)
  (i: U32.t)
  (v: a)
: HST.Stack unit
  (requires (fun h -> live h b /\ U32.v i < length b))
  (ensures (fun h _ h' ->
    (not (g_is_null b)) /\
    modifies_1 b h h' /\
    live h' b /\
    as_seq h' b == Seq.upd (as_seq h b) (U32.v i) v
  ))

(* Recall *)

val recallable (#a: Type) (b: buffer a) : GTot Type0

val recallable_includes (#a: Type) (larger smaller: buffer a) : Lemma
  (requires (larger `includes` smaller))
  (ensures (recallable larger <==> recallable smaller))
  [SMTPatOr [
    [SMTPat (recallable larger); SMTPat (recallable smaller);];
    [SMTPat (larger `includes` smaller)];
  ]]

val recall
  (#a:Type)
  (b:buffer a)
: HST.Stack unit
  (requires (fun _ -> recallable b))
  (ensures  (fun m0 _ m1 -> m0 == m1 /\ live m1 b))


(* Deallocation *)

val freeable (#a: Type) (b: buffer a) : GTot Type0

val free
  (#a: Type)
  (b: buffer a)
: HST.ST unit
  (requires (fun h0 -> live h0 b /\ freeable b))
  (ensures (fun h0 _ h1 ->
    (not (g_is_null b)) /\
    Map.domain h1.HS.h `Set.equal` Map.domain h0.HS.h /\ 
    h1.HS.tip == h0.HS.tip /\
    modifies_1 b h0 h1 /\
    HS.live_region h1 (frameOf b)
  ))


(* Allocation *)

let alloc_post_common
  (#a: Type)
  (r: HS.rid)
  (len: nat)
  (b: buffer a)
  (h0 h1: HS.mem)
: GTot Type0
= b `unused_in` h0 /\
  live h1 b /\
  (not (g_is_null b)) /\
  frameOf b == r /\
  Map.domain h1.HS.h `Set.equal` Map.domain h0.HS.h /\ 
  h1.HS.tip == h0.HS.tip /\
  length b == len /\
  modifies_0 h0 h1

val gcmalloc
  (#a: Type)
  (r: HS.rid)
  (init: a)
  (len: U32.t)
: HST.ST (buffer a)
  (requires (fun h -> HST.is_eternal_region r /\ U32.v len > 0))
  (ensures (fun h b h' ->
    alloc_post_common r (U32.v len) b h h' /\
    as_seq h' b == Seq.create (U32.v len) init /\     
    recallable b
  ))

val malloc
  (#a: Type)
  (r: HS.rid)
  (init: a)
  (len: U32.t)
: HST.ST (buffer a)
  (requires (fun h -> HST.is_eternal_region r /\ U32.v len > 0))
  (ensures (fun h b h' ->
    alloc_post_common r (U32.v len) b h h' /\
    as_seq h' b == Seq.create (U32.v len) init /\     
    freeable b
  ))

val alloca
  (#a: Type)
  (init: a)
  (len: U32.t)
: HST.StackInline (buffer a)
  (requires (fun h -> U32.v len > 0))
  (ensures (fun h b h' ->
    alloc_post_common h.HS.tip (U32.v len) b h h' /\
    as_seq h' b == Seq.create (U32.v len) init
  ))

unfold let alloca_of_list_pre (#a: Type0) (init: list a) : GTot Type0 =
  normalize (0 < FStar.List.Tot.length init) /\
  normalize (FStar.List.Tot.length init <= UInt.max_int 32)

unfold let alloca_of_list_post (#a: Type) (len: nat) (buf: buffer a) : GTot Type0 =
  normalize (length buf == len)

val alloca_of_list
  (#a: Type0)
  (init: list a)
: HST.StackInline (buffer a)
  (requires (fun h -> alloca_of_list_pre #a init))
  (ensures (fun h b h' ->
    let len = FStar.List.Tot.length init in
    alloc_post_common h.HS.tip len b h h' /\
    alloca_of_list_post #a len b
  ))
