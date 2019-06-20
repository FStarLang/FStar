module LowStar.Permissions.Array

module HS = FStar.HyperStack
open FStar.HyperStack.ST
module U32 = FStar.UInt32
module PR = LowStar.Permissions.References
module P = LowStar.Permissions

val array (a:Type0): Type0

(*** Definitions of Ghost operations and predicates on arrays ***)

val length (#a:Type) (b:array a) : U32.t
let vlength (#a:Type) (b:array a) : nat = U32.v (length b)

val as_seq (#a:Type) (h:HS.mem) (b:array a) : GTot (s:Seq.seq a{Seq.length s == vlength b})

val as_perm_seq (#a:Type) (h:HS.mem) (b:array a) : GTot (s:Seq.seq P.permission{Seq.length s == vlength b})

let get (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < vlength b}) : GTot a
  = Seq.index (as_seq h b) i

let get_perm (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < vlength b}) : GTot P.permission
  = Seq.index (as_perm_seq h b) i


val live (#a:Type) (h:HS.mem) (b:array a) : Type0

let writeable_cell (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < vlength b}) : Type0 =
  get_perm #a h b i == 1.0R /\ live #a h b

let writeable #a h b =
  live #a h b /\
  (forall (i:nat{i < vlength #a b}). writeable_cell h b i)


val mergeable (#a:Type0) (b1 b2:array a) : Type0

val mergeable_same_length (#a:Type0) (b1 b2:array a) : Lemma
  (requires (mergeable b1 b2))
  (ensures (length b1 = length b2))
  [SMTPatOr [
    [SMTPat (mergeable b1 b2); SMTPat (length b1)];
    [SMTPat (mergeable b1 b2); SMTPat (length b2)]
  ]]

val mergeable_comm (#a: Type0) (b1 b2: array a): Lemma
  (requires (mergeable b1 b2))
  (ensures (mergeable b2 b1))
  [SMTPat (mergeable b1 b2)]

let summable_permissions (#a: Type0) (h: HS.mem) (b1 b2: array a) : Type0 =
  mergeable #a b1 b2 /\
  (forall (i:nat{i < vlength #a b1}). P.summable_permissions (get_perm h b1 i) (get_perm h b2 i))

val frameOf (#a:Type0) (b:array a) : Tot HS.rid
val as_addr (#a:Type0) (b:array a) : GTot nat

(*** Sub-bufers *)

val gsub (#a:Type0) (b:array a) (i:U32.t) (len:U32.t)
  :Ghost (array a)
         (requires (U32.v i + U32.v len <= vlength b))
	 (ensures (fun b' ->
	   forall(h: HS.mem). {:pattern [as_seq h b'; as_perm_seq h b']}
	   as_seq h b' == Seq.slice (as_seq h b) (U32.v i) (U32.v i + U32.v len) /\
	   as_perm_seq h b' == Seq.slice (as_perm_seq h b) (U32.v i) (U32.v i + U32.v len)
	 ))

val live_gsub (#a:Type0) (h:HS.mem) (b:array a) (i:U32.t) (len:U32.t)
  :Lemma (requires (U32.v i + U32.v len <= vlength b))
         (ensures  (live h b ==> (live h (gsub  b i len))))
         [SMTPat (live h (gsub  b i len))]

val len_gsub (#a:Type0) (b:array a) (i:U32.t) (len':U32.t)
  :Lemma (requires (U32.v i + U32.v len' <= vlength b))
         (ensures (length (gsub b i len') == len'))
         [SMTPatOr [
             [SMTPat (length (gsub b i len'))];
             [SMTPat (length (gsub b i len'))];
         ]]

val frameOf_gsub (#a:Type0) (b:array a) (i:U32.t) (len:U32.t)
  :Lemma (requires (U32.v i + U32.v len <= vlength b))
         (ensures (frameOf (gsub b i len) == frameOf b))
  [SMTPat (frameOf (gsub  b i len))]

val as_addr_gsub (#a:Type0) (b:array a) (i:U32.t) (len:U32.t)
  :Lemma (requires (U32.v i + U32.v len <= vlength b))
         (ensures (as_addr (gsub b i len) == as_addr b))
         [SMTPat (as_addr (gsub b i len))]

val gsub_inj (#a:Type0) (b1 b2:array a) (i1 i2:U32.t) (len1 len2:U32.t)
  :Lemma (requires (U32.v i1 + U32.v len1 <= vlength b1 /\
                    U32.v i2 + U32.v len2 <= vlength b2 /\
		    gsub b1 i1 len1 === gsub b2 i2 len2))
         (ensures (len1 == len2 /\ (b1 == b2 ==> i1 == i2) /\ ((i1 == i2 /\ length b1 == length b2) ==> b1 == b2)))

val gsub_gsub (#a:Type0)
  (b:array a)
  (i1:U32.t) (len1:U32.t)
  (i2: U32.t) (len2: U32.t)
  :Lemma (requires (U32.v i1 + U32.v len1 <= vlength b /\
                    U32.v i2 + U32.v len2 <= U32.v len1))
         (ensures  (gsub (gsub b i1 len1) i2 len2 == gsub b (U32.add i1 i2) len2))
         [SMTPat (gsub (gsub b i1 len1) i2 len2)]

val gsub_zero_length (#a:Type0) (b:array a)
  :Lemma (b == gsub  b 0ul (length b))

val msub (#a:Type0) (b:array a) (i:U32.t) (len:U32.t)
  : Stack (array a)
    (requires (fun h ->
      U32.v i + U32.v len <= vlength b /\ live h b
    ))
    (ensures (fun h y h' ->
      h == h' /\ y == gsub b i len
    ))

(*** Definitions of locations for arrays with permissions ***)

val loc:Type0

val loc_none: loc
val loc_union (s1 s2: loc) : GTot loc
val loc_disjoint (s1 s2: loc) : GTot Type0
val loc_includes (s1 s2: loc) : GTot Type0

val loc_array (#a:Type0) (b:array a) : GTot loc

val modifies (s: loc) (h1 h2: HS.mem) : GTot Type0

(*** Stateful operations implementing the ghost specifications ***)


val index (#a:Type) (b:array a) (i:U32.t{U32.v i < vlength b})
  : Stack a (requires fun h -> live h b)
            (ensures fun h0 y h1 -> h0 == h1 /\ y == get h0 b (U32.v i))

val upd (#a:Type) (b:array a) (i:U32.t{U32.v i < vlength b}) (v:a)
    : Stack unit (requires fun h -> writeable_cell h b (U32.v i))
                 (ensures fun h0 _ h1 ->  writeable_cell h1 b (U32.v i) /\
                                       modifies (loc_array b) h0 h1 /\
                                       as_seq h1 b == Seq.upd (as_seq h0 b) (U32.v i) v)

val alloc (#a:Type0) (init:a) (len:U32.t)
  : ST (array a)
       (requires fun _ -> U32.v len > 0)
       (ensures fun h0 b h1 ->
         modifies loc_none h0 h1 /\
         writeable h1 b /\
         as_seq h1 b == Seq.create (U32.v len) init)

val share (#a:Type0) (b:array a) : Stack (array a)
  (requires fun h0 -> live h0 b /\ vlength b > 0)
  (ensures fun h0 b' h1 ->
    modifies (loc_array b) h0 h1 /\
    live h1 b /\ live h1 b' /\
    loc_disjoint (loc_array b) (loc_array b') /\
    as_seq h0 b == as_seq h1 b /\ // The values of the initial array are not modified
    as_seq h1 b' == as_seq h1 b /\ // The values of the new array are the same as the initial array
    mergeable b b' /\
    (forall (i:nat{i < vlength b}). {:pattern [get_perm h1 b' i; get_perm h1 b i] } // The permission gets split in two
      get_perm h1 b' i == P.half_permission (get_perm h0 b i) /\
      get_perm h1 b i == P.half_permission (get_perm h0 b i)
    ))

val merge:
  #a: Type ->
  b: array a ->
  b1: array a ->
  Stack unit (requires (fun h0 ->
    mergeable b b1 /\
    live h0 b /\ live h0 b1 /\
    (forall (i:nat{i < vlength b}). summable_permissions h0 b b1  )
  ))
  (ensures (fun h0 _ h1 ->
    live h1 b /\ (forall (i:nat{i < vlength b}). {:pattern (get_perm h1 b i)} // Permissions are summed into the first array
      get_perm h1 b i =  P.sum_permissions (get_perm h0 b i) (get_perm h0 b1 i)
    ) /\
    as_seq h1 b == as_seq h0 b /\ // The value of the array are not modifies
    modifies (loc_array b `loc_union` loc_array b1) h0 h1
  ))
