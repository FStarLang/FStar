module LowStar.Permissions.Array

module HS = FStar.HyperStack
open FStar.HyperStack.ST
module U32 = FStar.UInt32
module PR = LowStar.Permissions.References
module P = LowStar.Permissions

val array (a:Type0): Type0

(*** Definitions of Ghost operations and predicates on arrays ***)

val length (#a:Type) (b:array a) : nat

val as_seq (#a:Type) (h:HS.mem) (b:array a) : GTot (s:Seq.seq a{Seq.length s == length b})

val as_perm_seq (#a:Type) (h:HS.mem) (b:array a) : GTot (s:Seq.seq P.permission{Seq.length s == length b})

let get (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < length b}) : GTot a
  = Seq.index (as_seq h b) i

let get_perm (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < length b}) : GTot P.permission
  = Seq.index (as_perm_seq h b) i


val live (#a:Type) (h:HS.mem) (b:array a) : Type0

let writeable_cell (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < length b}) : Type0 =
  get_perm #a h b i == 1.0R /\ live #a h b

let writeable #a h b =
  live #a h b /\
  (forall (i:nat{i < length #a b}). writeable_cell h b i)


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
  (forall (i:nat{i < length #a b1}). P.summable_permissions (get_perm h b1 i) (get_perm h b2 i))

val frameOf (#a:Type0) (b:array a) : Tot HS.rid
val as_addr (#a:Type0) (b:array a) : GTot nat

(*** Definitions of locations for arrays with permissions ***)

val loc:Type0

val loc_none: loc
val loc_union (s1 s2: loc) : GTot loc
val loc_disjoint (s1 s2: loc) : GTot Type0
val loc_includes (s1 s2: loc) : GTot Type0

val loc_array (#a:Type0) (b:array a) : GTot loc

val modifies (s: loc) (h1 h2: HS.mem) : GTot Type0

(*** Stateful operations implementing the ghost specifications ***)


val index (#a:Type) (b:array a) (i:U32.t{U32.v i < length b})
  : Stack a (requires fun h -> live h b)
            (ensures fun h0 y h1 -> h0 == h1 /\ y == get h0 b (U32.v i))

val upd (#a:Type) (b:array a) (i:U32.t{U32.v i < length b}) (v:a)
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
  (requires fun h0 -> live h0 b /\ length b > 0)
  (ensures fun h0 b' h1 ->
    modifies (loc_array b) h0 h1 /\
    live h1 b /\ live h1 b' /\
    loc_disjoint (loc_array b) (loc_array b') /\
    as_seq h0 b == as_seq h1 b /\ // The values of the initial array are not modified
    as_seq h1 b' == as_seq h1 b /\ // The values of the new array are the same as the initial array
    mergeable b b' /\
    (forall (i:nat{i < length b}). {:pattern [get_perm h1 b' i; get_perm h1 b i] } // The permission gets split in two
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
    (forall (i:nat{i < length b}). summable_permissions h0 b b1  )
  ))
  (ensures (fun h0 _ h1 ->
    live h1 b /\ (forall (i:nat{i < length b}). {:pattern (get_perm h1 b i)} // Permissions are summed into the first array
      get_perm h1 b i =  P.sum_permissions (get_perm h0 b i) (get_perm h0 b1 i)
    ) /\
    as_seq h1 b == as_seq h0 b /\ // The value of the array are not modifies
    modifies (loc_array b `loc_union` loc_array b1) h0 h1
  ))
