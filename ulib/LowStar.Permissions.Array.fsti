module LowStar.Permissions.Array

module HS = FStar.HyperStack
open FStar.HyperStack.ST
module U32 = FStar.UInt32

val array (a:Type0): Type0

(*** Definitions of Ghost operations and predicates on arrays ***)

val length (#a:Type) (b:array a) : nat

val live (#a:Type) (h:HS.mem) (b:array a) : Type0
val writeable (#a:Type) (h:HS.mem) (b:array a) : Type0

val lemma_writeable_implies_live (#a:Type) (h:HS.mem) (b:array a)
  : Lemma (requires writeable h b)
          (ensures live h b)

val as_seq (#a:Type) (h:HS.mem) (b:array a) : GTot (s:Seq.seq a{Seq.length s == length b})

let get (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < length b}) : GTot a
  = Seq.index (as_seq h b) i

val mergeable (#a:Type0) (b1 b2:array a) : Type0

val frameOf (#a:Type0) (b:array a) : Tot HS.rid
val as_addr (#a:Type0) (b:array a) : GTot nat

(*** Definitions of locations for arrays with permissions ***)

val bloc:Type0

val loc_none: bloc
val loc_union (s1 s2: bloc) : GTot bloc
val loc_disjoint (s1 s2: bloc) : GTot Type0
val loc_includes (s1 s2: bloc) : GTot Type0

val loc_array (#a:Type0) (b:array a) : GTot bloc

val modifies (s: bloc) (h1 h2: HS.mem) : GTot Type0

(*** Stateful operations implementing the ghost specifications ***)


val index (#a:Type) (b:array a) (i:U32.t{U32.v i < length b})
  : Stack a (requires fun h -> live h b)
            (ensures fun h0 y h1 -> h0 == h1 /\ y == get h0 b (U32.v i))

val upd (#a:Type) (b:array a) (i:U32.t{U32.v i < length b}) (v:a)
    : Stack unit (requires fun h -> writeable h b)
                 (ensures fun h0 _ h1 ->  writeable h1 b /\
                                       modifies (loc_array b) h0 h1 /\
                                       as_seq h1 b == Seq.upd (as_seq h0 b) (U32.v i) v)


// TODO: Do we want split instead
val gsub (#a:Type0) (b:array a) (i:U32.t) (len:U32.t)
  :Ghost (array a)
         (requires (U32.v i + U32.v len <= length b))
	 (ensures (fun _ -> True))


val sub (#a:Type) (b:array a) (i:U32.t) (len:U32.t)
  : Stack (array a)
          (requires fun h -> U32.v i + U32.v len <= length b /\ live h b)
          (ensures fun h0 y h1 -> h0 == h1 /\ y == gsub b i len)


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
    as_seq h1 b' == as_seq h1 b /\ // The values of the new buffer are the same as the initial array
    mergeable b b' /\
    True) // TODO: Talk about permissions here?
