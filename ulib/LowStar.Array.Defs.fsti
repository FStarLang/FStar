module LowStar.Array.Defs


module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
open FStar.HyperStack.ST
module U32 = FStar.UInt32
module P = LowStar.Permissions



/// The array is an abstract type.
val array (a:Type0): Type0

(**** Definitions of ghost operations and predicates on arrays *)

val length (#a:Type) (b:array a) : l:U32.t{U32.v l > 0}
let vlength (#a:Type) (b:array a) : pos = U32.v (length b)

/// A array is viewed as an `FStar.Seq.seq`. However, since these arrays have permissions attached to them, `as_seq` is doubled by an
/// `as_seq_perm` which returns the list of permission held by the array on each of its cells.
val as_seq (#a:Type) (h:HS.mem) (b:array a) : GTot (s:Seq.seq a{Seq.length s == vlength b})
val as_perm_seq (#a:Type) (h:HS.mem) (b:array a) : GTot (s:Seq.seq P.permission{Seq.length s == vlength b})


/// Helper functions for accessing the array views.
let get (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < vlength b}) : GTot a
  = Seq.index (as_seq h b) i
let get_perm (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < vlength b}) : GTot P.permission
  = Seq.index (as_perm_seq h b) i

/// Liveness is an abstract predicate, required or ensured by functions in `LowStar.Array`. As a helper to understand its behavior, one can view it as "the array is correctly allocated and all of its cells have a strictly positive permission".
val live (#a:Type) (h:HS.mem) (b:array a) : Type0

/// Helpers for specifying full permissions on an array.
let writeable_cell (#a:Type) (h:HS.mem) (b:array a) (i:nat{i < vlength b}) : Type0 =
  get_perm #a h b i == 1.0R /\ live #a h b
let writeable #a h b =
  live #a h b /\
  (forall (i:nat{i < vlength #a b}). {:pattern (get_perm h b i) } writeable_cell h b i)


/// Abstract predicate used to describe what happens after sharing an array to get two immutable references from it. It implies that the
/// two arrays have the same length, and is commutative.
val gatherable (#a:Type0) (b1 b2:array a) : Type0
val gatherable_same_length (#a:Type0) (b1 b2:array a) : Lemma
  (requires (gatherable b1 b2))
  (ensures (length b1 = length b2))
  [SMTPatOr [
    [SMTPat (gatherable b1 b2); SMTPat (length b1)];
    [SMTPat (gatherable b1 b2); SMTPat (length b2)]
  ]]
val gatherable_comm (#a: Type0) (b1 b2: array a): Lemma
  (requires (gatherable b1 b2))
  (ensures (gatherable b2 b1))
  [SMTPat (gatherable b1 b2)]

/// In order to addition the permissions of two arrays, they have to be `gatherable`.
let summable_permissions (#a: Type0) (h: HS.mem) (b1 b2: array a) : Type0 =
  gatherable #a b1 b2 /\
  (forall (i:nat{i < vlength #a b1}). P.summable_permissions (get_perm h b1 i) (get_perm h b2 i))

/// Another abstract predicate used to define whether an array is susceptible to be freed.
val freeable (#a: Type) (b: array a) : GTot Type0

(**** Sub-buffers *)

/// `gsub` is the specification of what happens when performing a sub-array extraction.
val gsub (#a:Type0) (b:array a) (i:U32.t) (len:U32.t{U32.v len > 0})
  :Ghost (array a)
         (requires (U32.v i + U32.v len <= vlength b))
	 (ensures (fun b' ->
	   forall(h: HS.mem). {:pattern (as_seq h b') \/ (as_perm_seq h b')}
	   as_seq h b' == Seq.slice (as_seq h b) (U32.v i) (U32.v i + U32.v len) /\
	   as_perm_seq h b' == Seq.slice (as_perm_seq h b) (U32.v i) (U32.v i + U32.v len)
	 ))

/// `gsub` enjoys various properties related to the view and the length of the sub-array, compared to the original array.
val live_gsub (#a:Type0) (h:HS.mem) (b:array a) (i:U32.t) (len:U32.t{U32.v len > 0})
  :Lemma (requires (U32.v i + U32.v len <= vlength b))
         (ensures  (live h b ==> (live h (gsub  b i len))))
         [SMTPat (live h (gsub  b i len))]
val len_gsub (#a:Type0) (b:array a) (i:U32.t) (len':U32.t{U32.v len' > 0})
  :Lemma (requires (U32.v i + U32.v len' <= vlength b))
         (ensures (length (gsub b i len') == len'))
         [SMTPatOr [
             [SMTPat (length (gsub b i len'))];
             [SMTPat (length (gsub b i len'))];
         ]]
val gsub_inj (#a:Type0) (b1 b2:array a) (i1 i2:U32.t) (len1:U32.t{U32.v len1 > 0}) (len2:U32.t{U32.v len2 > 0})
  :Lemma (requires (U32.v i1 + U32.v len1 <= vlength b1 /\
                    U32.v i2 + U32.v len2 <= vlength b2 /\
		    gsub b1 i1 len1 === gsub b2 i2 len2))
         (ensures (len1 == len2 /\ (b1 == b2 ==> i1 == i2) /\ ((i1 == i2 /\ length b1 == length b2) ==> b1 == b2)))
val gsub_gsub (#a:Type0)
  (b:array a)
  (i1:U32.t) (len1:U32.t{U32.v len1 > 0})
  (i2: U32.t)  (len2:U32.t{U32.v len2 > 0})
  :Lemma (requires (U32.v i1 + U32.v len1 <= vlength b /\
                    U32.v i2 + U32.v len2 <= U32.v len1))
         (ensures  (gsub (gsub b i1 len1) i2 len2 == gsub b (U32.add i1 i2) len2))
         [SMTPat (gsub (gsub b i1 len1) i2 len2)]
val gsub_zero_length (#a:Type0) (b:array a)
  :Lemma (b == gsub  b 0ul (length b))


/// There exists a more sophisticated form of sub-array extraction that involves splitting an array into two disjoint parts, and this is
/// precisely what this abstract predicate captures.
val is_split_into (#a:Type0) (b: array a) (s:array a & array a) : Type0
