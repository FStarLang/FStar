module LowStar.Array.Modifies

module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
open FStar.HyperStack.ST
module U32 = FStar.UInt32
module P = LowStar.Permissions

open LowStar.Array.Defs

/// This module instantiates the `FStar.ModifiesGen` theory with our arrays. All the implementation details are hidden behind abstract
/// types, the comments inclue a brief description of what happens behind the scenes.

(**** Instantiation of the `FStar.ModifiesGen` theory **)


/// The atomic locations of this theory are each of the array cells, augmented with the permission identifier.
val loc:Type0

val loc_none: loc

val loc_union (s1 s2: loc) : GTot loc

/// Disjointness is defined as inequality between the memory address, the absolute index in the array or the permission identifier.
val loc_disjoint (s1 s2: loc) : GTot Type0

/// Inclusion for atomic locations is simply equality.
val loc_includes (s1 s2: loc) : GTot Type0

/// The location of the array is simply the `loc_union` of all the atomic locations of the cells composing it.
val loc_array (#a:Type0) (b:array a) : GTot loc

/// The notion of unused locations is the most tricky part of the instantiation. We have to set it up such that both allocation of a new
/// array and creation of a new reference from an existing array return a fresh location. Thus, we defined unusedness for an atomic
/// location (array cell) as a disjunction:
///  * either there is nothing allocated a the memory address pointed by the cell;
///  * either there is something allocated but it is not an array that has a sufficient length to contain the cell;
///  * or there is an allocated array of any length susceptible to contain the cell, but the permission identifier used by this cell in
///    the array is unused.
///
/// Cell usedness is defined as the logical negation of unusedness; however it can be shown to imply the existence of an allocated array
/// that uses the permission identifier of the cell.
///
/// Permission identifiers are used if they are below the current maximal permission identifier of the permission map
/// (see `LowStar.Permissions`).
val loc_unused_in (h: HS.mem) : GTot loc
val loc_used_in (h: HS.mem) : GTot loc
let fresh_loc (l: loc) (h h' : HS.mem) : GTot Type0 =
  (loc_unused_in h `loc_includes` l /\
  loc_used_in h' `loc_includes` l)

/// The modifies clauses specifies conservatively the largest location susceptible to have been modified between two heap states `h0` and
/// `h1`. Everything that was not modified and live in `h0` should still be live in `h1` with its contents untouched.
val modifies (s: loc) (h1 h2: HS.mem) : GTot Type0

(**** The lemma loft ***)

/// The `FStar.ModifiesGen` theory provides a bunch of lemmas describing the behavior of all its elements. For proof convenience, somme of these lemmas are reproduced here with `SMTPat`s. The lemma attic also contains array-specific lemmas.

(***** Locations: inclusion, disjointness, union *)


val loc_union_idem (s: loc) : Lemma
  (loc_union s s == s)
  [SMTPat (loc_union s s)]

val loc_union_comm (s1 s2: loc) : Lemma
  (loc_union s1 s2 == loc_union s2 s1)
  [SMTPat (loc_union s1 s2)]

val loc_union_assoc
  (s1 s2 s3: loc)
: Lemma
  (loc_union s1 (loc_union s2 s3) == loc_union (loc_union s1 s2) s3)

val loc_union_idem_1 (s1 s2: loc) : Lemma
  (loc_union s1 (loc_union s1 s2) == loc_union s1 s2)
  [SMTPat (loc_union s1 (loc_union s1 s2))]

val loc_union_idem_2 (s1 s2: loc) : Lemma
  (loc_union (loc_union s1 s2) s2 == loc_union s1 s2)
  [SMTPat (loc_union (loc_union s1 s2) s2)]

val loc_union_loc_none_l (s: loc) : Lemma
  (loc_union loc_none s == s)
  [SMTPat (loc_union loc_none s)]

val loc_union_loc_none_r (s: loc) : Lemma
  (loc_union s loc_none == s)
  [SMTPat (loc_union s loc_none)]

val loc_includes_refl (s: loc) : Lemma
  (loc_includes s s)
  [SMTPat (loc_includes s s)]

val loc_includes_trans_backwards (s1 s2 s3: loc) : Lemma
  (requires (loc_includes s1 s2 /\ loc_includes s2 s3))
  (ensures (loc_includes s1 s3))
  [SMTPat (loc_includes s1 s3); SMTPat (loc_includes s2 s3)]

val loc_includes_union_l (s1 s2 s: loc) : Lemma
  (requires (loc_includes s1 s \/ loc_includes s2 s))
  (ensures (loc_includes (loc_union s1 s2) s))
  [SMTPat (loc_includes (loc_union s1 s2) s)]

val loc_includes_union_r (s s1 s2: loc) : Lemma
  (loc_includes s (loc_union s1 s2) <==> (loc_includes s s1 /\ loc_includes s s2))
  [SMTPat (loc_includes s (loc_union s1 s2))]

val loc_includes_none (s: loc) : Lemma
  (loc_includes s loc_none)
  [SMTPat (loc_includes s loc_none)]

val loc_disjoint_sym'
  (s1 s2: loc)
: Lemma
  (loc_disjoint s1 s2 <==> loc_disjoint s2 s1)
  [SMTPat (loc_disjoint s1 s2)]

val loc_disjoint_none_r
  (s: loc)
: Lemma
  (ensures (loc_disjoint s loc_none))
  [SMTPat (loc_disjoint s loc_none)]

val loc_disjoint_union_r'
  (s s1 s2: loc)
: Lemma
  (ensures (loc_disjoint s (loc_union s1 s2) <==> (loc_disjoint s s1 /\ loc_disjoint s s2)))
  [SMTPat (loc_disjoint s (loc_union s1 s2))]

val loc_disjoint_includes
  (p1 p2 p1' p2' : loc)
: Lemma
  (requires (loc_includes p1 p1' /\ loc_includes p2 p2' /\ loc_disjoint p1 p2))
  (ensures (loc_disjoint p1' p2'))

val loc_disjoint_includes_r (b1 : loc) (b2 b2': loc) : Lemma
  (requires (loc_includes b2 b2' /\ loc_disjoint b1 b2))
  (ensures (loc_disjoint b1 b2'))
  [SMTPat (loc_disjoint b1 b2'); SMTPat (loc_includes b2 b2')]

(***** Modifies, unused and used locations *)

val modifies_array_elim
  (#t: Type)
  (b: array t)
  (p : loc)
  (h h': HS.mem)
: Lemma
  (requires (
    live h b /\
    loc_disjoint (loc_array b) p /\
    modifies p h h'
  ))
  (ensures (
    as_seq h b  == as_seq h' b /\
    as_perm_seq h b == as_perm_seq h' b /\
    live h' b
  ))
  [SMTPatOr [
    [ SMTPat (modifies p h h'); SMTPat (as_seq h b) ];
    [ SMTPat (modifies p h h'); SMTPat (as_perm_seq h b) ];
    [ SMTPat (modifies p h h'); SMTPat (live h b) ];
    [ SMTPat (modifies p h h'); SMTPat (as_seq h' b) ];
    [ SMTPat (modifies p h h'); SMTPat (as_perm_seq h' b) ];
    [ SMTPat (modifies p h h'); SMTPat (live h' b) ];
  ]]

val modifies_refl
  (s: loc)
  (h: HS.mem)
: Lemma
  (modifies s h h)
  [SMTPat (modifies s h h)]

val modifies_loc_includes
  (s1: loc)
  (h h': HS.mem)
  (s2: loc)
: Lemma
  (requires (modifies s2 h h' /\ loc_includes s1 s2))
  (ensures (modifies s1 h h'))
  [SMTPat (modifies s1 h h'); SMTPat (modifies s2 h h')]


val modifies_trans
  (s12: loc)
  (h1 h2: HS.mem)
  (s23: loc)
  (h3: HS.mem)
: Lemma
  (requires (modifies s12 h1 h2 /\ modifies s23 h2 h3))
  (ensures (modifies (loc_union s12 s23) h1 h3))

val modifies_trans_linear (l l_goal:loc) (h1 h2 h3:HS.mem)
  : Lemma (requires (modifies l h1 h2 /\ modifies l_goal h2 h3 /\ l_goal `loc_includes` l))
          (ensures  (modifies l_goal h1 h3))
	  [SMTPat (modifies l h1 h2); SMTPat (modifies l_goal h1 h3)]


val unused_in_used_in_disjoint_2
  (l1 l2 l1' l2': loc)
  (h: HS.mem)
: Lemma
  (requires (loc_unused_in h `loc_includes` l1 /\ loc_used_in h `loc_includes` l2 /\ l1 `loc_includes` l1' /\ l2 `loc_includes` l2' ))
  (ensures (loc_disjoint l1'  l2' ))
  [SMTPat (loc_disjoint l1' l2'); SMTPat (loc_unused_in h `loc_includes` l1); SMTPat (loc_used_in h `loc_includes` l2)]


val modifies_only_used_in
  (l: loc)
  (h h' : HS.mem)
: Lemma
  (requires (modifies (loc_unused_in h `loc_union` l) h h'))
  (ensures (modifies l h h'))

val modifies_remove_new_locs (l_fresh l_aux l_goal:loc) (h1 h2 h3:HS.mem)
  : Lemma (requires (fresh_loc l_fresh h1 h2 /\
                     modifies l_aux h1 h2 /\
		     l_goal `loc_includes` l_aux /\
                     modifies (loc_union l_fresh l_goal) h2 h3))
          (ensures  (modifies l_goal h1 h3))
	  [SMTPat (fresh_loc l_fresh h1 h2);
	   SMTPat (modifies l_aux h1 h2);
	   SMTPat (modifies l_goal h1 h3)]

val modifies_loc_disjoint (l0 l1:loc) (h0 h1 h2:HS.mem)
  : Lemma (requires (modifies l0 h0 h1 /\
                     modifies l1 h1 h2 /\
                     (forall l .
                       loc_disjoint l l0 /\
                       loc_includes (loc_used_in h0) l
                       ==>
                       loc_disjoint l l1)))
          (ensures  (modifies l0 h0 h2))

val loc_disjoint_used_in_modifies (h0 h1:HS.mem) (l l':loc)
  : Lemma (requires (loc_disjoint l' l /\
                     loc_includes (loc_used_in h0) l' /\
                     modifies l h0 h1))
          (ensures  (loc_includes (loc_used_in h1) l'))
          [SMTPat (loc_disjoint l' l);
           SMTPat (loc_includes (loc_used_in h0) l');
           SMTPat (loc_includes (loc_used_in h1) l')]

val live_array_used_in (#t: Type) (b: array t) (h: HS.mem) : Lemma
  (requires (live h b))
  (ensures (loc_used_in h `loc_includes` (loc_array b)))

(***** Locations: splitting arrays *)

val loc_union_gsub (#a:Type0) (b:array a) (i len1 len2:U32.t)
  :Lemma (requires (U32.v len1 > 0 /\ U32.v len2 > 0 /\ U32.v i + U32.v len1 + U32.v len2 <= vlength b))
         (ensures loc_union (loc_array (gsub b i len1)) (loc_array (gsub b (i `U32.add` len1) len2))
                  == loc_array (gsub b i (len1 `U32.add` len2)))


val loc_union_is_split_into (#a: Type) (b b1 b2: array a) : Lemma
  (requires (is_split_into b (b1, b2)))
  (ensures (loc_array b == loc_array b1 `loc_union` loc_array b2))

val disjoint_gsubs (#a:Type0) (b:array a) (i1 i2:U32.t) (len1:U32.t{U32.v len1 > 0}) (len2:U32.t{U32.v len2 > 0})
  :Lemma (requires (UInt32.v i1 + UInt32.v len1 <= (vlength b) /\
                    UInt32.v i2 + UInt32.v len2 <= (vlength b) /\
		    (UInt32.v i1 + UInt32.v len1 <= UInt32.v i2 \/
                     UInt32.v i2 + UInt32.v len2 <= UInt32.v i1)))
         (ensures  (loc_disjoint (loc_array (gsub b i1 len1)) (loc_array (gsub b i2 len2))))
