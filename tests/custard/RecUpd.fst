module RecUpd

(* Section 104.  The projection form of the constructor's eta law.

   Nobody writes [{ f1 = c.f1; ...; fn = c.fn }].  What the reporter found in
   EverParse is what [{c with f = e}] leaves behind once [f] is ghost: the
   elaboration fills every *other* field with a projection of [c], erasure
   deletes the one field that was not, and a partial update has become a total
   one.  The residue has no pattern anywhere in it, which is why section 102's
   law -- stated over a [match] -- cannot see it. *)

module U8 = FStar.UInt8
module U32 = FStar.UInt32
module G = FStar.Ghost

noeq type str = {
  s_type : U8.t;
  s_size : U32.t;
  s_perm : G.erased nat;
}

(* [cbor_string_reset_perm] and its four neighbours, to the letter. *)
let reset_perm (p: G.erased nat) (c: str) : str = { c with s_perm = p }

(* Two fields rather than three: the other four in the reporter's cluster. *)
noeq type tagged = {
  t_tag : U32.t;
  t_pay : U8.t;
  t_perm : G.erased nat;
}

let tagged_reset (p: G.erased nat) (c: tagged) : tagged = { c with t_perm = p }

(* A *permutation*, not an identity, and it must survive untouched: the field
   names are what tell the two apart, and getting this wrong would be silent. *)
noeq type pair2 = { p_a : U32.t; p_b : U32.t }

let swap (c: pair2) : pair2 = { p_a = c.p_b; p_b = c.p_a }

(* A partial update whose written field is *not* ghost stays a construction:
   one component is not a projection of [c], so the law does not apply. *)
let bump (c: pair2) : pair2 = { c with p_b = U32.add_mod c.p_b 1ul }

(* The same law at a tuple, where a component's position is its field name.
   [depat] runs before [simpl], so by the time the law is asked the pattern
   has already become two projections -- which is the point: section 102's
   form and this one are the same law reached by different roads. *)
let retuple (c: U32.t & U8.t) : U32.t & U8.t = let (a, b) = c in (a, b)

let main () : FStar.Int32.t =
  let s = { s_type = 3uy; s_size = 9ul; s_perm = G.hide 1 } in
  let s = reset_perm (G.hide 2) s in
  let t = { t_tag = 4ul; t_pay = 5uy; t_perm = G.hide 1 } in
  let t = tagged_reset (G.hide 2) t in
  let q = swap (bump { p_a = 10ul; p_b = 20ul }) in
  let (a, b) = retuple (7ul, 8uy) in
  if s.s_type = 3uy && s.s_size = 9ul && t.t_tag = 4ul && t.t_pay = 5uy
     && q.p_a = 21ul && q.p_b = 10ul && a = 7ul && b = 8uy
  then 0l else 1l
