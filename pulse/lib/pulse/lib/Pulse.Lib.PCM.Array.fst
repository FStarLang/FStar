module Pulse.Lib.PCM.Array
#lang-pulse
module P = Pulse.Lib.PCM.Fraction
module M = FStar.Map
module PM = Pulse.Lib.PCM.Map
module Seq = FStar.Seq
open PulseCore.FractionalPermission

let index_t (len: Ghost.erased nat)
: Type0
= i: nat { i < len }

let carrier (elt: Type u#a) (len: Ghost.erased nat)
: Type u#a
= PM.map (index_t len) (P.fractional elt)

let pcm (elt: Type u#a) (len: Ghost.erased nat)
: FStar.PCM.pcm (carrier elt len)
= PM.pointwise (index_t len) (P.pcm_frac #elt)

let one (#elt: Type) (#len: Ghost.erased nat) = (pcm elt len).p.one

let composable (#elt: Type) (#len: Ghost.erased nat) = (pcm elt len).p.composable

let compose (#elt: Type) (#len: Ghost.erased nat) = (pcm elt len).p.op

let mk_carrier
  (#elt: Type)
  (len: nat)
  (offset: nat)
  (s: Seq.seq elt)
  (p: perm)
: Tot (carrier elt len)
= let f (i: nat) : Tot (P.fractional elt) =
    if offset + Seq.length s > len || i < offset || i >= offset + Seq.length s
    then None
    else Some (Seq.index s (i - offset), p)
  in
  M.map_literal f

let mk_carrier_inj
  (#elt: Type)
  (len: nat)
  (offset: nat)
  (s1 s2: Seq.seq elt)
  (p1 p2: perm)
: Lemma
  (requires (
    mk_carrier len offset s1 p1 == mk_carrier len offset s2 p2 /\
    offset + Seq.length s1 <= len /\
    offset + Seq.length s2 <= len
  ))
  (ensures (
    s1 `Seq.equal` s2 /\
    (Seq.length s1 > 0 ==> p1 == p2)
  ))
= assert (forall (i: nat) . i < Seq.length s1 ==>
    (M.sel (mk_carrier len offset s1 p1) (offset + i) == Some (Seq.index s1 i, p1)));
  assert (forall (i: nat) . i < Seq.length s2 ==>
     M.sel (mk_carrier len offset s2 p2) (offset + i) == Some (Seq.index s2 i, p2))

