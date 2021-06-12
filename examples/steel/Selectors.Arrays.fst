module Selectors.Arrays
open Steel.Effect
open Steel.Effect.Atomic
open Steel.CStdInt

module A = Steel.Array

let is_seq_max (x: nat) (l: Seq.seq nat) : Tot prop =
  (exists (i: nat {i < Seq.length l}) . x == Seq.index l i) /\
  (forall (i: nat {i < Seq.length l}) . Seq.index l i <= x)

let max (x1 x2: nat) : Tot nat = if x1 < x2 then x2 else x1

#set-options "--ide_id_info_off"

let rec array_max
  (a: A.array nat) (len: size_t { len == A.len a /\ size_v len > 0 })
: Steel nat
  (A.varray a)
  (fun _ -> A.varray a)
  (fun _ -> True)
  (fun h res h' ->
    let s = h (A.varray a) in
    h' (A.varray a) == s /\
    is_seq_max res s
  )
=
  if len = A.one_size
  then begin
    noop ();
    A.index a A.zero_size
  end
  else begin
    let len1 = size_div len (A.mk_size_t 2ul) in
    let len2 = size_sub len len1 in
    let a1a2 = A.split a len1 in
    let m1 = array_max (fst a1a2) len1 in
    let m2 = array_max (snd a1a2) len2 in
    let a' = A.join (fst a1a2) (snd a1a2) in
    change_equal_slprop (A.varray a') (A.varray a);
    let res = max m1 m2 in
    return res
  end
