module Selectors.Arrays
open Steel.Effect
open Steel.Effect.Atomic

module A = Steel.Array
module AP = Steel.ArrayPtr
module U32 = FStar.UInt32

let max (x1 x2: nat) : Tot nat = if x1 < x2 then x2 else x1

let rec array_max (a: A.array nat) (len: U32.t { len == A.len a /\ U32.v len > 0 }) : SteelT nat (A.varray a) (fun _ -> A.varray a) =
  if len = 1ul
  then begin
    noop ();
    A.index a 0ul
  end
  else begin
    let len1 = U32.div len 2ul in
    let len2 = U32.sub len len1 in
    let a1a2 = A.split a len1 in
    let m1 = array_max (A.pfst a1a2) len1 in
    let m2 = array_max (A.psnd a1a2) len2 in
    let a' = A.join (A.pfst a1a2) (A.psnd a1a2) in
    change_equal_slprop (A.varray a') (A.varray a);
    let res = max m1 m2 in
    return res
  end

let rec varray_max (a: AP.t nat) (len: U32.t) : Steel nat
  (AP.varrayptr a)
  (fun _ -> AP.varrayptr a)
  (fun h ->
    len == A.len (h (AP.varrayptr a)).AP.array /\
    U32.v len > 0
  )
  (fun h _ h' ->
    (h' (AP.varrayptr a)).AP.array == (h (AP.varrayptr a)).AP.array /\
    (h' (AP.varrayptr a)).AP.perm == (h (AP.varrayptr a)).AP.perm)
=
  if len = 1ul
  then begin
    noop ();
    AP.index a 0ul
  end
  else begin
    let len1 = U32.div len 2ul in
    let len2 = U32.sub len len1 in
    let a2 = AP.split a len1 in
    let m1 = varray_max a len1 in
    let m2 = varray_max a2 len2 in
    AP.join a a2;
    let res = max m1 m2 in
    return res
  end
