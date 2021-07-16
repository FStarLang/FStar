(*
   Copyright 2021 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Steel.Array

let array_prop
  (#t: Type)
  (from: P.t t)
  (to: Ghost.erased size_t)
  (free_perm: perm)
: Tot prop
=
   if P.g_is_null from
   then size_v to == 0 /\ free_perm == full_perm // for unicity
   else size_v (P.offset from) + size_v to <= size_v (P.base_array_len (P.base from)) == true

noeq
type array t = {
  from: P.t t;
  to: Ghost.erased size_t;
  free_perm: perm;
  prf: squash (array_prop from to free_perm);
}

let len a = Ghost.reveal a.to

let null (a: Type) : Tot (array a) = {
  from = P.null a;
  to = zero_size;
  free_perm = full_perm;
  prf = ();
}

let g_is_null a = P.g_is_null a.from

let range_of_array
  (#t: Type)
  (a: array t)
  (p: perm)
: Tot P.range
= {
  P.range_from = 0;
  P.range_to = size_v a.to;
  P.range_write_perm = p;
  P.range_free_perm = a.free_perm;
  P.range_prf = ();
}

let varray0 (#t: Type) (a: array t) (p: perm) : Tot vprop =
  P.vptr_range a.from (range_of_array a p)

let is_array r p = hp_of (varray0 r p)

let array_sel r p = fun h -> sel_of (varray0 r p) h

let intro_varrayp
  (#opened: _)
  (#t: Type)
  (ptr: P.t t)
  (rg: P.range)
  (a: array t)
  (p: perm)
: SteelGhost unit opened
    (P.vptr_range ptr rg)
    (fun _ -> varrayp a p)
    (fun _ ->
      ptr == a.from /\
      rg == range_of_array a p
    )
    (fun h _ h' -> (h' (varrayp a p) <: Seq.seq t) == h (P.vptr_range ptr rg))
=
  change_slprop_rel
    (P.vptr_range ptr rg)
    (varrayp a p)
    (fun x y -> x == y)
    (fun _ -> ())

let elim_varrayp
  (#opened: _)
  (#t: Type)
  (a: array t)
  (p: perm)
: SteelGhost unit opened
    (varrayp a p)
    (fun _ -> P.vptr_range a.from (range_of_array a p))
    (fun _ -> True)
    (fun h _ h' ->
      (h' (P.vptr_range a.from (range_of_array a p)) <: Seq.seq t) == h (varrayp a p)
    )
=
  change_slprop_rel
    (varrayp a p)
    (P.vptr_range a.from (range_of_array a p))
    (fun x y -> x == y)
    (fun _ -> ())

let varrayp_not_null a p =
  elim_varrayp a p;
  P.vptr_range_not_null a.from _;
  intro_varrayp a.from _ a p

[@@__steel_reduce__]
let varrayp_or_null0
  (#a: Type)
  (r: array a)
  (p: perm)
: Tot vprop
= P.vptr_range_or_null r.from (range_of_array r p)

let is_array_or_null r p = hp_of (varrayp_or_null0 r p)

let array_or_null_sel r p = fun h -> sel_of (varrayp_or_null0 r p) h

let intro_varrayp_or_null
  (#opened: _)
  (#t: Type)
  (ptr: P.t t)
  (rg: P.range)
  (a: array t)
  (p: perm)
: SteelGhost unit opened
    (P.vptr_range_or_null ptr rg)
    (fun _ -> varrayp_or_null a p)
    (fun _ ->
      ptr == a.from /\
      (P.g_is_null ptr == false ==> rg == range_of_array a p)
    )
    (fun h _ h' -> match h' (varrayp_or_null a p), h (P.vptr_range_or_null ptr rg) with
      | None, None -> True
      | Some s', Some s -> (s' <: Seq.seq t) == s
      | _ -> False
    )
=
  if P.g_is_null ptr
  then begin
    P.assert_null ptr rg;
    P.intro_vptr_range_or_null_none ptr (range_of_array a p);
    change_slprop_rel
      (P.vptr_range_or_null ptr (range_of_array a p))
      (varrayp_or_null a p)
      (fun x y -> x == y)
      (fun _ -> ())    
  end else begin
    noop ();
    change_slprop_rel
      (P.vptr_range_or_null ptr rg)
      (varrayp_or_null a p)
      (fun x y -> x == y)
      (fun _ -> ())
  end

let elim_varrayp_or_null
  (#opened: _)
  (#t: Type)
  (a: array t)
  (p: perm)
: SteelGhost unit opened
    (varrayp_or_null a p)
    (fun _ -> P.vptr_range_or_null a.from (range_of_array a p))
    (fun _ -> True)
    (fun h _ h' ->
      match h' (P.vptr_range_or_null a.from (range_of_array a p)), h (varrayp_or_null a p) with
      | None, None -> True
      | Some s', Some s -> (s' <: Seq.seq t) == s
      | _ -> False
    )
=
  change_slprop_rel
    (varrayp_or_null a p)
    (P.vptr_range_or_null a.from (range_of_array a p))
    (fun x y -> x == y)
    (fun _ -> ())

let is_null x r =
  elim_varrayp_or_null x r;
  let res = P.is_null x.from _ in
  intro_varrayp_or_null x.from (range_of_array x r) x r;
  return res

let intro_varrayp_or_null_none
  #_ #t a p
=
  P.intro_vptr_range_or_null_none a.from (range_of_array a p);
  intro_varrayp_or_null a.from (range_of_array a p) a p

let intro_varrayp_or_null_some
  #_ #t a p
=
  elim_varrayp a p;
  P.intro_vptr_range_or_null_some a.from (range_of_array a p);
  intro_varrayp_or_null a.from (range_of_array a p) a p

let assert_null a p =
  elim_varrayp_or_null a p;
  P.assert_null a.from (range_of_array a p)

let assert_not_null a p =
  elim_varrayp_or_null a p;
  P.assert_not_null a.from (range_of_array a p);
  intro_varrayp a.from (range_of_array a p) a p

let adjacent r1 r2 =
  P.g_is_null r1.from == P.g_is_null r2.from /\
  begin if P.g_is_null r1.from
  then True
  else
    P.base r1.from == P.base r2.from /\
    size_v (P.offset r1.from) + size_v r1.to == size_v (P.offset r2.from)
  end

val pure_merge
  (#t: Type)
  (r1 r2: array t)
: Pure (array t)
  (requires (adjacent r1 r2))
  (ensures (fun r -> length r == length r1 + length r2))

let pure_merge r1 r2 = {
  from = r1.from;
  to = r1.to `size_add` r2.to;
  free_perm = if g_is_null r1 then r1.free_perm else r1.free_perm `sum_perm` r2.free_perm;
  prf = ();
}

let merge r1 r2 = pure_merge r1 r2

let merge_assoc r1 r2 r3 = ()

let gsplit r i =
  if g_is_null r
  then (r, r)
  else
  let rl = {
    from = r.from;
    to = i;
    free_perm = half_perm r.free_perm;
    prf = ();
  } in
  let rr = {
    from = P.g_add r.from i;
    to = r.to `size_sub` i;
    free_perm = half_perm r.free_perm;
    prf = ();
  } in
  (rl, rr)

let split' a p i =
  varrayp_not_null a p;
  elim_varrayp a _;
  let pr_from = P.g_add a.from i in
  let _ = P.move a.from pr_from _ in
  let tmp = P.split pr_from _ in
  let _ = P.move pr_from a.from (P.GPair?.fst _) in
  let res' = gsplit a i in
  let fres = fst res' in
  let sres = snd res' in
  let res = P.GPair fres sres in
  intro_varrayp a.from _ (P.GPair?.fst res) p;
  intro_varrayp pr_from _ (P.GPair?.snd res) p;
  res

let splitc a p i =
  elim_varrayp a _;
  let pr_from = P.add a.from _ i in
  let res = ({
    from = a.from;
    to = i;
    free_perm = half_perm a.free_perm;
    prf = ();
  }, {
    from = pr_from;
    to = a.to `size_sub` i;
    free_perm = half_perm a.free_perm;
    prf = ();
  }) in
  intro_varrayp a.from _ a _;
  return res

let join' al ar p =
  elim_varrayp al _;
  elim_varrayp ar _;
  let _ = P.merge_left al.from ar.from _ _ in
  let res = Ghost.hide (merge al ar) in
  intro_varrayp al.from _ res p;
  res

let joinc al ar p =
  varrayp_not_null al _;
  varrayp_not_null ar _;
  elim_varrayp al _;
  elim_varrayp ar _;
  let res = pure_merge al ar in
  intro_varrayp al.from _ al _;
  intro_varrayp ar.from _ ar _;
  return res

let freeable a =
  P.g_is_null a.from == false /\
  P.base_array_freeable (P.base a.from) /\
  size_v (P.offset a.from) == 0 /\
  Ghost.reveal a.to == P.base_array_len (P.base a.from) /\
  a.free_perm == full_perm

let malloc #t x n =
  let p = P.calloc x n in
  let res = {
    from = p;
    to = Ghost.hide (if P.g_is_null p then zero_size else n);
    free_perm = full_perm;
    prf = ();
  } in
  intro_varrayp_or_null p (P.calloc_range n) res full_perm;
  return res

let indexp r p i =
  (* TODO: we should make Steel.Pointer support indexing with size_t in addition to ptrdiff_t.
     For now we do things manually, which will extract to ugly pointer arithmetic
  *)
  elim_varrayp r _;
  let pacc = P.add r.from _ i in
  let _ = P.move r.from pacc _ in
  let res = P.index pacc _ zero_ptrdiff in
  let _ = P.move pacc r.from _ in
  intro_varrayp r.from _ r p;
  return res

let upd r i x =
  (* TODO: same here *)
  elim_varrayp r _;
  let pacc = P.add r.from _ i in
  let _ = P.move r.from pacc _ in
  P.index_upd pacc _ zero_ptrdiff x;
  let _ = P.move pacc r.from _ in
  intro_varrayp r.from _ r _

let free r =
  elim_varrayp r _;
  P.free r.from _

let share a p =
  elim_varrayp a _;
  let r = P.share a.from _ in
  intro_varrayp a.from _ a r.P.range_write_perm;
  intro_varrayp a.from _ a r.P.range_write_perm;
  r.P.range_write_perm

let gather a p1 p2 =
  elim_varrayp a p1;
  elim_varrayp a p2;
  let r = P.gather a.from (range_of_array a p1) (range_of_array a p2) in
  intro_varrayp a.from _ a r.P.range_write_perm;
  r.P.range_write_perm

let g_get_pointer a = a.from

let get_range a p = range_of_array a p

let get_pointer a p = return a.from

let enter p r =
  P.vptr_range_not_null p _;
  let res = {
    from = p;
    to = int_to_size_t r.P.range_to;
    free_perm = r.P.range_free_perm;
    prf = ();
  } in
  intro_varrayp p _ res r.P.range_write_perm;
  return res

let exit' a p =
  elim_varrayp a p

let reveal r a p =
  let sq : squash (array_prop r a.to a.free_perm) = () in
  let res = {
    from = r;
    to = a.to;
    free_perm = a.free_perm;
    prf = sq;
  } in
  assert (Ghost.reveal a == res);
  change_equal_slprop
    (varrayp_or_null a p)
    (varrayp_or_null res p);
  return res

let get_pointer_gsplit r i = ()

let get_pointer_merge r1 r2 = ()

let length_get_pointer r = ()

let is_null_get_pointer r = ()
