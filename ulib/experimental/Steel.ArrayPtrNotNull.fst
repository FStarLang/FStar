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

module Steel.ArrayPtrNotNull
open Steel.Reference

(* We could implement this module as a pointer to an array, 
   but we would like to be as close as possible to C 
   pointers, i.e. as base+offset.
 *)
friend Steel.Array
module A = Steel.Array

let to_v
  (#t: Type)
  (base: A.array1 t)
  (from: U32.t)
: Tot Type0
= (to: U32.t { U32.v from <= U32.v to /\ U32.v to <= Seq.length base })

let to_t
  (#t: Type)
  (base: A.array1 t)
  (from: U32.t)
: Tot Type0
= Ghost.erased (to_v base from)

noeq
type t (a: Type u#0) = {
  base: A.array1 a;
  from: U32.t;
  to: ghost_ref (to_v base from);
  rperm: ghost_ref perm;
}

let mk_t (#a: Type u#0) (base: A.array1 a) (from: U32.t) (to: ghost_ref (to_v base from)) (perm: ghost_ref perm) : Tot (t a) =
  {
    base = base;
    from = from;
    to = to;
    rperm = perm;
  }

let array_of
  (#a: Type)
  (p: t a)
  (to: to_t p.base p.from)
: Tot (A.array a)
= {
  A.base = p.base;
  A.from = p.from;
  A.to = Ghost.hide (Ghost.reveal to);
}

let varrayptr0_dep
  (#a: Type)
  (p: t a)
  (to_perm: normal (t_of (ghost_vptr p.to `star` ghost_vptr p.rperm)))
: Tot vprop
= A.varrayp (array_of p (fst to_perm)) (snd to_perm)

let varrayptr0_rewrite
  (#a: Type)
  (p: t a)
  (x: normal (t_of ((ghost_vptr p.to `star` ghost_vptr p.rperm) `vdep` varrayptr0_dep p)))
: Tot (v a)
= let (| to_perm, contents |) = x in
  {
    array = array_of p (fst to_perm);
    contents = contents;
    perm = snd to_perm;
  }

[@@ __steel_reduce__; __reduce__ ]
let varrayptr0
  (#a: Type)
  (r: t a)
: Tot vprop
= ((ghost_vptr r.to `star` ghost_vptr r.rperm) `vdep` varrayptr0_dep r) `vrewrite` varrayptr0_rewrite r

let is_arrayptr #a r = hp_of (varrayptr0 r)

let arrayptr_sel #a r = fun h -> sel_of (varrayptr0 r) h

val intro_varrayptr
  (#opened: _)
  (#a: Type)
  (r: t a)
  (x: A.array a)
  (p: perm)
: SteelGhost unit opened
    (ghost_vptr r.to `star` ghost_vptr r.rperm `star` A.varrayp x p)
    (fun _ -> varrayptr r)
    (fun h -> (
      can_be_split (ghost_vptr r.to `star` ghost_vptr r.rperm `star` A.varrayp x p) (ghost_vptr r.to) /\
      can_be_split (ghost_vptr r.to `star` ghost_vptr r.rperm `star` A.varrayp x p) (ghost_vptr r.rperm)
    ) ==> (
      let to = h (ghost_vptr r.to) in
      x == array_of r to /\
      p == h (ghost_vptr r.rperm)
    ))
    (fun h _ h' ->
      let s' = h' (varrayptr r) in
      s'.array == x /\
      s'.perm == p /\
      s'.contents == h (A.varrayp x p)
    )

let intro_varrayptr
  #_ #a r x p
=
  reveal_star_3 (ghost_vptr r.to) (ghost_vptr r.rperm) (A.varrayp x p);
  reveal_star (ghost_vptr r.to) (ghost_vptr r.rperm);
  intro_vdep
    (ghost_vptr r.to `star` ghost_vptr r.rperm)
    (A.varrayp x p)
    (varrayptr0_dep r);
  intro_vrewrite
    ((ghost_vptr r.to `star` ghost_vptr r.rperm) `vdep` varrayptr0_dep r)
    (varrayptr0_rewrite r);
  let g : Ghost.erased (v a) = gget (varrayptr0 r) in
  assert (g.array == x);
  assert (g.perm == p);
  change_slprop_rel
    (varrayptr0 r)
    (varrayptr r)
    (fun x y -> x == y)
    (fun m -> ())

[@@erasable]
noeq
type w (a: Type) = {
  w_array: A.array a; 
  w_perm: perm;
}

val elim_varrayptr
  (#opened: _)
  (#a: Type)
  (r: t a)
: SteelGhost (w a) opened
    (varrayptr r)
    (fun res -> ghost_vptr r.to `star` ghost_vptr r.rperm `star` A.varrayp res.w_array res.w_perm)
    (fun h -> True)
    (fun h res h' ->
      let s = h (varrayptr r) in
      can_be_split (ghost_vptr r.to `star` ghost_vptr r.rperm `star` A.varrayp res.w_array res.w_perm) (ghost_vptr r.to) /\
      can_be_split (ghost_vptr r.to `star` ghost_vptr r.rperm `star` A.varrayp res.w_array res.w_perm) (ghost_vptr r.rperm) /\
      res.w_array == s.array /\
      res.w_array == array_of r (h' (ghost_vptr r.to)) /\
      res.w_perm == h' (ghost_vptr r.rperm) /\
      res.w_perm == s.perm /\
      h' (A.varrayp res.w_array res.w_perm) == s.contents
    )

let elim_varrayptr
  #_ #a r
=
  change_slprop_rel
    (varrayptr r)
    (varrayptr0 r)
    (fun x y -> x == y)
    (fun m -> ());
  elim_vrewrite
    ((ghost_vptr r.to `star` ghost_vptr r.rperm) `vdep` varrayptr0_dep r)
    (varrayptr0_rewrite r);
  let to_perm = elim_vdep
    (ghost_vptr r.to `star` ghost_vptr r.rperm)
    (varrayptr0_dep r)
  in
  reveal_star (ghost_vptr r.to) (ghost_vptr r.rperm);
  let to = ghost_read r.to in
  let p = ghost_read r.rperm in
  let res = {
    w_array = array_of r to;
    w_perm = p;
  } in
  change_equal_slprop
    (varrayptr0_dep r to_perm)
    (A.varrayp res.w_array res.w_perm);
  reveal_star_3 (ghost_vptr r.to) (ghost_vptr r.rperm) (A.varrayp res.w_array res.w_perm);
  res

#push-options "--z3rlimit 16"
let join #opened #a al ar =
  let wl = elim_varrayptr al in
  let p = ghost_read al.rperm in
  change_equal_slprop
    (A.varrayp wl.w_array wl.w_perm)
    (A.varrayp wl.w_array p);
  let wr = elim_varrayptr ar in
  let ar_to = ghost_read ar.to in
  ghost_free ar.to;
  ghost_free ar.rperm;
  change_equal_slprop
    (A.varrayp wr.w_array wr.w_perm)
    (A.varrayp wr.w_array p);
  let aj = A.gjoin wl.w_array wr.w_array p in
  let ar_to : U32.t = ar_to in
  let ar_to : to_t al.base al.from = ar_to in
  ghost_write al.to ar_to;
  intro_varrayptr al aj p
#pop-options

let u32_bounded_add
  (x y: U32.t) (z: Ghost.erased U32.t)
: Pure U32.t
  (requires (U32.v x + U32.v y <= U32.v z))
  (ensures (fun t -> U32.v t == U32.v x + U32.v y))
=
  x `U32.add` y

#push-options "--z3rlimit 16"
#restart-solver
let split x i =
  let w = elim_varrayptr x in
  let p = w.w_perm in
  change_equal_slprop
    (A.varrayp w.w_array w.w_perm)
    (A.varrayp w.w_array p);
  let res2 : Ghost.erased (A.array _ & A.array _) = A.gsplit0 p w.w_array i in
  reveal_star (A.varrayp (A.pfst res2) p) (A.varrayp (A.psnd res2) p);
  let x_to_1 = ghost_read x.to in
  let x_to_2 : Ghost.erased U32.t = Ghost.hide (Ghost.reveal x_to_1) in
  let j : to_v x.base x.from = u32_bounded_add x.from i x_to_2 in
  let x_to_3 : to_t x.base j = Ghost.hide (Ghost.reveal x_to_2) in
  ghost_write x.to j;
  intro_varrayptr x (A.pfst res2) p;
  let to2 : ghost_ref (to_v x.base j) = ghost_alloc x_to_3 in
  let p2 : ghost_ref perm = ghost_alloc p in
  let res : t _ = mk_t x.base j to2 p2 in
  change_equal_slprop
    (ghost_vptr to2)
    (ghost_vptr res.to);
  change_equal_slprop
    (ghost_vptr p2)
    (ghost_vptr res.rperm);
  intro_varrayptr res (A.psnd res2) p;
  return res
#pop-options

let alloc
  #a x n
=
  Seq.slice_length (Seq.create (U32.v n) x);
  let ar = A.alloc2 x n in
  let n2 : to_t ar.A.base 0ul = n in
  let to : ghost_ref (to_v ar.A.base 0ul) = ghost_alloc n2 in
  let perm : ghost_ref perm = ghost_alloc full_perm in
  let res = {
    base = ar.A.base;
    from = 0ul;
    to = to;
    rperm = perm;
  } in
  change_equal_slprop
    (ghost_vptr to)
    (ghost_vptr res.to);
  change_equal_slprop
    (ghost_vptr perm)
    (ghost_vptr res.rperm);
  intro_varrayptr res ar full_perm;
  return res

let index
  #a r i
=
  let w = elim_varrayptr r in
  let to = ghost_read r.to in
  let ar = array_of r to in
  change_equal_slprop
    (A.varrayp w.w_array w.w_perm)
    (A.varrayp ar w.w_perm);
  let res = A.indexp ar w.w_perm i in
  intro_varrayptr r ar w.w_perm;
  return res

let upd
  #a r i x
=
  let w = elim_varrayptr r in
  let to = ghost_read r.to in
  let ar = array_of r to in
  change_equal_slprop
    (A.varrayp w.w_array w.w_perm)
    (A.varrayp ar full_perm);
  A.upd ar i x;
  intro_varrayptr r ar full_perm

let free #a r =
  let w = elim_varrayptr r in
  ghost_free r.rperm;
  let to = ghost_read r.to in
  ghost_free r.to;
  let ar = array_of r to in
  change_equal_slprop
    (A.varrayp w.w_array w.w_perm)
    (A.varray ar);
  A.free ar

let share r =
  let w = elim_varrayptr r in
  let h = A.share w.w_array w.w_perm in
  ghost_write r.rperm h;
  let to = ghost_read r.to in
  intro_varrayptr r w.w_array h;
  let rto2 : ghost_ref (to_v r.base r.from) = ghost_alloc to in
  let rperm2 = ghost_alloc h in
  let res = {
    base = r.base;
    from = r.from;
    to = rto2;
    rperm = rperm2
  } in
  change_equal_slprop
    (ghost_vptr rto2)
    (ghost_vptr res.to);
  change_equal_slprop
    (ghost_vptr rperm2)
    (ghost_vptr res.rperm);
  intro_varrayptr res w.w_array h;
  return res

let gather r1 r2 =
  let w1 = elim_varrayptr r1 in
  let w2 = elim_varrayptr r2 in
  ghost_free r2.to;
  ghost_free r2.rperm;
  assert (w1.w_array == w2.w_array);
  change_equal_slprop
    (A.varrayp w2.w_array w2.w_perm)
    (A.varrayp w1.w_array w2.w_perm);
  let p = A.gather w1.w_array w1.w_perm w2.w_perm in
  ghost_write r1.rperm p;
  intro_varrayptr r1 w1.w_array p
