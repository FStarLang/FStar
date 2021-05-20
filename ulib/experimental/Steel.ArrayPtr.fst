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

module Steel.ArrayPtr
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
}

let mk_t (#a: Type u#0) (base: A.array1 a) (from: U32.t) (to: ghost_ref (to_v base from)) : Tot (t a) =
  {
    base = base;
    from = from;
    to = to;
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
  (to: normal (t_of (ghost_vptr p.to)))
: Tot vprop
= A.varray (array_of p to)

let varrayptr0_rewrite
  (#a: Type)
  (p: t a)
  (x: normal (t_of (ghost_vptr p.to `vdep` varrayptr0_dep p)))
: Tot (v a)
= let (| to, contents |) = x in
  {
    array = array_of p to;
    contents = contents;
  }

let varrayptr0
  (#a: Type)
  (r: t a)
: Tot vprop
= (ghost_vptr r.to `vdep` varrayptr0_dep r) `vrewrite` varrayptr0_rewrite r

let is_arrayptr #a r = hp_of (varrayptr0 r)

let arrayptr_sel #a r = fun h -> sel_of (varrayptr0 r) h

let intro_varrayptr
  (#opened: _)
  (#a: Type)
  (r: t a)
: SteelGhost unit opened
    ((ghost_vptr r.to `vdep` varrayptr0_dep r) `vrewrite` varrayptr0_rewrite r)
    (fun _ -> varrayptr r)
    (fun _ -> True)
    (fun h0 _ h1 -> h1 (varrayptr r) == h0 ((ghost_vptr r.to `vdep` varrayptr0_dep r) `vrewrite` varrayptr0_rewrite r))
=
  change_slprop_rel
    ((ghost_vptr r.to `vdep` varrayptr0_dep r) `vrewrite` varrayptr0_rewrite r)
    (varrayptr r)
    (fun x y -> x == y)
    (fun _ -> ())

let elim_varrayptr
  (#opened: _)
  (#a: Type)
  (r: t a)
: SteelGhost unit opened
    (varrayptr r)
    (fun _ -> (ghost_vptr r.to `vdep` varrayptr0_dep r) `vrewrite` varrayptr0_rewrite r)
    (fun _ -> True)
    (fun h0 _ h1 -> h0 (varrayptr r) == h1 ((ghost_vptr r.to `vdep` varrayptr0_dep r) `vrewrite` varrayptr0_rewrite r))
=
  change_slprop_rel
    (varrayptr r)
    ((ghost_vptr r.to `vdep` varrayptr0_dep r) `vrewrite` varrayptr0_rewrite r)
    (fun x y -> x == y)
    (fun _ -> ())

#push-options "--z3rlimit 32"
let join #opened #a al ar =
  elim_varrayptr al;
  elim_vrewrite (ghost_vptr al.to `vdep` varrayptr0_dep al) (varrayptr0_rewrite al);
  let g_al_to = elim_vdep (ghost_vptr al.to) (varrayptr0_dep al) in
  let al_to = ghost_read al.to in
  let aal = array_of al al_to in
  change_equal_slprop
    (varrayptr0_dep al (Ghost.reveal g_al_to))
    (A.varray aal);
  elim_varrayptr ar;
  elim_vrewrite (ghost_vptr ar.to `vdep` varrayptr0_dep ar) (varrayptr0_rewrite ar);
  let g_ar_to = elim_vdep (ghost_vptr ar.to) (varrayptr0_dep ar) in
  let ar_to = ghost_read ar.to in
  ghost_free ar.to;
  let aar = array_of ar ar_to in
  change_equal_slprop
    (varrayptr0_dep ar (Ghost.reveal g_ar_to))
    (A.varray aar);
  let aj = A.gjoin aal aar in
  let ar_to : U32.t = ar_to in
  let ar_to : to_t al.base al.from = ar_to in
  ghost_write al.to ar_to;
  assert (Ghost.reveal aj == array_of al ar_to);
  intro_vdep (ghost_vptr al.to) (A.varray aj) (varrayptr0_dep al);
  intro_vrewrite (ghost_vptr al.to `vdep` varrayptr0_dep al) (varrayptr0_rewrite al);
  intro_varrayptr al
#pop-options

let u32_bounded_add
  (x y: U32.t) (z: Ghost.erased U32.t)
: Pure U32.t
  (requires (U32.v x + U32.v y <= U32.v z))
  (ensures (fun t -> U32.v t == U32.v x + U32.v y))
=
  x `U32.add` y

#push-options "--z3rlimit 32"
#restart-solver
let split #a x i =
  elim_varrayptr x;
  elim_vrewrite (ghost_vptr x.to `vdep` varrayptr0_dep x) (varrayptr0_rewrite x);
  let x_to_1 : to_t x.base x.from = elim_vdep (ghost_vptr x.to) (varrayptr0_dep x) in
  let xa = array_of x x_to_1 in
  change_equal_slprop
    (varrayptr0_dep x (Ghost.reveal x_to_1))
    (A.varray xa);
  let res2 : Ghost.erased (A.array a & A.array a) = A.gsplit0 xa i in
  reveal_star (A.varray (A.pfst res2)) (A.varray (A.psnd res2));
  let x_to_2 : Ghost.erased U32.t = Ghost.hide (Ghost.reveal x_to_1) in
  let j : to_v x.base x.from = u32_bounded_add x.from i x_to_2 in
  let x_to_3 : to_t x.base j = Ghost.hide (Ghost.reveal x_to_2) in
  ghost_write x.to j;
  assert (A.pfst res2 == array_of x j);
  intro_vdep
    (ghost_vptr x.to)
    (A.varray (A.pfst res2))
    (varrayptr0_dep x);
  intro_vrewrite (ghost_vptr x.to `vdep` varrayptr0_dep x) (varrayptr0_rewrite x);
  intro_varrayptr x;
  let to2 : ghost_ref (to_v x.base j) = ghost_alloc x_to_3 in
  let res : t a = mk_t x.base j to2 in
  let x_to_4 : to_t res.base res.from = Ghost.hide (Ghost.reveal x_to_3 <: U32.t) in
  assert (A.psnd res2 == array_of res x_to_4);
  change_equal_slprop
    (ghost_vptr to2)
    (ghost_vptr res.to);
  intro_vdep
    (ghost_vptr res.to)
    (A.varray (A.psnd res2))
    (varrayptr0_dep res);
  intro_vrewrite (ghost_vptr res.to `vdep` varrayptr0_dep res) (varrayptr0_rewrite res);
  intro_varrayptr res;
  return res
#pop-options

let alloc
  #a x n
=
  Seq.slice_length (Seq.create (U32.v n) x);
  let ar = A.alloc2 x n in
  let n2 : to_t ar.A.base 0ul = n in
  let to : ghost_ref (to_v ar.A.base 0ul) = ghost_alloc n2 in
  let res = {
    base = ar.A.base;
    from = 0ul;
    to = to;
  } in
  assert (array_of res n2 == ar);
  change_equal_slprop
    (ghost_vptr to)
    (ghost_vptr res.to);
  intro_vdep
    (ghost_vptr res.to)
    (A.varray ar)
    (varrayptr0_dep res);
  intro_vrewrite (ghost_vptr res.to `vdep` varrayptr0_dep res) (varrayptr0_rewrite res);
  intro_varrayptr res;
  return res

let index
  #a r i
=
  elim_varrayptr r;
  elim_vrewrite (ghost_vptr r.to `vdep` varrayptr0_dep r) (varrayptr0_rewrite r);
  let g = elim_vdep (ghost_vptr r.to) (varrayptr0_dep r) in
  let to = ghost_read r.to in
  let ar = array_of r to in
  change_equal_slprop
    (varrayptr0_dep r (Ghost.reveal g))
    (A.varray ar);
  let res = A.index ar i in
  intro_vdep
    (ghost_vptr r.to)
    (A.varray ar)
    (varrayptr0_dep r);
  intro_vrewrite (ghost_vptr r.to `vdep` varrayptr0_dep r) (varrayptr0_rewrite r);
  intro_varrayptr r;
  return res

let upd
  #a r i x
=
  elim_varrayptr r;
  elim_vrewrite (ghost_vptr r.to `vdep` varrayptr0_dep r) (varrayptr0_rewrite r);
  let to = elim_vdep (ghost_vptr r.to) (varrayptr0_dep r) in
  let ar = array_of r to in
  change_equal_slprop
    (varrayptr0_dep r (Ghost.reveal to))
    (A.varray ar);
  A.upd ar i x;
  intro_vdep
    (ghost_vptr r.to)
    (A.varray ar)
    (varrayptr0_dep r);
  intro_vrewrite (ghost_vptr r.to `vdep` varrayptr0_dep r) (varrayptr0_rewrite r);
  intro_varrayptr r

let free #a r =
  elim_varrayptr r;
  elim_vrewrite (ghost_vptr r.to `vdep` varrayptr0_dep r) (varrayptr0_rewrite r);
  let to = elim_vdep (ghost_vptr r.to) (varrayptr0_dep r) in
  ghost_free r.to;
  let ar = array_of r to in
  change_equal_slprop
    (varrayptr0_dep r to)
    (A.varray ar);
  A.free ar
