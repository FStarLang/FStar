(*
   Copyright 2019 Microsoft Research

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

module LowParseWriters
include LowParseWriters.LowParse

open FStar.HyperStack.ST

module HS = FStar.HyperStack
module B = LowStar.Buffer
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST

noeq
type memory_invariant = {
  h0: Ghost.erased HS.mem;
  lread: Ghost.erased B.loc;
  lwrite: (lwrite: Ghost.erased B.loc { lread `B.loc_disjoint` lwrite });
}

unfold
let memory_invariant_includes (ol ne: memory_invariant) =
  B.modifies ol.lwrite ol.h0 ne.h0 /\
  ol.lwrite `B.loc_includes` ne.lwrite /\
  ne.lread `B.loc_includes` ol.lread

let memory_invariant_includes_trans (l1 l2 l3: memory_invariant) : Lemma
  (requires (l1 `memory_invariant_includes` l2 /\ l2 `memory_invariant_includes` l3))
  (ensures (l1 `memory_invariant_includes` l3))
= ()

unfold
let pure_wp_mono
  (a: Type)
  (wp: pure_wp a)
: GTot Type0
= (forall (p q:pure_post a).
     (forall (x:a). p x ==> q x) ==> (wp p ==> wp q))

inline_for_extraction
let read_repr_spec (a:Type u#x) (pre: pure_pre) (post: pure_post' a pre) : Tot (Type u#x) =
  unit ->
  Ghost a
  (requires pre)
  (ensures (fun v -> post v))

inline_for_extraction
val read_repr_impl
  (a:Type u#x)
  (pre: pure_pre)
  (post: pure_post' a pre)
  (l: memory_invariant)
  (spec: read_repr_spec a pre post)
: Tot Type0

let read_repr
  (a:Type u#x)
  (pre: pure_pre)
  (post: pure_post' a pre)
  (l: memory_invariant)
= dtuple2 _ (read_repr_impl a pre post l)

let read_return_spec
  (a:Type) (x:a)
: Tot (read_repr_spec a True (fun res -> res == x))
= fun _ -> x

inline_for_extraction
val read_return_impl
  (a:Type) (x:a) (inv: memory_invariant)
: Tot (read_repr_impl a True (fun res -> res == x) inv (read_return_spec a x))

inline_for_extraction
let read_return
  (a:Type) (x:a) (inv: memory_invariant)
: Tot (read_repr a True (fun res -> res == x) inv)
= (| read_return_spec a x, read_return_impl a x inv |)

let read_bind_pre
  (a:Type)
  (pre_f: pure_pre) (post_f: pure_post' a pre_f)
  (pre_g: (x:a) -> pure_pre)
: Tot pure_pre
= pre_f /\ (forall (x: a) . post_f x ==> pre_g x)

let read_bind_post
  (a:Type) (b:Type)
  (pre_f: pure_pre) (post_f: pure_post' a pre_f)
  (pre_g: (x:a) -> pure_pre) (post_g: (x:a) -> pure_post' b (pre_g x))
: Tot (pure_post' b (read_bind_pre a pre_f post_f pre_g))
= fun y ->
  exists x . pre_f /\ post_f x /\ post_g x y

let read_bind_spec
  (a:Type) (b:Type)
  (pre_f: pure_pre) (post_f: pure_post' a pre_f)
  (pre_g: (x:a) -> pure_pre) (post_g: (x:a) -> pure_post' b (pre_g x))
  (f_bind_spec: read_repr_spec a pre_f post_f)
  (g:(x:a -> read_repr_spec b (pre_g x) (post_g x)))
: Tot (read_repr_spec b (read_bind_pre a pre_f post_f pre_g) (read_bind_post a b pre_f post_f pre_g post_g))
= fun _ -> g (f_bind_spec ()) ()

inline_for_extraction
val read_bind_impl
  (a:Type) (b:Type)
  (pre_f: pure_pre) (post_f: pure_post' a pre_f)
  (pre_g: (x:a) -> pure_pre) (post_g: (x:a) -> pure_post' b (pre_g x))
  (f_bind_impl: read_repr_spec a pre_f post_f)
  (g:(x:a -> read_repr_spec b (pre_g x) (post_g x)))
  (l: memory_invariant)
  (f' : read_repr_impl a pre_f post_f l f_bind_impl)
  (g' : (x: a -> read_repr_impl b (pre_g x) (post_g x) l (g x)))
: Tot (read_repr_impl b (read_bind_pre a pre_f post_f pre_g) (read_bind_post a b pre_f post_f pre_g post_g) l (read_bind_spec a b pre_f post_f pre_g post_g f_bind_impl g))

inline_for_extraction
let read_bind
  (a:Type) (b:Type)
  (pre_f: pure_pre) (post_f: pure_post' a pre_f)
  (pre_g: (x:a) -> pure_pre) (post_g: (x:a) -> pure_post' b (pre_g x))
  (l: memory_invariant)
  (f_bind : read_repr a pre_f post_f l)
  (g : (x: a -> read_repr b (pre_g x) (post_g x) l))
: Tot (read_repr b (read_bind_pre a pre_f post_f pre_g) (read_bind_post a b pre_f post_f pre_g post_g) l)
= (| _, read_bind_impl a b pre_f post_f pre_g post_g (dfst f_bind) (fun x -> dfst (g x)) l (dsnd f_bind) (fun x -> dsnd (g x)) |)

unfold
let read_subcomp_spec_cond
  (a:Type)
  (pre: pure_pre) (post: pure_post' a pre)
  (pre': pure_pre) (post': pure_post' a pre')
: GTot Type0
= (pre' ==> pre) /\
  (forall x . (pre' /\ post x) ==> post' x)

unfold
let read_subcomp_cond
  (a:Type)
  (pre: pure_pre) (post: pure_post' a pre)
  (pre': pure_pre) (post': pure_post' a pre')
  (l: memory_invariant)
  (l' : memory_invariant)
: GTot Type0
= l `memory_invariant_includes` l' /\
  read_subcomp_spec_cond a pre post pre' post'

let read_subcomp_spec (a:Type)
  (pre: pure_pre) (post: pure_post' a pre)
  (pre': pure_pre) (post': pure_post' a pre')
  (f_subcomp:read_repr_spec a pre post)
: Pure (read_repr_spec a pre' post')
  (requires (read_subcomp_spec_cond a pre post pre' post'))
  (ensures (fun _ -> True))
= (fun x -> f_subcomp x)

inline_for_extraction
val read_subcomp_impl (a:Type)
  (pre: pure_pre) (post: pure_post' a pre)
  (pre': pure_pre) (post': pure_post' a pre')
  (l:memory_invariant)
  (l' : memory_invariant)
  (f_subcomp_spec:read_repr_spec a pre post)
  (f_subcomp:read_repr_impl a pre post l f_subcomp_spec)
  (sq: squash (read_subcomp_cond a pre post pre' post' l l'))
: Tot (read_repr_impl a pre' post' l' (read_subcomp_spec a pre post pre' post' f_subcomp_spec))

inline_for_extraction
let read_subcomp (a:Type)
  (pre: pure_pre) (post: pure_post' a pre)
  (pre': pure_pre) (post': pure_post' a pre')
  (l:memory_invariant)
  (l' : memory_invariant)
  (f_subcomp:read_repr a pre post l)
: Pure (read_repr a pre' post' l')
  (requires (read_subcomp_cond a pre post pre' post' l l'))
  (ensures (fun _ -> True))
= (| read_subcomp_spec a pre post pre' post' (dfst f_subcomp),
     read_subcomp_impl a pre post pre' post' l l' (dfst f_subcomp) (dsnd f_subcomp) ()
  |)

let read_if_then_else_pre
  (pre_f pre_g: pure_pre)
  (p:Type0)
: Tot pure_pre
= (p ==> pre_f) /\ ((~ p) ==> pre_g)

let read_if_then_else_post
  (a:Type)
  (pre_f pre_g: pure_pre)
  (post_f: pure_post' a pre_f)
  (post_g: pure_post' a pre_g)
  (p:Type0)
: Tot (pure_post' a (read_if_then_else_pre pre_f pre_g p))
= fun x ->
  (p ==> post_f x) /\
  ((~ p) ==> post_g x)

let read_if_then_else (a:Type)
  (pre_f pre_g: pure_pre)
  (post_f: pure_post' a pre_f)
  (post_g: pure_post' a pre_g)
  (l:memory_invariant)
  (f_ifthenelse:read_repr a pre_f post_f l)
  (g:read_repr a pre_g post_g l)
  (p:Type0)
: Tot Type
= read_repr a (read_if_then_else_pre pre_f pre_g p) (read_if_then_else_post a pre_f pre_g post_f post_g p) l

reifiable reflectable total
layered_effect {
  Read : a:Type -> (pre: pure_pre) -> (post: pure_post' a pre) -> (memory_invariant) -> Effect
  with
  repr = read_repr;
  return = read_return;
  bind = read_bind;
  subcomp = read_subcomp;
  if_then_else = read_if_then_else
}

unfold
let lift_pure_read_pre
  (a:Type) (wp:pure_wp a { pure_wp_mono a wp })
: Tot pure_pre
= wp (fun _ -> True)

unfold
let lift_pure_read_post
  (a:Type) (wp:pure_wp a { pure_wp_mono a wp })
: Tot (pure_post' a (lift_pure_read_pre a wp))
= fun x -> ~ (wp (fun x' -> ~ (x == x')))

let lift_pure_read_spec
  (a:Type) (wp:pure_wp a { pure_wp_mono a wp }) (f_pure_spec:unit -> PURE a wp)
: Tot (read_repr_spec a (lift_pure_read_pre a wp) (lift_pure_read_post a wp))
= fun () -> f_pure_spec ()

inline_for_extraction
val lift_pure_read_impl
  (a:Type) (wp:pure_wp a { pure_wp_mono a wp })
  (f_pure_spec_for_impl:unit -> PURE a wp)
  (l: memory_invariant)
: Tot (read_repr_impl a (lift_pure_read_pre a wp) (fun x -> lift_pure_read_post a wp x) l (lift_pure_read_spec a wp f_pure_spec_for_impl))

inline_for_extraction
let lift_pure_read (a:Type) (wp:pure_wp a { pure_wp_mono a wp })
  (l: memory_invariant)
  (f_pure:unit -> PURE a wp)
: Tot (read_repr a (lift_pure_read_pre a wp) (fun x -> lift_pure_read_post a wp x) l)
= (| lift_pure_read_spec a wp f_pure, lift_pure_read_impl a wp f_pure l |)

sub_effect PURE ~> Read = lift_pure_read

inline_for_extraction
val rptr: Type0
val valid_rptr (p: parser) : memory_invariant -> rptr -> GTot Type0

let ptr (p: parser) (inv: memory_invariant) =
  (x: rptr { valid_rptr p inv x })

val deref_spec (#p: parser) (#inv: memory_invariant) (x: ptr p inv) : GTot (dfst p)

inline_for_extraction
val deref_impl
  (#p: parser)
  (#inv: memory_invariant)
  (r: leaf_reader p)
  (x: ptr p inv)
: Tot (read_repr_impl (dfst p) True (fun res -> res == deref_spec x) inv (fun _ -> deref_spec x))

inline_for_extraction
let deref_repr
  (#p: parser)
  (#inv: memory_invariant)
  (r: leaf_reader p)
  (x: ptr p inv)
: Tot (read_repr (dfst p) True (fun res -> res == deref_spec x) inv)
= (| (fun _ -> deref_spec x), deref_impl r x |)

inline_for_extraction
let deref
  (#p: parser)
  (#inv: memory_invariant)
  (r: leaf_reader p)
  (x: ptr p inv)
: Read (dfst p) True (fun res -> res == deref_spec x) inv
= Read?.reflect (deref_repr r x)

val access_spec
  (#p1 #p2: parser)
  (#lens: clens (dfst p1) (dfst p2))
  (#inv: memory_invariant)
  (g: gaccessor p1 p2 lens)
  (x: ptr p1 inv)
: Ghost (ptr p2 inv)
  (requires (lens.clens_cond (deref_spec x)))
  (ensures (fun res -> deref_spec res == lens.clens_get (deref_spec x)))

inline_for_extraction
val access_impl
  (#p1 #p2: parser)
  (#lens: clens (dfst p1) (dfst p2))
  (#inv: memory_invariant)
  (#g: gaccessor p1 p2 lens)
  (a: accessor g)
  (x: ptr p1 inv)
: Tot (read_repr_impl (ptr p2 inv) (lens.clens_cond (deref_spec x)) (fun res -> deref_spec res == lens.clens_get (deref_spec x)) inv (fun _ -> access_spec g x))

inline_for_extraction
let access_repr
  (#p1 #p2: parser)
  (#lens: clens (dfst p1) (dfst p2))
  (#inv: memory_invariant)
  (#g: gaccessor p1 p2 lens)
  (a: accessor g)
  (x: ptr p1 inv)
: Tot (read_repr (ptr p2 inv) (lens.clens_cond (deref_spec x)) (fun res -> deref_spec res == lens.clens_get (deref_spec x)) inv)
= (| (fun _ -> access_spec g x), access_impl a x |)

inline_for_extraction
let access
  (#p1 #p2: parser)
  (#lens: clens (dfst p1) (dfst p2))
  (#inv: memory_invariant)
  (#g: gaccessor p1 p2 lens)
  (a: accessor g)
  (x: ptr p1 inv)
: Read (ptr p2 inv) (lens.clens_cond (deref_spec x)) (fun res -> deref_spec res == lens.clens_get (deref_spec x)) inv
= Read?.reflect (access_repr a x)

unfold
let validate_pre
  (inv: memory_invariant)
  (b: B.buffer U8.t)
: Tot pure_pre
=
  inv.lread `B.loc_includes` B.loc_buffer b /\
  B.live inv.h0 b

unfold
let validate_post
  (p: parser)
  (inv: memory_invariant)
  (b: B.buffer U8.t)
: Tot (pure_post' (option (ptr p inv & U32.t)) (validate_pre inv b))
= fun res ->
  match res with
  | None ->
    forall pos . ~ (valid_pos p inv.h0 b 0ul pos)
  | Some (x, pos) ->
    valid_pos p inv.h0 b 0ul pos /\
    deref_spec x == contents p inv.h0 b 0ul pos

val validate_spec
  (p: parser)
  (inv: memory_invariant)
  (b: B.buffer U8.t)
: Tot (read_repr_spec (option (ptr p inv & U32.t)) (validate_pre inv b) (validate_post p inv b))

inline_for_extraction
val validate_impl
  (#p: parser)
  (v: validator p)
  (inv: memory_invariant)
  (b: B.buffer U8.t)
  (len: U32.t { B.len b == len })
: Tot (read_repr_impl _ _ _ inv (validate_spec p inv b))

inline_for_extraction
let validate_repr
  (#p: parser)
  (v: validator p)
  (inv: memory_invariant)
  (b: B.buffer U8.t)
  (len: U32.t { B.len b == len })
: Tot (read_repr (option (ptr p inv & U32.t)) (validate_pre inv b) (validate_post p inv b) inv)
= (| _, validate_impl v inv b len |)

inline_for_extraction
let validate
  (#p: parser)
  (v: validator p)
  (inv: memory_invariant)
  (b: B.buffer U8.t)
  (len: U32.t { B.len b == len })
: Read (option (ptr p inv & U32.t)) (validate_pre inv b) (validate_post p inv b) inv
= Read?.reflect (validate_repr v inv b len)


let pre_t
  (rin: parser)
: Tot Type
= dfst rin -> GTot Type0

let post_t
  (a: Type)
  (rin: parser)
  (rout: a -> Tot parser)
  (pre: pre_t rin)
: Tot Type
= (x: dfst rin { pre x }) -> (res: a) -> dfst (rout res) -> GTot Type0

inline_for_extraction
let repr_spec (a:Type u#x) (r_in: parser) (r_out:a -> parser) (pre: pre_t r_in) (post: post_t a r_in r_out pre) : Tot (Type u#x) =
  (v_in: dfst r_in) ->
  Ghost (v: a & dfst (r_out v))
  (requires (pre v_in))
  (ensures (fun (| v, v_out |) -> post v_in v v_out /\ size r_in v_in <= size (r_out v) v_out))

inline_for_extraction
val repr_impl
  (a:Type u#x)
  (r_in: parser)
  (r_out:a -> parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (l: memory_invariant)
  (spec: repr_spec a r_in r_out pre post)
: Tot Type0

inline_for_extraction
let repr
  (a: Type u#x)
  (r_in: parser) (r_out:a -> parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (l: memory_invariant)
: Tot (Type u#x)
= dtuple2 (repr_spec a r_in r_out pre post) (repr_impl a r_in r_out pre post l)

// unfold
let return_pre
  (a:Type) (x:a) (r: a -> parser)
: Tot (pre_t (r x))
= fun _ -> True

// unfold
let return_post
  (a:Type) (x:a) (r: a -> parser)
: Tot (post_t a (r x) r (return_pre a x r))
= fun ppre x' ppost -> x' == x /\ ppost == ppre

let return_spec
  (a:Type) (x:a) (r: a -> parser)
: Tot (repr_spec a (r x) r (return_pre a x r) (return_post a x r))
= fun c -> (| x, c |)

inline_for_extraction
val return_impl
  (a:Type) (x:a) (r: a -> parser)
  (l: memory_invariant)
: Tot (repr_impl a (r x) r (return_pre a x r) (return_post a x r) l (return_spec a x r))

inline_for_extraction
let returnc
  (a:Type) (x:a) (r: a -> parser) (l: memory_invariant)
: Tot (repr a (r x) r (return_pre a x r) (return_post a x r) l)
= (| return_spec a x r, return_impl a x r l |)

let bind_pre
  (a:Type) (b:Type)
  (r_in_f:parser) (r_out_f:a -> parser)
  (pre_f:pre_t r_in_f) (post_f: post_t a r_in_f r_out_f pre_f)
  (pre_g: (x:a) ->  pre_t (r_out_f x))
: Tot (pre_t r_in_f)
= fun v_in -> pre_f v_in /\ (forall (x: a) v_out . post_f v_in x v_out ==> pre_g x v_out)

let bind_post
  (a:Type) (b:Type)
  (r_in_f:parser) (r_out_f:a -> parser)
  (pre_f:pre_t r_in_f) (post_f: post_t a r_in_f r_out_f pre_f)
  (r_out_g:b -> parser)
  (pre_g: (x:a) ->  pre_t (r_out_f x))
  (post_g: (x:a) -> post_t b (r_out_f x) r_out_g (pre_g x))
: Tot (post_t b r_in_f r_out_g (bind_pre a b r_in_f r_out_f pre_f post_f pre_g))
= fun v_in y v_out ->
  exists x v_out_f . pre_f v_in /\ post_f v_in x v_out_f /\ post_g x v_out_f y v_out

let bind_spec (a:Type) (b:Type)
  (r_in_f:parser) (r_out_f:a -> parser)
  (pre_f: pre_t r_in_f) (post_f: post_t a r_in_f r_out_f pre_f)
  (r_out_g:b -> parser)
  (pre_g: (x:a) -> pre_t (r_out_f x)) (post_g: (x:a) -> post_t b (r_out_f x) r_out_g (pre_g x))
  (f_bind_spec:repr_spec a r_in_f r_out_f pre_f post_f)
  (g:(x:a -> repr_spec b (r_out_f x) r_out_g (pre_g x) (post_g x)))
: Tot (repr_spec b r_in_f r_out_g (bind_pre a b r_in_f r_out_f pre_f post_f pre_g) (bind_post a b r_in_f r_out_f pre_f post_f r_out_g pre_g post_g))
= fun c ->
  match f_bind_spec c with
  | (| x, cf |) ->
    g x cf

inline_for_extraction
val bind_impl
  (a:Type) (b:Type)
  (r_in_f:parser) (r_out_f:a -> parser)
  (pre_f: pre_t r_in_f) (post_f: post_t a r_in_f r_out_f pre_f)
  (r_out_g:b -> parser)
  (pre_g: (x:a) -> pre_t (r_out_f x)) (post_g: (x:a) -> post_t b (r_out_f x) r_out_g (pre_g x))
  (f_bind_impl:repr_spec a r_in_f r_out_f pre_f post_f)
  (g:(x:a -> repr_spec b (r_out_f x) r_out_g (pre_g x) (post_g x)))
  (l: memory_invariant)
  (f' : repr_impl a r_in_f r_out_f pre_f post_f l f_bind_impl)
  (g' : (x: a -> repr_impl b (r_out_f x) r_out_g (pre_g x) (post_g x) l (g x)))
: Tot (repr_impl b r_in_f r_out_g (bind_pre a b r_in_f r_out_f pre_f post_f pre_g) (bind_post a b r_in_f r_out_f pre_f post_f r_out_g pre_g post_g) l (bind_spec a b r_in_f r_out_f pre_f post_f r_out_g pre_g post_g f_bind_impl g))

inline_for_extraction
let bind (a:Type) (b:Type)
  (r_in_f:parser) (r_out_f:a -> parser)
  (pre_f: pre_t r_in_f) (post_f: post_t a r_in_f r_out_f pre_f)
  (r_out_g:b -> parser)
  (pre_g: (x:a) -> pre_t (r_out_f x)) (post_g: (x:a) -> post_t b (r_out_f x) r_out_g (pre_g x))
  (l: memory_invariant)
  (f_bind : repr a r_in_f r_out_f pre_f post_f l)
  (g : (x: a -> repr b (r_out_f x) r_out_g (pre_g x) (post_g x) l))
: Tot (repr b r_in_f r_out_g (bind_pre a b r_in_f r_out_f pre_f post_f pre_g) (bind_post a b r_in_f r_out_f pre_f post_f r_out_g pre_g post_g) l)
= (| bind_spec a b r_in_f r_out_f pre_f post_f r_out_g pre_g post_g (dfst f_bind) (fun x -> dfst (g x)), bind_impl a b r_in_f r_out_f pre_f post_f r_out_g pre_g post_g (dfst f_bind) (fun x -> dfst (g x)) l (dsnd f_bind) (fun x -> dsnd (g x)) |)

unfold
let subcomp_spec_cond
  (a:Type)
  (r_in:parser) (r_out:a -> parser)
  (pre: pre_t r_in) (post: post_t a r_in r_out pre)
  (pre': pre_t r_in) (post': post_t a r_in r_out pre')
: GTot Type0
= (forall v_in . pre' v_in ==> pre v_in) /\
  (forall v_in x v_out . (pre' v_in /\ post v_in x v_out) ==> post' v_in x v_out)

unfold
let subcomp_cond
  (a:Type)
  (r_in:parser) (r_out:a -> parser)
  (pre: pre_t r_in) (post: post_t a r_in r_out pre)
  (pre': pre_t r_in) (post': post_t a r_in r_out pre')
  (l: memory_invariant)
  (l' : memory_invariant)
: GTot Type0
= l `memory_invariant_includes` l' /\
  subcomp_spec_cond a r_in r_out pre post pre' post'

let subcomp_spec (a:Type)
  (r_in:parser) (r_out:a -> parser)
  (pre: pre_t r_in) (post: post_t a r_in r_out pre)
  (pre': pre_t r_in) (post': post_t a r_in r_out pre')
  (f_subcomp:repr_spec a r_in r_out pre post)
: Pure (repr_spec a r_in r_out pre' post')
  (requires (subcomp_spec_cond a r_in r_out pre post pre' post'))
  (ensures (fun _ -> True))
= (fun x -> f_subcomp x)

inline_for_extraction
val subcomp_impl (a:Type)
  (r_in:parser) (r_out:a -> parser)
  (pre: pre_t r_in) (post: post_t a r_in r_out pre)
  (pre': pre_t r_in) (post': post_t a r_in r_out pre')
  (l:memory_invariant)
  (l' : memory_invariant)
  (f_subcomp_spec:repr_spec a r_in r_out pre post)
  (f_subcomp:repr_impl a r_in r_out pre post l f_subcomp_spec)
  (sq: squash (subcomp_cond a r_in r_out pre post pre' post' l l'))
: Tot (repr_impl a r_in r_out pre' post' l' (subcomp_spec a r_in r_out pre post pre' post' f_subcomp_spec))

inline_for_extraction
let subcomp (a:Type)
  (r_in:parser) (r_out:a -> parser)
  (pre: pre_t r_in) (post: post_t a r_in r_out pre)
  (pre': pre_t r_in) (post': post_t a r_in r_out pre')
  (l:memory_invariant)
  (l' : memory_invariant)
  (f_subcomp:repr a r_in r_out pre post l)
: Pure (repr a r_in r_out pre' post' l')
  (requires (subcomp_cond a r_in r_out pre post pre' post' l l'))
  (ensures (fun _ -> True))
= (| subcomp_spec a r_in r_out pre post pre' post' (dfst f_subcomp),
     subcomp_impl a r_in r_out pre post pre' post' l l' (dfst f_subcomp) (dsnd f_subcomp) ()
  |)

let if_then_else_pre
  (r_in:parser)
  (pre_f pre_g: pre_t r_in)
  (p:Type0)
: Tot (pre_t r_in)
= fun v_in -> (p ==> pre_f v_in) /\ ((~ p) ==> pre_g v_in)

let if_then_else_post
  (a:Type)
  (r_in:parser) (r_out:a -> parser)
  (pre_f pre_g: pre_t r_in)
  (post_f: post_t a r_in r_out pre_f)
  (post_g: post_t a r_in r_out pre_g)
  (p:Type0)
: Tot (post_t a r_in r_out (if_then_else_pre r_in pre_f pre_g p))
= fun v_in x v_out ->
  (p ==> post_f v_in x v_out) /\
  ((~ p) ==> post_g v_in x v_out)

let if_then_else (a:Type)
  (r_in:parser) (r_out:a -> parser)
  (pre_f pre_g: pre_t r_in)
  (post_f: post_t a r_in r_out pre_f)
  (post_g: post_t a r_in r_out pre_g)
  (l:memory_invariant)
  (f_ifthenelse:repr a r_in r_out pre_f post_f l)
  (g:repr a r_in r_out pre_g post_g l)
  (p:Type0)
: Tot Type
= repr a r_in r_out (if_then_else_pre r_in pre_f pre_g p) (if_then_else_post a r_in r_out pre_f pre_g post_f post_g p) l

reifiable reflectable total
layered_effect {
  Write : a:Type -> (pin: parser) -> (pout: (a -> parser)) -> (pre: pre_t pin) -> (post: post_t a pin pout pre) -> (memory_invariant) -> Effect
  with
  repr = repr;
  return = returnc;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}

(*
unfold
let lift_pure_pre
  (a:Type) (wp:pure_wp a { pure_wp_mono a wp }) (r:parser)
: Tot (pre_t r)
= fun st -> wp (fun _ -> True)

unfold
let lift_pure_post
  (a:Type) (wp:pure_wp a { pure_wp_mono a wp }) (r:parser)
: Tot (post_t a r (fun _ -> r) (lift_pure_pre a wp r))
= fun st x st' -> ~ (wp (fun x' -> ~ (st == st' /\ x == x')))

let lift_pure_spec
  (a:Type) (wp:pure_wp a { pure_wp_mono a wp }) (r:parser) (f_pure_spec:unit -> PURE a wp)
: Tot (repr_spec a r (fun _ -> r) (lift_pure_pre a wp r) (lift_pure_post a wp r))
= fun v -> (| f_pure_spec (), v |)

inline_for_extraction
val lift_pure_impl
  (a:Type) (wp:pure_wp a { pure_wp_mono a wp }) (r:parser) (f_pure_spec_for_impl:unit -> PURE a wp)
  (l: memory_invariant)
: Tot (repr_impl a r (fun _ -> r)  (fun v_in -> lift_pure_pre a wp r v_in) (fun v_in x v_out -> lift_pure_post a wp r v_in x v_out) l (lift_pure_spec a wp r f_pure_spec_for_impl))

inline_for_extraction
let lift_pure (a:Type) (wp:pure_wp a { pure_wp_mono a wp }) (r:parser)
  (l: memory_invariant)
  (f_pure:unit -> PURE a wp)
: Tot (repr a r (fun _ -> r) (fun v_in -> lift_pure_pre a wp r v_in) (fun v_in x v_out -> lift_pure_post a wp r v_in x v_out) l)
= (| lift_pure_spec a wp r f_pure, lift_pure_impl a wp r f_pure l |)

sub_effect PURE ~> Write = lift_pure
*)

let lift_read_pre
  (pre: pure_pre)
  (r: parser)
: Tot (pre_t r)
= fun st -> pre

let lift_read_post
  (a: Type)
  (pre: pure_pre)
  (post: pure_post' a pre)
  (r: parser)
: Tot (post_t a r (fun _ -> r) (lift_read_pre pre r))
= fun st x st' -> st == st' /\ post x

let lift_read_spec
  (a: Type)
  (pre: pure_pre)
  (post: pure_post' a pre)
  (inv: memory_invariant)
  (r: parser)
  (f_read_spec: read_repr a pre post inv)
: Tot (repr_spec a r (fun _ -> r) (lift_read_pre pre r) (lift_read_post a pre post r))
= fun st -> (| dfst f_read_spec (), st |)

val lift_read_impl
  (a: Type)
  (pre: pure_pre)
  (post: pure_post' a pre)
  (inv: memory_invariant)
  (r: parser)
  (f_read_spec: read_repr a pre post inv)
: Tot (repr_impl a r (fun _ -> r) (lift_read_pre pre r) (lift_read_post a pre post r) inv (lift_read_spec a pre post inv r f_read_spec))

let lift_read
  (a: Type)
  (pre: pure_pre)
  (post: pure_post' a pre)
  (inv: memory_invariant)
  (r: parser)
  (f_read_spec: read_repr a pre post inv)
: Tot (repr a r (fun _ -> r) (lift_read_pre pre r) (lift_read_post a pre post r) inv)
= (| lift_read_spec a pre post inv r f_read_spec, lift_read_impl a pre post inv r f_read_spec |)

sub_effect Read ~> Write = lift_read

unfold
let destr_repr_spec
  (a:Type u#x)
  (r_in: parser)
  (r_out:a -> parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (l: memory_invariant)
  ($f_destr_spec: unit -> Write a r_in r_out pre post l)
: Tot (repr_spec a r_in r_out pre post)
= dfst (reify (f_destr_spec ()))

inline_for_extraction
let destr_repr_impl
  (a:Type u#x)
  (r_in: parser)
  (r_out:a -> parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (l: memory_invariant)
  (f_destr_spec: unit -> Write a r_in r_out pre post l)
: Tot (repr_impl a r_in r_out pre post l (destr_repr_spec a r_in r_out pre post l f_destr_spec))
= dsnd (reify (f_destr_spec ()))

inline_for_extraction
unfold
let mk_repr
  (a:Type u#x)
  (r_in: parser)
  (r_out:a -> parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (l: memory_invariant)
  (spec: repr_spec a r_in r_out pre post)
  (impl: repr_impl a r_in r_out pre post l spec)
  ()
: Write a r_in r_out pre post l
= Write?.reflect (| spec, impl |)

let frame_out
  (a: Type)
  (frame: parser)
  (p: (a -> Tot parser))
  (x: a)
: Tot parser
= frame `star` (p x)

let frame_pre
  (frame: parser)
  (pre: pre_t emp)
: Tot (pre_t frame)
= fun _ -> pre ()

let frame_post
  (a: Type)
  (frame: parser)
  (pre: pre_t emp)
  (p: a -> parser)
  (post: post_t a emp p pre)
: Tot (post_t a frame (frame_out a frame p) (frame_pre frame pre))
= fun v_in v (v_in', v_out) -> v_in == v_in' /\ post () v v_out

let frame_spec
  (a: Type)
  (frame: parser)
  (pre: pre_t emp)
  (p: a -> parser)
  (post: post_t a emp p pre)
  (l: memory_invariant)
  (inner: unit -> Write a emp p pre post l)
: Tot (repr_spec a frame (frame_out a frame p) (frame_pre frame pre) (frame_post a frame pre p post))
= fun fr ->
  let (| v, w |) = destr_repr_spec a emp p pre post l inner () in
  (| v, (fr, w) |)

inline_for_extraction
val frame_impl
  (a: Type)
  (frame: parser)
  (pre: pre_t emp)
  (p: a -> parser)
  (post: post_t a emp p pre)
  (l: memory_invariant)
  (inner: unit -> Write a emp p pre post l)
: Tot (repr_impl a frame (frame_out a frame p) (frame_pre frame pre) (frame_post a frame pre p post) l (frame_spec a frame pre p post l inner))

inline_for_extraction
let frame'
  (a: Type)
  (frame: parser)
  (pre: pre_t emp)
  (p: a -> parser)
  (post: post_t a emp p pre)
  (l: memory_invariant)
  (inner: unit -> Write a emp p pre post l)
: Tot (unit -> Write a frame (frame_out a frame p) (frame_pre frame pre) (frame_post a frame pre p post) l)
= mk_repr
    a frame (frame_out a frame p) (frame_pre frame pre) (frame_post a frame pre p post) l
    (frame_spec a frame pre p post l inner)
    (frame_impl a frame pre p post l inner)

inline_for_extraction
let frame
  (a: Type)
  (frame: parser)
  (pre: pre_t emp)
  (p: a -> parser)
  (post: post_t a emp p pre)
  (l: memory_invariant)
  (inner: unit -> Write a emp p pre post l)
: Write a frame (frame_out a frame p) (frame_pre frame pre) (frame_post a frame pre p post) l
= frame' a frame pre p post l inner ()

let elem_writer_spec
  (p: parser)
  (x: dfst p)
: Tot (repr_spec unit emp (fun _ -> p) (fun _ -> True) (fun _ _ y -> y == x))
= fun _ -> (| (), x |)

inline_for_extraction
val elem_writer_impl
  (#p: parser)
  (w: leaf_writer p)
  (l: memory_invariant)
  (x: dfst p)
: Tot (repr_impl unit emp (fun _ -> p) (fun _ -> True) (fun _ _ y -> y == x) l (elem_writer_spec p x))

inline_for_extraction
let start
  (#p: parser)
  (w: leaf_writer p)
  (#l: memory_invariant)
  (x: dfst p)
: Write unit emp (fun _ -> p) (fun _ -> True) (fun _ _ y -> y == x) l
= mk_repr
    unit emp (fun _ -> p) (fun _ -> True) (fun _ _ y -> y == x) l
    (elem_writer_spec p x)
    (elem_writer_impl w l x)
    ()

let append
  (#fr: parser)
  (#p: parser)
  (w: leaf_writer p)
  (#l: memory_invariant)
  (x: dfst p)
: Write unit fr (fun _ -> fr `star` p) (fun _ -> True) (fun w _ (w', x') -> w' == w /\ x' == x) l
= frame unit fr (fun _ -> True) (fun _ -> p) (fun _ _ x' -> x' == x) l (fun _ -> start w x)

let write_two_ints
  (l: memory_invariant)
  (x y: U32.t)
: Write unit emp (fun _ -> parse_u32 `star` parse_u32) (fun _ -> True) (fun _ _ (x', y') -> x' == x /\ y' == y) l
= start write_u32 x;
  append write_u32 y

let write_two_ints_2
  (l: memory_invariant)
  (x y: U32.t)
  ()
: Write unit emp (fun _ -> parse_u32 `star` parse_u32) (fun _ -> True) (fun _ _ _ -> True) l
= start write_u32 x;
  append write_u32 y

[@@ expect_failure ] // FIXME: WHY WHY WHY?
let write_two_ints_2_lemma_1
  (l: memory_invariant)
  (x y: U32.t)
: Lemma
  (destr_repr_spec unit emp (fun _ -> parse_u32 `star` parse_u32) (fun _ -> True) (fun _ _ _ -> True) l (write_two_ints_2 l x y) () == (| (), (x, y) |) )
= ()

[@@ expect_failure ] // FIXME: WHY WHY WHY?
let write_two_ints_2_lemma_2
  (l: memory_invariant)
  (x y: U32.t)
: Lemma
  (True)
= assert (dfst (reify (write_two_ints_2 l x y ())) () == (| (), (x, y) |))

let write_two_ints_ifthenelse
  (l: memory_invariant)
  (x y: U32.t)
: Write unit emp (fun _ -> parse_u32 `star` parse_u32) (fun _ -> True) (fun _ _ (x', y') -> x' == x /\ y' == (if U32.v x < U32.v y then x else y)) l
= start write_u32 x;
  if x `U32.lt` y
  then
    append write_u32 x
  else
    append write_u32 y

let write_two_ints_ifthenelse_2_aux
  (l: memory_invariant)
  (x y: U32.t)
  ()
: Write unit emp (fun _ -> parse_u32 `star` parse_u32) (fun _ -> True) (fun _ _ _ -> True) l
= start write_u32 x;
  if x `U32.lt` y
  then
    append write_u32 x
  else
    append write_u32 y

let write_two_ints_ifthenelse_2_aux_lemma
  (l: memory_invariant)
  (x y: U32.t)
: Lemma
  (destr_repr_spec unit emp (fun _ -> parse_u32 `star` parse_u32) (fun _ -> True) (fun _ _ _ -> True) l (write_two_ints_ifthenelse_2_aux l x y) () == (| (), (x, (if U32.v x < U32.v y then x else y)) |) )
= admit () // FIXME: WHY WHY WHY?

unfold
let recast_writer_post
  (a:Type u#x)
  (r_in: parser)
  (r_out:a -> parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (l: memory_invariant)
  (f: unit -> Write a r_in r_out pre post l)
: Tot (post_t a r_in r_out pre)
=
  fun v_in v v_out -> destr_repr_spec a r_in r_out pre post l f v_in == (| v, v_out |) /\ post v_in v v_out

let recast_writer_spec
  (a:Type u#x)
  (r_in: parser)
  (r_out:a -> parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (l: memory_invariant)
  (f: unit -> Write a r_in r_out pre post l)
: Tot (repr_spec a r_in r_out pre (recast_writer_post a r_in r_out pre post l f))
= fun v_in -> destr_repr_spec a r_in r_out pre post l f v_in

inline_for_extraction
val recast_writer_impl
  (a:Type u#x)
  (r_in: parser)
  (r_out:a -> parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (l: memory_invariant)
  (f: unit -> Write a r_in r_out pre post l)
: Tot (repr_impl a r_in r_out pre (recast_writer_post a r_in r_out pre post l f) l (recast_writer_spec a r_in r_out pre post l f))

inline_for_extraction
let recast_writer'
  (a:Type u#x)
  (r_in: parser)
  (r_out:a -> parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (l: memory_invariant)
  (f: unit -> Write a r_in r_out pre post l)
: Tot (unit -> Write a r_in r_out pre (recast_writer_post a r_in r_out pre post l f) l)
= mk_repr a r_in r_out pre (recast_writer_post a r_in r_out pre post l f) l
    (recast_writer_spec a r_in r_out pre post l f)
    (recast_writer_impl a r_in r_out pre post l f)

inline_for_extraction
let recast_writer
  (a:Type u#x)
  (r_in: parser)
  (r_out:a -> parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (l: memory_invariant)
  ($f: unit -> Write a r_in r_out pre post l)
: Write a r_in r_out pre (recast_writer_post a r_in r_out pre post l f) l
= recast_writer' a r_in r_out pre post l f ()

let write_two_ints_ifthenelse_2
  (l: memory_invariant)
  (x y: U32.t)
: Write unit emp (fun _ -> parse_u32 `star` parse_u32)
    (fun _ -> True)
    (fun _ _ (x', y') -> x' == x /\ y' == (if U32.v x < U32.v y then x else y))
    l
= write_two_ints_ifthenelse_2_aux_lemma l x y;
  recast_writer _ _ _ _ _ _ (write_two_ints_ifthenelse_2_aux l x y)

let frame2_pre
  (frame: parser)
  (ppre: parser)
  (pre: pre_t ppre)
: Tot (pre_t (frame `star` ppre))
= fun (_, x) -> pre x

let frame2_post
  (a: Type)
  (frame: parser)
  (ppre: parser)
  (pre: pre_t ppre)
  (p: a -> parser)
  (post: post_t a ppre p pre)
: Tot (post_t a (frame `star` ppre) (frame_out a frame p) (frame2_pre frame ppre pre))
= fun (v_frame, v_in) v (v_frame', v_out) -> v_frame == v_frame' /\ post v_in v v_out

let frame2_spec
  (a: Type)
  (frame: parser)
  (ppre: parser)
  (pre: pre_t ppre)
  (p: a -> parser)
  (post: post_t a ppre p pre)
  (l: memory_invariant)
  (inner: unit -> Write a ppre p pre post l)
: Tot (repr_spec a (frame `star` ppre) (frame_out a frame p) (frame2_pre frame ppre pre) (frame2_post a frame ppre pre p post))
= fun (fr, w_in) ->
  let (| v, w |) = destr_repr_spec a ppre p pre post l inner w_in in
  (| v, (fr, w) |)

inline_for_extraction
val frame2_impl
  (a: Type)
  (frame: parser)
  (ppre: parser)
  (pre: pre_t ppre)
  (p: a -> parser)
  (post: post_t a ppre p pre)
  (l: memory_invariant)
  (inner: unit -> Write a ppre p pre post l)
: Tot (repr_impl a (frame `star` ppre) (frame_out a frame p) (frame2_pre frame ppre pre) (frame2_post a frame ppre pre p post) l (frame2_spec a frame ppre pre p post l inner))

inline_for_extraction
let frame2'
  (a: Type)
  (frame: parser)
  (ppre: parser)
  (pre: pre_t ppre)
  (p: a -> parser)
  (post: post_t a ppre p pre)
  (l: memory_invariant)
  (inner: unit -> Write a ppre p pre post l)
: Tot (unit -> Write a (frame `star` ppre) (frame_out a frame p) (frame2_pre frame ppre pre) (frame2_post a frame ppre pre p post) l)
= mk_repr
    a (frame `star` ppre) (frame_out a frame p) (frame2_pre frame ppre pre) (frame2_post a frame ppre pre p post) l
    (frame2_spec a frame ppre pre p post l inner)
    (frame2_impl a frame ppre pre p post l inner)

inline_for_extraction
let frame2
  (a: Type)
  (frame: parser)
  (ppre: parser)
  (pre: pre_t ppre)
  (p: a -> parser)
  (post: post_t a ppre p pre)
  (l: memory_invariant)
  (inner: unit -> Write a ppre p pre post l)
: Write a (frame `star` ppre) (frame_out a frame p) (frame2_pre frame ppre pre) (frame2_post a frame ppre pre p post) l
= frame2' a frame ppre pre p post l inner ()
