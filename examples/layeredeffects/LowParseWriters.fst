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


open FStar.HyperStack.ST

module HS = FStar.HyperStack
module B = LowStar.Buffer
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module HST = FStar.HyperStack.ST

assume type parser' (t: Type0) : Type0

let parser : Type u#1 = (t: Type0 & parser' t)

inline_for_extraction
let dsnd
  (#u: Type)
  (#v: ((x: u) -> Type))
  (p: dtuple2 u v)
: Tot (v (dfst p))
= match p with (| _, x |) -> x

assume
val valid_pos
  (p: parser)
  (h: HS.mem)
  (b: B.buffer U8.t)
  (pos: U32.t)
  (pos' : U32.t)
: GTot Type0

assume
val valid_pos_post
  (p: parser)
  (h: HS.mem)
  (b: B.buffer U8.t)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (requires (valid_pos p h b pos pos'))
  (ensures (
    B.live h b /\
    U32.v pos <= U32.v pos' /\
    U32.v pos' <= B.length b
  ))
  [SMTPat (valid_pos p h b pos pos')]

assume
val contents
  (p: parser)
  (h: HS.mem)
  (b: B.buffer U8.t)
  (pos: U32.t)
  (pos' : U32.t)
: Ghost (dfst p)
  (requires (valid_pos p h b pos pos'))
  (ensures (fun _ -> True))

unfold
let pure_wp_mono
  (a: Type)
  (wp: pure_wp a)
: GTot Type0
= (forall (p q:pure_post a).
     (forall (x:a). p x ==> q x) ==> (wp p ==> wp q))

let wp_t
  (a: Type u#x)
  (r_in: parser)
  (r_out: a -> parser)
: Tot Type
= (wp: ((dfst r_in) -> Tot (pure_wp (v: a & dfst (r_out v)))) {
    forall x . pure_wp_mono _ (wp x)
  })

inline_for_extraction
let repr_spec (a:Type u#x) (r_in: parser) (r_out:a -> parser) (wp: wp_t a r_in r_out) : Tot (Type u#x) =
  (v_in: dfst r_in) ->
  GHOST (v: a & dfst (r_out v)) (wp v_in)

type u8 : Type0 = U8.t

unfold
let repr_impl_wp
  (a:Type u#x) (r_in: parser) (r_out:a -> parser) (wp: wp_t a r_in r_out) (l: B.loc) (spec: repr_spec a r_in r_out wp)
  (b: B.buffer u8 { l `B.loc_includes` B.loc_buffer b })
  (pos1: U32.t { U32.v pos1 <= B.length b })
: Tot (st_wp_h HS.mem (a & U32.t))
= fun (k: st_post_h HS.mem (a & U32.t)) (h: HS.mem) ->
  valid_pos r_in h b 0ul pos1 /\
  wp (contents r_in h b 0ul pos1) (fun y' ->
  forall (v: a) (pos2: U32.t) (h': HS.mem) .
  (
    U32.v pos1 <= U32.v pos2 /\
    valid_pos (r_out v) h' b 0ul pos2 /\
    B.modifies (B.loc_buffer_from_to b 0ul pos2) h h' /\
    y' == (| v, contents (r_out v) h' b 0ul pos2 |) /\
    HST.equal_domains h h'
  ) ==> (
    k (v, pos2) h'
  ))

inline_for_extraction
let repr_impl (a:Type u#x) (r_in: parser) (r_out:a -> parser) (wp: wp_t a r_in r_out) (l: B.loc) (spec: repr_spec a r_in r_out wp) : Tot Type0 =
  (b: B.buffer u8 { l `B.loc_includes` B.loc_buffer b }) ->
  (pos1: U32.t { U32.v pos1 <= B.length b }) ->
  HST.STATE (a & U32.t) (repr_impl_wp a r_in r_out wp l spec b pos1)

inline_for_extraction
let repr
  (a: Type u#x)
  (r_in: parser) (r_out:a -> parser)
  (wp: wp_t a r_in r_out)
  (l: B.loc)
: Tot (Type u#x)
= dtuple2 (repr_spec a r_in r_out wp) (repr_impl a r_in r_out wp l)

unfold
let return_wp
  (a:Type) (x:a) (r: a -> parser)
: Tot (wp_t a (r x) r)
= fun c p -> p (| x, c |)

let return_spec
  (a:Type) (x:a) (r: a -> parser)
: Tot (repr_spec a (r x) r (return_wp a x r))
= fun c -> (| x, c |)

inline_for_extraction
let return_impl
  (a:Type) (x:a) (r: a -> parser)
  (l: B.loc)
: Tot (repr_impl a (r x) r (return_wp a x r) l (return_spec a x r))
= fun b pos1 -> (x, pos1)

inline_for_extraction
let returnc
  (a:Type) (x:a) (r: a -> parser) (l: B.loc)
: Tot (repr a (r x) r (return_wp a x r) l)
= (| return_spec a x r, return_impl a x r l |)

unfold
let bind_wp
  (a:Type) (b:Type)
  (r_in_f:parser) (r_out_f:a -> parser) (r_wp_f: wp_t a r_in_f r_out_f)
  (r_out_g:b -> parser)
  (r_wp_g: (x:a -> wp_t b (r_out_f x) r_out_g))
: Tot (wp_t b r_in_f r_out_g)
=
  fun r0 p -> r_wp_f r0 (fun xr1 -> match xr1 with (| x, r1 |) -> r_wp_g x r1 p)

let bind_spec (a:Type) (b:Type)
  (r_in_f:parser) (r_out_f:a -> parser) (r_wp_f: wp_t a r_in_f r_out_f)
  (r_out_g:b -> parser)
  (r_wp_g: (x:a -> wp_t b (r_out_f x) r_out_g))
  (f:repr_spec a r_in_f r_out_f r_wp_f) (g:(x:a -> repr_spec b (r_out_f x) r_out_g (r_wp_g x)))
: Tot (repr_spec b r_in_f r_out_g (bind_wp a b r_in_f r_out_f r_wp_f r_out_g r_wp_g))
= fun c ->
  match f c with
  | (| x, cf |) ->
    g x cf

let loc_includes_loc_buffer_loc_buffer_from_to
  (#a: _) (#rrel #rel: _)
  (b: B.mbuffer a rrel rel)
  (from to: U32.t)
: Lemma
  (B.loc_includes (B.loc_buffer b) (B.loc_buffer_from_to b from to))
  [SMTPat (B.loc_includes (B.loc_buffer b) (B.loc_buffer_from_to b from to))]
= B.loc_includes_loc_buffer_loc_buffer_from_to b from to

let loc_includes_loc_buffer_from_to
  (#a: _) (#rrel #rel: _)
  (b: B.mbuffer a rrel rel)
  (from1 to1 from2 to2: U32.t)
: Lemma
  (requires (U32.v from1 <= U32.v from2 /\ U32.v to2 <= U32.v to1))
  (ensures (B.loc_includes (B.loc_buffer_from_to b from1 to1) (B.loc_buffer_from_to b from2 to2)))
  [SMTPat (B.loc_includes (B.loc_buffer_from_to b from1 to1) (B.loc_buffer_from_to b from2 to2))]
= B.loc_includes_loc_buffer_from_to b from1 to1 from2 to2

inline_for_extraction
let bind_impl
  (a:Type) (b:Type)
  (r_in_f:parser) (r_out_f:a -> parser) (r_wp_f: wp_t a r_in_f r_out_f)
  (r_out_g:b -> parser)
  (r_wp_g: (x:a -> wp_t b (r_out_f x) r_out_g))
  (f:repr_spec a r_in_f r_out_f r_wp_f)
  (g:(x:a -> repr_spec b (r_out_f x) r_out_g (r_wp_g x)))
  (l: B.loc)
  (f' : repr_impl a r_in_f r_out_f r_wp_f l f)
  (g' : (x: a -> repr_impl b (r_out_f x) r_out_g (r_wp_g x) l (g x)))
: Tot (repr_impl b r_in_f r_out_g (bind_wp a b r_in_f r_out_f r_wp_f r_out_g r_wp_g) l (bind_spec a b r_in_f r_out_f r_wp_f r_out_g r_wp_g f g))
= fun buf pos ->
  match f' buf pos with
  | (x, posf) -> g' x buf posf

inline_for_extraction
let bind (a:Type) (b:Type)
  (r_in_f:parser) (r_out_f:a -> parser) (r_wp_f: wp_t a r_in_f r_out_f)
  (r_out_g:b -> parser)
  (r_wp_g: (x:a -> wp_t b (r_out_f x) r_out_g))
  (l: B.loc)
  (f:repr a r_in_f r_out_f r_wp_f l) (g:(x:a -> repr b (r_out_f x) r_out_g (r_wp_g x) l))
: Tot (repr b r_in_f r_out_g (bind_wp a b r_in_f r_out_f r_wp_f r_out_g r_wp_g) l)
= (| bind_spec a b r_in_f r_out_f r_wp_f r_out_g r_wp_g (dfst f) (fun x -> dfst (g x)), bind_impl a b r_in_f r_out_f r_wp_f r_out_g r_wp_g (dfst f) (fun x -> dfst (g x)) l (dsnd f) (fun x -> dsnd (g x)) |)

inline_for_extraction
let subcomp (a:Type)
  (r_in:parser) (r_out:a -> parser) (r_wp: wp_t a r_in r_out)
  (r_wp': wp_t a r_in r_out)
  (l:B.loc)
  (l' : B.loc)
  (f:repr a r_in r_out r_wp l)
: Pure (repr a r_in r_out r_wp' l')
  (requires (l `B.loc_includes` l' /\ (forall x p . r_wp' x p ==> r_wp x p)))
  (ensures (fun _ -> True))
= (| (fun x -> dfst f x), (fun pos -> dsnd f pos) |)

unfold
let if_then_else_wp
  (a:Type)
  (r_in:parser) (r_out:a -> parser) (r_wp_f r_wp_g: wp_t a r_in r_out) 
  (p:Type0)
: Tot (wp_t a r_in r_out)
= fun s k ->
  (p ==> r_wp_f s k) /\
  ((~ p) ==> r_wp_g s k)

let if_then_else (a:Type)
  (r_in:parser) (r_out:a -> parser) (r_wp_f r_wp_g: wp_t a r_in r_out) 
  (l:B.loc)
  (f:repr a r_in r_out r_wp_f l) (g:repr a r_in r_out r_wp_g l)
  (p:Type0)
: Tot Type
= repr a r_in r_out (if_then_else_wp a r_in r_out r_wp_f r_wp_g p) l

#push-options "--print_universes"

reifiable reflectable total
layered_effect {
  WRITE : a:Type -> (pin: parser) -> (pout: (a -> parser)) -> (wp: wp_t a pin pout) -> (B.loc) -> Effect
  with
  repr = repr;
  return = returnc;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}

#pop-options

inline_for_extraction
let mk_repr
  (a:Type u#x)
  (r_in: parser)
  (r_out:a -> parser)
  (wp: wp_t a r_in r_out)
  (l: B.loc)
  (spec: repr_spec a r_in r_out wp)
  (impl: repr_impl a r_in r_out wp l spec)
: WRITE a r_in r_out wp l
= WRITE?.reflect (| spec, impl |)

unfold
let lift_pure_wp
  (a:Type) (wp:pure_wp a { pure_wp_mono a wp }) (r:parser)
: Tot (wp_t a r (fun _ -> r))
= fun st p -> wp (fun res -> p (| res, st |))

let lift_pure_spec
  (a:Type) (wp:pure_wp a { pure_wp_mono a wp }) (r:parser) (f:unit -> PURE a wp)
: Tot (repr_spec a r (fun _ -> r) (lift_pure_wp a wp r))
= fun v -> (| f (), v |)

let lift_pure_impl
  (a:Type) (wp:pure_wp a { pure_wp_mono a wp }) (r:parser) (f:unit -> PURE a wp)
  (l: B.loc)
: Tot (repr_impl a r (fun _ -> r) (lift_pure_wp a wp r) l (lift_pure_spec a wp r f))
= fun buf pos -> (f (), pos)

let lift_pure (a:Type) (wp:pure_wp a { pure_wp_mono a wp }) (r:parser)
  (l: B.loc)
  (f:unit -> PURE a wp)
: Pure (repr a r (fun _ -> r) (lift_pure_wp a wp r) l)
  (requires wp (fun _ -> True))
  (ensures fun _ -> True)
= (| lift_pure_spec a wp r f, lift_pure_impl a wp r f l |)

sub_effect PURE ~> WRITE = lift_pure

inline_for_extraction
let destr_repr_spec
  (a:Type u#x)
  (r_in: parser)
  (r_out:a -> parser)
  (wp: wp_t a r_in r_out)
  (l: B.loc)
  (f: unit -> WRITE a r_in r_out wp l)
: Tot (repr_spec a r_in r_out wp)
= dfst (reify (f ()))

inline_for_extraction
let destr_repr_impl
  (a:Type u#x)
  (r_in: parser)
  (r_out:a -> parser)
  (wp: wp_t a r_in r_out)
  (l: B.loc)
  (f: unit -> WRITE a r_in r_out wp l)
: Tot (repr_impl a r_in r_out wp l (destr_repr_spec a r_in r_out wp l f))
= dsnd (reify (f ()))

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

unfold
let hoare_to_wp
  (a: Type)
  (rin: parser)
  (rout: a -> Tot parser)
  (pre: pre_t rin)
  (post: post_t a rin rout pre)
: Tot (wp_t a rin rout)
= fun x p ->
  pre x /\
  (forall (res: a) x' . post x res x' ==> p (| res, x' |))

effect Write (a: Type) (rin: parser) (rout: a -> Tot parser) (l: B.loc) (pre: pre_t rin) (post: post_t a rin rout pre) =
  WRITE a rin rout (hoare_to_wp a rin rout pre post) l

inline_for_extraction
unfold
let repr_hoare_spec
  (a:Type u#x)
  (r_in: parser)
  (r_out:a -> parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
: Tot (Type u#x)
=
  (v_in: dfst r_in) ->
  Ghost (v: a & dfst (r_out v))
  (requires (pre v_in))
  (ensures (fun (| v, v_out |) -> post v_in v v_out))

unfold
let repr_spec_of_repr_hoare_spec
  (a:Type u#x)
  (r_in: parser)
  (r_out:a -> parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (f: repr_hoare_spec a r_in r_out pre post)
: Tot (repr_spec a r_in r_out (hoare_to_wp a r_in r_out pre post))
= fun v_in -> f v_in

unfold
let repr_hoare_impl_post
  (a:Type u#x)
  (r_in: parser)
  (r_out:a -> parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (l: B.loc)
  (spec: repr_hoare_spec a r_in r_out pre post)
  (b: B.buffer u8 { l `B.loc_includes` B.loc_buffer b })
  (pos1: U32.t { U32.v pos1 <= B.length b })
  (h: HS.mem)
  (v: a)
  (pos2: U32.t)
  (h' : HS.mem)
: GTot Type0
= 
    valid_pos r_in h b 0ul pos1 /\ (
    let v_in = contents r_in h b 0ul pos1 in
    pre v_in /\
    U32.v pos1 <= U32.v pos2 /\
    valid_pos (r_out v) h' b 0ul pos2 /\ (
    let v_out = contents (r_out v) h' b 0ul pos2 in
    B.modifies (B.loc_buffer_from_to b 0ul pos2) h h' /\
    spec v_in == (| v, v_out |)
  ))

let buffer_offset
  (#t: Type)
  (b: B.buffer t)
: Tot Type0
= pos1: U32.t { U32.v pos1 <= B.length b }

inline_for_extraction
unfold
let repr_hoare_impl
  (a:Type u#x)
  (r_in: parser)
  (r_out:a -> parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (l: B.loc)
  (spec: repr_hoare_spec a r_in r_out pre post)
: Tot Type0 =
  (b: B.buffer u8 { l `B.loc_includes` B.loc_buffer b }) ->
  (pos1: buffer_offset b) ->
  HST.Stack (a & U32.t)
  (requires (fun h ->
    valid_pos r_in h b 0ul pos1 /\
    pre (contents r_in h b 0ul pos1)
  ))
  (ensures (fun h (v, pos2) h' ->
    repr_hoare_impl_post a r_in r_out pre post l spec b pos1 h v pos2 h'
  ))

inline_for_extraction
let repr_impl_of_repr_hoare_impl
  (a:Type u#x)
  (r_in: parser)
  (r_out:a -> parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (l: B.loc)
  (spec: repr_hoare_spec a r_in r_out pre post)
  (impl: repr_hoare_impl a r_in r_out pre post l spec)
: Tot (repr_impl a r_in r_out (hoare_to_wp a r_in r_out pre post) l (repr_spec_of_repr_hoare_spec a r_in r_out pre post spec))
= fun b pos1 -> impl b pos1

inline_for_extraction
let mk_repr_hoare
  (a:Type u#x)
  (r_in: parser)
  (r_out:a -> parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (l: B.loc)
  (spec: repr_hoare_spec a r_in r_out pre post)
  (impl: repr_hoare_impl a r_in r_out pre post l spec)
  ()
: Write a r_in r_out l pre post
= mk_repr a r_in r_out (hoare_to_wp a r_in r_out pre post) l (repr_spec_of_repr_hoare_spec a r_in r_out pre post spec) (repr_impl_of_repr_hoare_impl a r_in r_out pre post l spec impl)

let reify_repr_hoare_spec
  (a:Type u#x)
  (r_in: parser)
  (r_out:a -> parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (l: B.loc)
  (w: unit -> Write a r_in r_out l pre post)
: Tot (repr_hoare_spec a r_in r_out pre post)
= fun v_in -> dfst (reify (w ())) v_in

inline_for_extraction
let reify_repr_hoare_impl
  (a:Type u#x)
  (r_in: parser)
  (r_out:a -> parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (l: B.loc)
  (w: unit -> Write a r_in r_out l pre post)
: Tot (repr_hoare_impl a r_in r_out pre post l (reify_repr_hoare_spec a r_in r_out pre post l w))
= fun b pos ->
  // [@inline_let]
  let (| spec, impl |) = reify (w ()) in
  let h = HST.get () in
  let (v, pos') = impl b pos in
  let h' = HST.get () in
  let v_in = Ghost.hide (contents r_in h b 0ul pos) in
  let v_out = Ghost.hide (contents (r_out v) h' b 0ul pos') in
  assume (spec v_in == (| v, Ghost.reveal v_out |)); // by (FStar.Tactics.fail "abc"); // FIXME: WHY WHY WHY can't I derive that from the wp?
  (v, pos')

assume
val emp' : parser' unit

let emp : parser = (| unit, emp' |)

assume
val valid_emp
  (h: HS.mem)
  (b: B.buffer u8)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (
    valid_pos emp h b pos pos' <==> (
    B.live h b /\
    U32.v pos <= B.length b /\
    U32.v pos' == U32.v pos
  ))
  [SMTPat (valid_pos emp h b pos pos')]

assume
val star' (#t1 #t2: Type) (p1: parser' t1) (p2: parser' t2) : Tot (parser' (t1 & t2))

let star (p1 p2: parser) : Tot parser = (| (dfst p1 & dfst p2), star' (dsnd p1) (dsnd p2) |)

assume
val valid_star
  (p1 p2: parser)
  (h: HS.mem)
  (b: B.buffer U8.t)
  (pos1 pos2 pos3: U32.t)
: Lemma
  (requires (
    valid_pos p1 h b pos1 pos2 /\
    valid_pos p2 h b pos2 pos3
  ))
  (ensures (
    valid_pos p1 h b pos1 pos2 /\
    valid_pos p2 h b pos2 pos3 /\
    valid_pos (p1 `star` p2) h b pos1 pos3 /\
    contents (p1 `star` p2) h b pos1 pos3 == (contents p1 h b pos1 pos2, contents p2 h b pos2 pos3)
  ))

assume
val valid_frame
  (p: parser)
  (h: HS.mem)
  (b: B.buffer U8.t)
  (pos: U32.t)
  (pos' : U32.t)
  (l: B.loc)
  (h' : HS.mem)
: Lemma
  (requires (
    valid_pos p h b pos pos' /\
    B.modifies l h h' /\
    B.loc_disjoint l (B.loc_buffer_from_to b pos pos')
  ))
  (ensures (
    valid_pos p h b pos pos' /\
    valid_pos p h' b pos pos' /\
    contents p h' b pos pos' == contents p h b pos pos'
  ))

assume
val valid_gsub
  (p: parser)
  (h: HS.mem)
  (b: B.buffer U8.t)
  (pos0 pos1 pos2: U32.t)
  (len: U32.t)
: Lemma
  (requires (
    U32.v pos0 + U32.v len <= B.length b /\
    valid_pos p h (B.gsub b pos0 len) pos1 pos2
  ))
  (ensures (
    U32.v pos0 + U32.v pos2 <= B.length b /\
    valid_pos p h (B.gsub b pos0 len) pos1 pos2 /\
    valid_pos p h b (pos0 `U32.add` pos1) (pos0 `U32.add` pos2) /\
    contents p h b (pos0 `U32.add` pos1) (pos0 `U32.add` pos2) == contents p h (B.gsub b pos0 len) pos1 pos2
  ))
  [SMTPat (valid_pos p h (B.gsub b pos0 len) pos1 pos2)]

let frame_out
  (a: Type)
  (frame: parser)
  (p: (a -> Tot parser))
  (x: a)
: Tot parser
= frame `star` (p x)

unfold
let frame_pre
  (a: Type)
  (frame: parser)
  (pre: pre_t emp)
: Tot (pre_t frame)
= fun _ -> pre ()

unfold
let frame_post
  (a: Type)
  (frame: parser)
  (pre: pre_t emp)
  (p: a -> parser)
  (post: post_t a emp p pre)
: Tot (post_t a frame (frame_out a frame p) (frame_pre a frame pre))
= fun _ v (_, v_out) -> post () v v_out

let frame_spec
  (a: Type)
  (frame: parser)
  (pre: pre_t emp)
  (p: a -> parser)
  (post: post_t a emp p pre)
  (l: B.loc)
  (inner: unit -> Write a emp p l pre post)
: Tot (repr_hoare_spec a frame (frame_out a frame p) (frame_pre a frame pre) (frame_post a frame pre p post))
= fun fr ->
  let (| v, w |) = reify_repr_hoare_spec a emp p pre post l inner () in
  (| v, (fr, w) |)

inline_for_extraction
let frame_impl
  (a: Type)
  (frame: parser)
  (pre: pre_t emp)
  (p: a -> parser)
  (post: post_t a emp p pre)
  (l: B.loc)
  (inner: unit -> Write a emp p l pre post)
: Tot (repr_hoare_impl a frame (frame_out a frame p) (frame_pre a frame pre) (frame_post a frame pre p post) l (frame_spec a frame pre p post l inner))
= fun buf pos ->
  let h = HST.get () in
  let buf' = B.offset buf pos in
  let (x, len) = reify_repr_hoare_impl a emp p pre post l inner buf' 0ul in
  let h' = HST.get () in
  let pos' = pos `U32.add` len in
  B.loc_disjoint_loc_buffer_from_to buf 0ul pos pos len;
  valid_frame frame h buf 0ul pos (B.loc_buffer_from_to buf' 0ul len) h';
  valid_star frame (p x) h' buf 0ul pos pos' ;
  (x, pos')

inline_for_extraction
let frame'
  (a: Type)
  (frame: parser)
  (pre: pre_t emp)
  (p: a -> parser)
  (post: post_t a emp p pre)
  (l: B.loc)
  (inner: unit -> Write a emp p l pre post)
: Tot (unit -> Write a frame (frame_out a frame p) l (frame_pre a frame pre) (frame_post a frame pre p post))
= mk_repr_hoare
    a frame (frame_out a frame p) (frame_pre a frame pre) (frame_post a frame pre p post) l
    (frame_spec a frame pre p post l inner)
    (frame_impl a frame pre p post l inner)

inline_for_extraction
let frame
  (a: Type)
  (frame: parser)
  (pre: pre_t emp)
  (p: a -> parser)
  (post: post_t a emp p pre)
  (l: B.loc)
  (inner: unit -> Write a emp p l pre post)
: Write a frame (frame_out a frame p) l (frame_pre a frame pre) (frame_post a frame pre p post)
= frame' a frame pre p post l inner ()

assume
val parse_u32' : parser' U32.t

let parse_u32 : parser = (| U32.t , parse_u32' |)

assume
val write_u32
  (#l: B.loc)
  (x: U32.t)
: Write unit emp (fun _ -> parse_u32) l (fun _ -> True) (fun _ _ y -> y == x)  

#push-options "--admit_smt_queries true"
let frame_write_u32
  (#fr: parser)
  (#l: B.loc)
  (x: U32.t)
: Write unit fr (fun _ -> fr `star` parse_u32) l (fun _ -> True) (fun w _ (w', x') -> w' == w /\ x' == x)
= frame unit fr (fun _ -> True) (fun _ -> parse_u32) (fun _ _ x' -> x' == x) l (fun _ -> write_u32 #l x)
#pop-options

let write_two_ints
  (l: B.loc)
  (x y: U32.t)
: Write unit emp (fun _ -> parse_u32 `star` parse_u32) l (fun _ -> True) (fun _ _ (x', y') -> x' == x /\ y' == y)
= write_u32 x;
  frame_write_u32 y

let write_two_ints_ifthenelse
  (l: B.loc)
  (x y: U32.t)
: Write unit emp (fun _ -> parse_u32 `star` parse_u32) l (fun _ -> True) (fun _ _ (x', y') -> x' == x /\ y' == (if U32.v x < U32.v y then x else y))
= write_u32 x;
  if x `U32.lt` y
  then
    frame_write_u32 x
  else
    frame_write_u32 y
