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
  (ensures (fun (| v, v_out |) -> post v_in v v_out))

type u8 : Type0 = U8.t

unfold
let repr_impl_post
  (a:Type u#x)
  (r_in: parser)
  (r_out:a -> parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (l: B.loc)
  (spec: repr_spec a r_in r_out pre post)
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
let repr_impl
  (a:Type u#x)
  (r_in: parser)
  (r_out:a -> parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (l: B.loc)
  (spec: repr_spec a r_in r_out pre post)
: Tot Type0 =
  (b: B.buffer u8 { l `B.loc_includes` B.loc_buffer b }) ->
  (pos1: buffer_offset b) ->
  HST.Stack (a & U32.t)
  (requires (fun h ->
    valid_pos r_in h b 0ul pos1 /\
    pre (contents r_in h b 0ul pos1)
  ))
  (ensures (fun h (v, pos2) h' ->
    repr_impl_post a r_in r_out pre post l spec b pos1 h v pos2 h'
  ))

inline_for_extraction
let repr
  (a: Type u#x)
  (r_in: parser) (r_out:a -> parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (l: B.loc)
: Tot (Type u#x)
= dtuple2 (repr_spec a r_in r_out pre post) (repr_impl a r_in r_out pre post l)

unfold
let return_pre
  (a:Type) (x:a) (r: a -> parser)
: Tot (pre_t (r x))
= fun _ -> True

unfold
let return_post
  (a:Type) (x:a) (r: a -> parser)
: Tot (post_t a (r x) r (return_pre a x r))
= fun ppre x' ppost -> x' == x /\ ppost == ppre

let return_spec
  (a:Type) (x:a) (r: a -> parser)
: Tot (repr_spec a (r x) r (return_pre a x r) (return_post a x r))
= fun c -> (| x, c |)

inline_for_extraction
let return_impl
  (a:Type) (x:a) (r: a -> parser)
  (l: B.loc)
: Tot (repr_impl a (r x) r (return_pre a x r) (return_post a x r) l (return_spec a x r))
= fun b pos1 -> (x, pos1)

inline_for_extraction
let returnc
  (a:Type) (x:a) (r: a -> parser) (l: B.loc)
: Tot (repr a (r x) r (return_pre a x r) (return_post a x r) l)
= (| return_spec a x r, return_impl a x r l |)

unfold
let bind_pre
  (a:Type) (b:Type)
  (r_in_f:parser) (r_out_f:a -> parser)
  (pre_f:pre_t r_in_f) (post_f: post_t a r_in_f r_out_f pre_f)
  (pre_g: (x:a) ->  pre_t (r_out_f x))
: Tot (pre_t r_in_f)
= fun v_in -> pre_f v_in /\ (forall (x: a) v_out . post_f v_in x v_out ==> pre_g x v_out)

unfold
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
  (r_in_f:parser) (r_out_f:a -> parser)
  (pre_f: pre_t r_in_f) (post_f: post_t a r_in_f r_out_f pre_f)
  (r_out_g:b -> parser)
  (pre_g: (x:a) -> pre_t (r_out_f x)) (post_g: (x:a) -> post_t b (r_out_f x) r_out_g (pre_g x))
  (f_bind_impl:repr_spec a r_in_f r_out_f pre_f post_f)
  (g:(x:a -> repr_spec b (r_out_f x) r_out_g (pre_g x) (post_g x)))
  (l: B.loc)
  (f' : repr_impl a r_in_f r_out_f pre_f post_f l f_bind_impl)
  (g' : (x: a -> repr_impl b (r_out_f x) r_out_g (pre_g x) (post_g x) l (g x)))
: Tot (repr_impl b r_in_f r_out_g (bind_pre a b r_in_f r_out_f pre_f post_f pre_g) (bind_post a b r_in_f r_out_f pre_f post_f r_out_g pre_g post_g) l (bind_spec a b r_in_f r_out_f pre_f post_f r_out_g pre_g post_g f_bind_impl g))
= fun buf pos ->
  match f' buf pos with
  | (x, posf) -> g' x buf posf

inline_for_extraction
let bind (a:Type) (b:Type)
  (r_in_f:parser) (r_out_f:a -> parser)
  (pre_f: pre_t r_in_f) (post_f: post_t a r_in_f r_out_f pre_f)
  (r_out_g:b -> parser)
  (pre_g: (x:a) -> pre_t (r_out_f x)) (post_g: (x:a) -> post_t b (r_out_f x) r_out_g (pre_g x))
  (l: B.loc)
  (f_bind : repr a r_in_f r_out_f pre_f post_f l)
  (g : (x: a -> repr b (r_out_f x) r_out_g (pre_g x) (post_g x) l))
: Tot (repr b r_in_f r_out_g (bind_pre a b r_in_f r_out_f pre_f post_f pre_g) (bind_post a b r_in_f r_out_f pre_f post_f r_out_g pre_g post_g) l)
= (| bind_spec a b r_in_f r_out_f pre_f post_f r_out_g pre_g post_g (dfst f_bind) (fun x -> dfst (g x)), bind_impl a b r_in_f r_out_f pre_f post_f r_out_g pre_g post_g (dfst f_bind) (fun x -> dfst (g x)) l (dsnd f_bind) (fun x -> dsnd (g x)) |)

unfold
let subcomp_cond
  (a:Type)
  (r_in:parser) (r_out:a -> parser)
  (pre: pre_t r_in) (post: post_t a r_in r_out pre)
  (pre': pre_t r_in) (post': post_t a r_in r_out pre')
  (l:B.loc)
  (l' : B.loc)
: GTot Type0
= l `B.loc_includes` l' /\
  (forall v_in . pre' v_in ==> pre v_in) /\
  (forall v_in x v_out . (pre' v_in /\ post v_in x v_out) ==> post' v_in x v_out)

inline_for_extraction
let subcomp (a:Type)
  (r_in:parser) (r_out:a -> parser)
  (pre: pre_t r_in) (post: post_t a r_in r_out pre)
  (pre': pre_t r_in) (post': post_t a r_in r_out pre')
  (l:B.loc)
  (l' : B.loc)
  (f_subcomp:repr a r_in r_out pre post l)
: Pure (repr a r_in r_out pre' post' l')
  (requires (subcomp_cond a r_in r_out pre post pre' post' l l'))
  (ensures (fun _ -> True))
= (| (fun x -> dfst f_subcomp x), (fun pos -> dsnd f_subcomp pos) |)

unfold
let if_then_else_pre
  (r_in:parser)
  (pre_f pre_g: pre_t r_in)
  (p:Type0)
: Tot (pre_t r_in)
= fun v_in -> (p ==> pre_f v_in) /\ ((~ p) ==> pre_g v_in)

unfold
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
  (l:B.loc)
  (f_ifthenelse:repr a r_in r_out pre_f post_f l)
  (g:repr a r_in r_out pre_g post_g l)
  (p:Type0)
: Tot Type
= repr a r_in r_out (if_then_else_pre r_in pre_f pre_g p) (if_then_else_post a r_in r_out pre_f pre_g post_f post_g p) l

#push-options "--print_universes"

reifiable reflectable total
layered_effect {
  Write : a:Type -> (pin: parser) -> (pout: (a -> parser)) -> (pre: pre_t pin) -> (post: post_t a pin pout pre) -> (B.loc) -> Effect
  with
  repr = repr;
  return = returnc;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}

#pop-options

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

let lift_pure_impl
  (a:Type) (wp:pure_wp a { pure_wp_mono a wp }) (r:parser) (f_pure_spec_for_impl:unit -> PURE a wp)
  (l: B.loc)
: Tot (repr_impl a r (fun _ -> r) (lift_pure_pre a wp r) (lift_pure_post a wp r) l (lift_pure_spec a wp r f_pure_spec_for_impl))
= fun buf pos -> (f_pure_spec_for_impl (), pos)

let lift_pure (a:Type) (wp:pure_wp a { pure_wp_mono a wp }) (r:parser)
  (l: B.loc)
  (f_pure:unit -> PURE a wp)
: Tot (repr a r (fun _ -> r) (lift_pure_pre a wp r) (lift_pure_post a wp r) l)
= (| lift_pure_spec a wp r f_pure, lift_pure_impl a wp r f_pure l |)

sub_effect PURE ~> Write = lift_pure

inline_for_extraction
let destr_repr_spec
  (a:Type u#x)
  (r_in: parser)
  (r_out:a -> parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (l: B.loc)
  (f_destr_spec: unit -> Write a r_in r_out pre post l)
: Tot (repr_spec a r_in r_out pre post)
= dfst (reify (f_destr_spec ()))

inline_for_extraction
let destr_repr_impl
  (a:Type u#x)
  (r_in: parser)
  (r_out:a -> parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (l: B.loc)
  (f_destr_spec: unit -> Write a r_in r_out pre post l)
: Tot (repr_impl a r_in r_out pre post l (destr_repr_spec a r_in r_out pre post l f_destr_spec))
= dsnd (reify (f_destr_spec ()))

inline_for_extraction
let mk_repr
  (a:Type u#x)
  (r_in: parser)
  (r_out:a -> parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (l: B.loc)
  (spec: repr_spec a r_in r_out pre post)
  (impl: repr_impl a r_in r_out pre post l spec)
  ()
: Write a r_in r_out pre post l
= Write?.reflect (| spec, impl |)


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
= fun v_in v (v_in', v_out) -> v_in == v_in' /\ post () v v_out

let frame_spec
  (a: Type)
  (frame: parser)
  (pre: pre_t emp)
  (p: a -> parser)
  (post: post_t a emp p pre)
  (l: B.loc)
  (inner: unit -> Write a emp p pre post l)
: Tot (repr_spec a frame (frame_out a frame p) (frame_pre a frame pre) (frame_post a frame pre p post))
= fun fr ->
  let (| v, w |) = destr_repr_spec a emp p pre post l inner () in
  (| v, (fr, w) |)

inline_for_extraction
let frame_impl
  (a: Type)
  (frame: parser)
  (pre: pre_t emp)
  (p: a -> parser)
  (post: post_t a emp p pre)
  (l: B.loc)
  (inner: unit -> Write a emp p pre post l)
: Tot (repr_impl a frame (frame_out a frame p) (frame_pre a frame pre) (frame_post a frame pre p post) l (frame_spec a frame pre p post l inner))
= fun buf pos ->
  let h = HST.get () in
  let buf' = B.offset buf pos in
  let (x, len) = destr_repr_impl a emp p pre post l inner buf' 0ul in
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
  (inner: unit -> Write a emp p pre post l)
: Tot (unit -> Write a frame (frame_out a frame p) (frame_pre a frame pre) (frame_post a frame pre p post) l)
= mk_repr
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
  (inner: unit -> Write a emp p pre post l)
: Write a frame (frame_out a frame p) (frame_pre a frame pre) (frame_post a frame pre p post) l
= frame' a frame pre p post l inner ()

let elem_writer
  (p: parser)
: Tot Type
= (#l: B.loc) -> (x: dfst p) -> Write unit emp (fun _ -> p) (fun _ -> True) (fun _ _ y -> y == x) l

let append
  (#fr: parser)
  (#p: parser)
  (w: elem_writer p)
  (#l: B.loc)
  (x: dfst p)
: Write unit fr (fun _ -> fr `star` p) (fun _ -> True) (fun w _ (w', x') -> w' == w /\ x' == x) l
= frame unit fr (fun _ -> True) (fun _ -> p) (fun _ _ x' -> x' == x) l (fun _ -> w x)

assume
val parse_u32' : parser' U32.t

let parse_u32 : parser = (| U32.t , parse_u32' |)

assume
val write_u32 : elem_writer parse_u32

let write_two_ints
  (l: B.loc)
  (x y: U32.t)
: Write unit emp (fun _ -> parse_u32 `star` parse_u32) (fun _ -> True) (fun _ _ (x', y') -> x' == x /\ y' == y) l
= write_u32 x;
  append write_u32 y

let write_two_ints_ifthenelse
  (l: B.loc)
  (x y: U32.t)
: Write unit emp (fun _ -> parse_u32 `star` parse_u32) (fun _ -> True) (fun _ _ (x', y') -> x' == x /\ y' == (if U32.v x < U32.v y then x else y)) l
= write_u32 x;
  if x `U32.lt` y
  then
    append write_u32 x
  else
    append write_u32 y
