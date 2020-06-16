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

let parser' = admit ()

let valid_pos = admit ()

let valid_pos_post = admit ()

let contents = admit ()

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
let return_impl
  (a:Type) (x:a) (r: a -> parser)
  (l: B.loc)
: Tot (repr_impl a (r x) r (return_pre a x r) (return_post a x r) l (return_spec a x r))
= fun b pos1 -> (x, pos1)

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
let subcomp_impl (a:Type)
  (r_in:parser) (r_out:a -> parser)
  (pre: pre_t r_in) (post: post_t a r_in r_out pre)
  (pre': pre_t r_in) (post': post_t a r_in r_out pre')
  (l:B.loc)
  (l' : B.loc)
  (f_subcomp_spec:repr_spec a r_in r_out pre post)
  (f_subcomp:repr_impl a r_in r_out pre post l f_subcomp_spec)
  (sq: squash (subcomp_cond a r_in r_out pre post pre' post' l l'))
: Tot (repr_impl a r_in r_out pre' post' l' (subcomp_spec a r_in r_out pre post pre' post' f_subcomp_spec))
= (fun b pos -> f_subcomp b pos)

inline_for_extraction
let lift_pure_impl
  (a:Type) (wp:pure_wp a { pure_wp_mono a wp }) (r:parser) (f_pure_spec_for_impl:unit -> PURE a wp)
  (l: B.loc)
: Tot (repr_impl a r (fun _ -> r) (lift_pure_pre a wp r) (lift_pure_post a wp r) l (lift_pure_spec a wp r f_pure_spec_for_impl))
= fun buf pos -> (f_pure_spec_for_impl (), pos)

let emp' = admit ()

let valid_emp = admit ()

let star' = admit ()

let valid_star = admit ()

let valid_frame = admit ()

let valid_gsub = admit ()

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

let parse_u32' = admit ()

let write_u32 = admit ()

inline_for_extraction
let recast_writer_impl
  (a:Type u#x)
  (r_in: parser)
  (r_out:a -> parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (l: B.loc)
  (f: unit -> Write a r_in r_out pre post l)
: Tot (repr_impl a r_in r_out pre (recast_writer_post a r_in r_out pre post l f) l (recast_writer_spec a r_in r_out pre post l f))
= fun b pos -> destr_repr_impl a r_in r_out pre post l f b pos
