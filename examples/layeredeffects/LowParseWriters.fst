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

let read_repr_impl
  a pre post post_err l spec
=
  unit ->
  HST.Stack (result a)
  (requires (fun h ->
    B.modifies l.lwrite l.h0 h /\
    pre
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    res == spec ()
  ))

let read_return_impl
  a x inv
= fun _ -> Correct x

let read_bind_impl
  a b pre_f post_f post_err_f pre_g post_g post_err_g f_bind_impl g l f' g'
=
  fun _ ->
  match f' () with
  | Correct x -> g' x ()
  | Error e -> Error e

let read_subcomp_impl
  a pre post post_err pre' post' post_err' l l' f_subcomp_spec f_subcomp sq
=
  fun _ -> f_subcomp ()

let lift_pure_read_impl
  a wp f_pure_spec_for_impl l
=
  fun _ -> Correct (f_pure_spec_for_impl ())

let failwith_impl
  a inv s
= fun _ -> Error s

noeq
type rptr = {
  rptr_base: B.buffer U8.t;
  rptr_len: (rptr_len: U32.t { rptr_len == B.len rptr_base });
}

let valid_rptr
  p inv x
=
  inv.lread `B.loc_includes` B.loc_buffer x.rptr_base /\
  valid_buffer p inv.h0 x.rptr_base

let deref_spec
  #p #inv x
=
  buffer_contents p inv.h0 x.rptr_base

let deref_impl
  #p #inv r x _
=
  let h = HST.get () in
  valid_frame p inv.h0 x.rptr_base 0ul (B.len x.rptr_base) inv.lwrite h;
  Correct (r x.rptr_base x.rptr_len)

let access_spec
  #p1 #p2 #lens #inv g x
=
  let y' = gaccess g inv.h0 x.rptr_base in
  { rptr_base = y'; rptr_len = B.len y' }

let access_impl
  #p1 #p2 #lens #inv #g a x
=
  fun _ ->
  let h = HST.get () in
  valid_frame p1 inv.h0 x.rptr_base 0ul (B.len x.rptr_base) inv.lwrite h;
  let (base', len') = baccess a x.rptr_base x.rptr_len in
  let h' = HST.get () in
  gaccessor_frame g inv.h0 x.rptr_base inv.lwrite h;
  gaccessor_frame g inv.h0 x.rptr_base inv.lwrite h';
  Correct ({ rptr_base = base'; rptr_len = len' })

let validate_spec
  p inv b
= fun _ ->
  match gvalidate p inv.h0 b with
  | None -> Error "validation failed"
  | Some pos ->
    let b' = B.gsub b 0ul pos in
    let x = { rptr_base = b' ; rptr_len = pos } in
    Correct (x, pos)

let valid_frame'
  (p: parser)
  (h: HS.mem)
  (b: B.buffer U8.t)
  (pos: U32.t)
  (l: B.loc)
  (h' : HS.mem)
  (pos' : U32.t)
: Lemma
  ((
    B.live h b /\
    (valid_pos p h b pos pos' \/ valid_pos p h' b pos pos') /\
    B.modifies l h h' /\
    B.loc_disjoint l (B.loc_buffer_from_to b pos pos')
  ) ==> (
    valid_pos p h b pos pos' /\
    valid_pos p h' b pos pos' /\
    contents p h' b pos pos' == contents p h b pos pos'
  ))
= Classical.move_requires (valid_frame p h b pos pos' l) h'

let validate_impl
  #p v inv b len
= fun _ ->
  let h1 = HST.get () in
  Classical.forall_intro (valid_frame' p inv.h0 b 0ul inv.lwrite h1);
  gvalidate_frame p inv.h0 b inv.lwrite h1;
  let res = bvalidate v b len in
  let h2 = HST.get () in
  Classical.forall_intro (valid_frame' p inv.h0 b 0ul inv.lwrite h2);
  gvalidate_frame p inv.h0 b inv.lwrite h2;
  match res with
  | None -> Error "validation failed"
  | Some pos ->
    let b' = B.sub b 0ul pos in
    let x = { rptr_base = b' ; rptr_len = pos } in
    Correct (x, pos)

noeq
type iresult (a: Type u#x) : Type u#x =
| ICorrect: (res: a) -> (pos' : U32.t) -> iresult a
| IError of string
| IOverflow

unfold
let repr_impl_post
  (a:Type u#x)
  (r_in: parser)
  (r_out:a -> parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (post_err: post_err_t r_in pre)
  (l: memory_invariant)
  (spec: repr_spec a r_in r_out pre post post_err)
  (b: B.buffer u8 { l.lwrite `B.loc_includes` B.loc_buffer b })
  (pos1: U32.t { U32.v pos1 <= B.length b })
  (h: HS.mem)
  (res: iresult a)
  (h' : HS.mem)
: GTot Type0
= 
    valid_pos r_in h b 0ul pos1 /\ (
    let v_in = contents r_in h b 0ul pos1 in
    pre v_in /\
    begin match spec v_in, res with
    | Correct (| v, v_out |), ICorrect v' pos2 ->
      U32.v pos1 <= U32.v pos2 /\
      valid_pos (r_out v) h' b 0ul pos2 /\
      v' == v /\
      v_out == contents (r_out v) h' b 0ul pos2 /\
      B.modifies (B.loc_buffer_from_to b 0ul pos2) h h'
    | Correct (| v, v_out |), IOverflow ->
      size (r_out v) v_out > B.length b /\
      B.modifies (B.loc_buffer b) h h'
    | Error s, IError s' ->
      s == s' /\
      B.modifies (B.loc_buffer b) h h'
    | Error _, IOverflow ->
      (* overflow happened in implementation before specification could reach error *)
      B.modifies (B.loc_buffer b) h h'
    | _ -> False
    end
  )

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
  (post_err: post_err_t r_in pre)
  (l: memory_invariant)
  (spec: repr_spec a r_in r_out pre post post_err)
: Tot Type0 =
  (b: B.buffer u8 { l.lwrite `B.loc_includes` B.loc_buffer b }) ->
  (len: U32.t { len == B.len b }) ->
  (pos1: buffer_offset b) ->
  HST.Stack (iresult a)
  (requires (fun h ->
    B.modifies l.lwrite l.h0 h /\
    valid_pos r_in h b 0ul pos1 /\
    pre (contents r_in h b 0ul pos1)
  ))
  (ensures (fun h res h' ->
    repr_impl_post a r_in r_out pre post post_err l spec b pos1 h res h'
  ))

inline_for_extraction
let return_impl
  (a:Type) (x:a) (r: a -> parser)
  (l: memory_invariant)
: Tot (repr_impl a (r x) r (return_pre a x r) (return_post a x r) (return_post_err a x r) l (return_spec a x r))
= fun b len pos1 -> ICorrect x pos1

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
  (post_err_f: post_err_t r_in_f pre_f)
  (r_out_g:b -> parser)
  (pre_g: (x:a) -> pre_t (r_out_f x)) (post_g: (x:a) -> post_t b (r_out_f x) r_out_g (pre_g x))
  (post_err_g: (x:a) -> post_err_t (r_out_f x) (pre_g x))
  (f_bind_impl:repr_spec a r_in_f r_out_f pre_f post_f post_err_f)
  (g:(x:a -> repr_spec b (r_out_f x) r_out_g (pre_g x) (post_g x) (post_err_g x)))
  (l: memory_invariant)
  (f' : repr_impl a r_in_f r_out_f pre_f post_f post_err_f l f_bind_impl)
  (g' : (x: a -> repr_impl b (r_out_f x) r_out_g (pre_g x) (post_g x) (post_err_g x) l (g x)))
: Tot (repr_impl b r_in_f r_out_g (bind_pre a r_in_f r_out_f pre_f post_f pre_g) (bind_post a b r_in_f r_out_f pre_f post_f r_out_g pre_g post_g) (bind_post_err a r_in_f r_out_f pre_f post_f post_err_f pre_g post_err_g) l (bind_spec a b r_in_f r_out_f pre_f post_f post_err_f r_out_g pre_g post_g post_err_g f_bind_impl g))
= fun buf len pos ->
  match f' buf len pos with
  | IError e -> IError e
  | IOverflow -> IOverflow
  | ICorrect x posf -> g' x buf len posf

inline_for_extraction
let subcomp_impl (a:Type)
  (r_in:parser) (r_out:a -> parser)
  (pre: pre_t r_in) (post: post_t a r_in r_out pre) (post_err: post_err_t r_in pre)
  (pre': pre_t r_in) (post': post_t a r_in r_out pre') (post_err': post_err_t r_in pre')
  (l:memory_invariant)
  (l' : memory_invariant)
  (f_subcomp_spec:repr_spec a r_in r_out pre post post_err)
  (f_subcomp:repr_impl a r_in r_out pre post post_err l f_subcomp_spec)
  (sq: squash (subcomp_cond a r_in r_out pre post post_err pre' post' post_err' l l'))
: Tot (repr_impl a r_in r_out pre' post' post_err' l' (subcomp_spec a r_in r_out pre post post_err pre' post' post_err' f_subcomp_spec))
= (fun b len pos -> f_subcomp b len pos)

(*
inline_for_extraction
let lift_pure_impl
  (a:Type) (wp:pure_wp a { pure_wp_mono a wp }) (r:parser) (f_pure_spec_for_impl:unit -> PURE a wp)
  (l: memory_invariant)
: Tot (repr_impl a r (fun _ -> r) (lift_pure_pre a wp r) (lift_pure_post a wp r) l (lift_pure_spec a wp r f_pure_spec_for_impl))
= fun buf len pos -> Some (f_pure_spec_for_impl (), pos)
*)

let lift_read_impl
  a pre post post_err inv r f_read_spec
=
  fun b len pos ->
    let h = HST.get () in
    let rres = dsnd f_read_spec () in
    let h' = HST.get () in
    valid_frame r h b 0ul pos B.loc_none h';
    match rres with
    | Correct res -> ICorrect res pos
    | Error e -> IError e

inline_for_extraction
let frame_impl
  (a: Type)
  (frame: parser)
  (pre: pre_t emp)
  (p: a -> parser)
  (post: post_t a emp p pre)
  (post_err: post_err_t emp pre)
  (l: memory_invariant)
  (inner: unit -> EWrite a emp p pre post post_err l)
: Tot (repr_impl a frame (frame_out a frame p) (frame_pre frame pre) (frame_post a frame pre p post) (frame_post_err frame pre post_err) l (frame_spec a frame pre p post post_err l inner))
= fun buf len pos ->
  let h = HST.get () in
  let buf' = B.offset buf pos in
  match destr_repr_impl a emp p pre post post_err l inner buf' (len `U32.sub` pos) 0ul with
  | IError e -> IError e
  | IOverflow -> IOverflow
  | ICorrect x wlen ->
    let h' = HST.get () in
    let pos' = pos `U32.add` wlen in
    B.loc_disjoint_loc_buffer_from_to buf 0ul pos pos wlen;
    valid_frame frame h buf 0ul pos (B.loc_buffer_from_to buf' 0ul wlen) h';
    valid_star frame (p x) h' buf 0ul pos pos' ;
    ICorrect x pos'

#push-options "--z3rlimit 128"

let elem_writer_impl
  #p w l x
=
  fun b len pos ->
  let b' = B.offset b pos in
  match w b' (len `U32.sub` pos) x with
  | None -> IOverflow
  | Some xlen -> ICorrect () (pos `U32.add` xlen)

inline_for_extraction
let recast_writer_impl
  (a:Type u#x)
  (r_in: parser)
  (r_out:a -> parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (post_err: post_err_t r_in pre)
  (l: memory_invariant)
  (f: unit -> EWrite a r_in r_out pre post post_err l)
: Tot (repr_impl a r_in r_out pre (recast_writer_post a r_in r_out pre post post_err l f) (recast_writer_post_err a r_in r_out pre post post_err l f) l (recast_writer_spec a r_in r_out pre post post_err l f))
= fun b len pos -> destr_repr_impl a r_in r_out pre post post_err l f b len pos

#restart-solver

inline_for_extraction
let frame2_impl
  a frame ppre pre p post post_err l inner
= fun buf len pos ->
  let h = HST.get () in
  let pos2 = valid_star_inv frame ppre buf len 0ul pos in
  let buf' = B.offset buf pos2 in
  assert (valid_pos ppre h buf pos2 pos);
  assert (valid_pos ppre h buf' 0ul (pos `U32.sub` pos2));
  let h1 = HST.get () in
  valid_frame ppre h buf' 0ul (pos `U32.sub` pos2) B.loc_none h1;
  match destr_repr_impl a ppre p pre post post_err l inner buf' (len `U32.sub` pos2) (pos `U32.sub` pos2) with
  | IOverflow -> IOverflow
  | IError e -> IError e
  | ICorrect x wlen ->
    let h' = HST.get () in
    let pos' = pos2 `U32.add` wlen in
    B.loc_disjoint_loc_buffer_from_to buf 0ul pos2 pos2 wlen;
    valid_frame frame h buf 0ul pos2 (B.loc_buffer_from_to buf' 0ul wlen) h';
    valid_star frame (p x) h' buf 0ul pos2 pos' ;
    ICorrect x pos'

#pop-options
