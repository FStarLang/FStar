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
  lwrite: (lwrite: Ghost.erased B.loc);
}

unfold
let memory_invariant_includes (ol ne: memory_invariant) =
  B.modifies ol.lwrite ol.h0 ne.h0 /\
  ol.lwrite `B.loc_includes` ne.lwrite

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

noeq
type result (a: Type u#x) : Type u#x =
| Correct of a
| Error of string

let pure_post_err
  (pre: pure_pre)
: Tot Type
= unit (* squash pre *) -> GTot Type0

let pure_post'
  (a: Type)
  (pre: pure_pre)
: Tot Type
= (x: a) -> GTot Type0 // (requires pre) (ensures (fun _ -> True))

inline_for_extraction
let read_repr_spec (a:Type u#x) (pre: pure_pre) (post: pure_post' a pre) (post_err: pure_post_err pre)  : Tot (Type u#x) =
  unit ->
  Ghost (result a)
  (requires pre)
  (ensures (fun res ->
    match res with
    | Correct v -> post v
    | Error _ -> post_err ()
  ))

inline_for_extraction
val read_repr_impl
  (a:Type u#x)
  (pre: pure_pre)
  (post: pure_post' a pre)
  (post_err: pure_post_err pre)
  (l: memory_invariant)
  (spec: read_repr_spec a pre post post_err)
: Tot Type0

inline_for_extraction
val mk_read_repr_impl
  (a:Type u#x)
  (pre: pure_pre)
  (post: pure_post' a pre)
  (post_err: pure_post_err pre)
  (l: memory_invariant)
  (spec: read_repr_spec a pre post post_err)
  (impl: (
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
  ))
: Tot (read_repr_impl a pre post post_err l spec)

let read_repr
  (a:Type u#x)
  (pre: pure_pre)
  (post: pure_post' a pre)
  (post_err: pure_post_err pre)
  (l: memory_invariant)
= dtuple2 _ (read_repr_impl a pre post post_err l)

let read_return_spec
  (a:Type) (x:a)
: Tot (read_repr_spec a True (fun res -> res == x) (fun _ -> False))
= fun _ -> Correct x

inline_for_extraction
val read_return_impl
  (a:Type) (x:a) (inv: memory_invariant)
: Tot (read_repr_impl a True (fun res -> res == x) (fun _ -> False) inv (read_return_spec a x))

inline_for_extraction
let read_return
  (a:Type) (x:a) (inv: memory_invariant)
: Tot (read_repr a True (fun res -> res == x) (fun _ -> False) inv)
= (| read_return_spec a x, read_return_impl a x inv |)

// let read_bind_pre
//   (a:Type)
//   (pre_f: pure_pre) (post_f: pure_post' a pre_f)
//   (pre_g: (x:a) -> pure_pre)
// : Tot pure_pre
// = pre_f /\ (forall (x: a) . post_f x ==> pre_g x)

// let read_bind_post
//   (a:Type) (b:Type)
//   (pre_f: pure_pre) (post_f: pure_post' a pre_f)
//   (pre_g: (x:a) -> pure_pre) (post_g: (x:a) -> pure_post' b (pre_g x))
// : Tot (pure_post' b (read_bind_pre a pre_f post_f pre_g))
// = fun y ->
//   exists x . pre_f /\ post_f x /\ post_g x y

// let read_bind_post_err
//   (a:Type)
//   (pre_f: pure_pre) (post_f: pure_post' a pre_f)
//   (post_err_f: pure_post_err pre_f)
//   (pre_g: (x:a) -> pure_pre)
//   (post_err_g: (x: a) -> pure_post_err (pre_g x))
// : Tot (pure_post_err (read_bind_pre a pre_f post_f pre_g))
// = fun _ ->
//   pre_f /\ (post_err_f () \/ (exists x . post_f x /\ post_err_g x ()))

let read_bind_spec
  (a:Type) (b:Type)
  (pre_f: pure_pre) (post_f: pure_post' a pre_f)
  (post_err_f: pure_post_err pre_f)
  (pre_g: (x:a) -> pure_pre) (post_g: (x:a) -> pure_post' b (pre_g x))
  (post_err_g: (x: a) -> pure_post_err (pre_g x))
  (f_bind_spec: read_repr_spec a pre_f post_f post_err_f)
  (g:(x:a -> read_repr_spec b (pre_g x) (post_g x) (post_err_g x)))
: Tot (read_repr_spec b
    (pre_f /\ (forall (x: a) . post_f x ==> pre_g x)) //(read_bind_pre a pre_f post_f pre_g)
    (fun y -> exists (x: a) . pre_f /\ post_f x /\ post_g x y) // (read_bind_post a b pre_f post_f pre_g post_g)
    (fun _ -> pre_f /\ (post_err_f () \/ (exists (x: a) . post_f x /\ post_err_g x ()))) // (read_bind_post_err a pre_f post_f post_err_f pre_g post_err_g)
  )
= fun _ ->
  match f_bind_spec () with
  | Correct a -> g a ()
  | Error e -> Error e

inline_for_extraction
val read_bind_impl
  (a:Type) (b:Type)
  (pre_f: pure_pre) (post_f: pure_post' a pre_f)
  (post_err_f: pure_post_err pre_f)
  (pre_g: (x:a) -> pure_pre) (post_g: (x:a) -> pure_post' b (pre_g x))
  (post_err_g: (x: a) -> pure_post_err (pre_g x))
  (f_bind_impl: read_repr_spec a pre_f post_f post_err_f)
  (g:(x:a -> read_repr_spec b (pre_g x) (post_g x) (post_err_g x)))
  (l: memory_invariant)
  (f' : read_repr_impl a pre_f post_f post_err_f l f_bind_impl)
  (g' : (x: a -> read_repr_impl b (pre_g x) (post_g x) (post_err_g x) l (g x)))
: Tot (read_repr_impl b _ _ _ l (read_bind_spec a b pre_f post_f post_err_f pre_g post_g post_err_g f_bind_impl g))

inline_for_extraction
let read_bind
  (a:Type) (b:Type)
  (pre_f: pure_pre)
  (post_f: pure_post' a pre_f)
  (post_err_f: pure_post_err pre_f)
  (pre_g: (x:a) -> pure_pre) (post_g: (x:a) -> pure_post' b (pre_g x))
  (post_err_g: (x: a) -> pure_post_err (pre_g x))
  (l: memory_invariant)
  (f_bind : read_repr a pre_f post_f post_err_f l)
  (g : (x: a -> read_repr b (pre_g x) (post_g x) (post_err_g x) l))
: Tot (read_repr b
    (pre_f /\ (forall (x: a) . post_f x ==> pre_g x)) //(read_bind_pre a pre_f post_f pre_g)
    (fun y -> exists (x: a) . pre_f /\ post_f x /\ post_g x y) // (read_bind_post a b pre_f post_f pre_g post_g)
    (fun _ -> pre_f /\ (post_err_f () \/ (exists (x: a) . post_f x /\ post_err_g x ()))) // (read_bind_post_err a pre_f post_f post_err_f pre_g post_err_g)
    l
  )
= (| _, read_bind_impl a b pre_f post_f post_err_f pre_g post_g post_err_g (dfst f_bind) (fun x -> dfst (g x)) l (dsnd f_bind) (fun x -> dsnd (g x)) |)

unfold
let read_subcomp_spec_cond
  (a:Type)
  (pre: pure_pre) (post: pure_post' a pre) (post_err: pure_post_err pre)
  (pre': pure_pre) (post': pure_post' a pre') (post_err': pure_post_err pre')
: GTot Type0
= (pre' ==> pre) /\
  (forall x . (pre' /\ post x) ==> post' x) /\
  ((pre' /\ post_err ()) ==> post_err' ())

unfold
let read_subcomp_cond
  (a:Type)
  (pre: pure_pre) (post: pure_post' a pre) (post_err: pure_post_err pre)
  (pre': pure_pre) (post': pure_post' a pre') (post_err': pure_post_err pre')
  (l: memory_invariant)
  (l' : memory_invariant)
: GTot Type0
= l `memory_invariant_includes` l' /\
  read_subcomp_spec_cond a pre post post_err pre' post' post_err'

let read_subcomp_spec (a:Type)
  (pre: pure_pre) (post: pure_post' a pre) (post_err: pure_post_err pre)
  (pre': pure_pre) (post': pure_post' a pre') (post_err': pure_post_err pre')
  (f_subcomp:read_repr_spec a pre post post_err)
: Pure (read_repr_spec a pre' post' post_err')
  (requires (read_subcomp_spec_cond a pre post post_err pre' post' post_err'))
  (ensures (fun _ -> True))
= (fun x -> f_subcomp x)

inline_for_extraction
val read_subcomp_impl (a:Type)
  (pre: pure_pre) (post: pure_post' a pre) (post_err: pure_post_err pre)
  (pre': pure_pre) (post': pure_post' a pre') (post_err': pure_post_err pre')
  (l:memory_invariant)
  (l' : memory_invariant)
  (f_subcomp_spec:read_repr_spec a pre post post_err)
  (f_subcomp:read_repr_impl a pre post post_err l f_subcomp_spec)
  (sq: squash (read_subcomp_cond a pre post post_err pre' post' post_err' l l'))
: Tot (read_repr_impl a pre' post' post_err' l' (read_subcomp_spec a pre post post_err pre' post' post_err' f_subcomp_spec))

inline_for_extraction
let read_subcomp (a:Type)
  (pre: pure_pre) (post: pure_post' a pre) (post_err: pure_post_err pre)
  (pre': pure_pre) (post': pure_post' a pre') (post_err': pure_post_err pre')
  (l:memory_invariant)
  (l' : memory_invariant)
  (f_subcomp:read_repr a pre post post_err l)
: Pure (read_repr a pre' post' post_err' l')
  (requires (read_subcomp_cond a pre post post_err pre' post' post_err' l l'))
  (ensures (fun _ -> True))
= (| read_subcomp_spec a pre post post_err pre' post' post_err' (dfst f_subcomp),
     read_subcomp_impl a pre post post_err pre' post' post_err' l l' (dfst f_subcomp) (dsnd f_subcomp) ()
  |)

let read_if_then_else (a:Type)
  (pre_f pre_g: pure_pre)
  (post_f: pure_post' a pre_f)
  (post_g: pure_post' a pre_g)
  (post_err_f: pure_post_err pre_f)
  (post_err_g: pure_post_err pre_g)
  (l:memory_invariant)
  (f_ifthenelse:read_repr a pre_f post_f post_err_f l)
  (g:read_repr a pre_g post_g post_err_g l)
  (p:Type0)
: Tot Type
= read_repr a
    ((p ==> pre_f) /\ ((~ p) ==> pre_g)) // (read_if_then_else_pre pre_f pre_g p)
    (fun x -> (p ==> post_f x) /\ ((~ p) ==> post_g x)) // (read_if_then_else_post a pre_f pre_g post_f post_g p)
    (fun _ -> (p ==> post_err_f ()) /\ ((~ p) ==> post_err_g ())) // (read_if_then_else_post_err pre_f pre_g post_err_f post_err_g p)
    l

[@@smt_reifiable_layered_effect]
reifiable reflectable total
layered_effect {
  ERead : a:Type -> (pre: pure_pre) -> (post: pure_post' a pre) -> (post_err: pure_post_err pre) -> (memory_invariant) -> Effect
  with
  repr = read_repr;
  return = read_return;
  bind = read_bind;
  subcomp = read_subcomp;
  if_then_else = read_if_then_else
}

effect Read
  (a:Type)
  (pre: pure_pre)
  (post: pure_post' a pre)
  (inv: memory_invariant)
= ERead a pre post (fun _ -> False) inv

let lift_pure_read_spec
  (a:Type) (wp:pure_wp a { pure_wp_mono a wp }) (f_pure_spec:unit -> PURE a wp)
: Tot (read_repr_spec a 
    (wp (fun _ -> True)) // (lift_pure_read_pre a wp)
    (fun x -> ~ (wp (fun x' -> ~ (x == x')))) // (lift_pure_read_post a wp)
    (fun _ -> False) // (lift_pure_read_post_err a wp))
  )
= fun () -> Correct (f_pure_spec ())

inline_for_extraction
val lift_pure_read_impl
  (a:Type) (wp:pure_wp a { pure_wp_mono a wp })
  (f_pure_spec_for_impl:unit -> PURE a wp)
  (l: memory_invariant)
: Tot (read_repr_impl a _ _ _ l (lift_pure_read_spec a wp f_pure_spec_for_impl))

inline_for_extraction
let lift_pure_read (a:Type) (wp:pure_wp a { pure_wp_mono a wp })
  (l: memory_invariant)
  (f_pure:unit -> PURE a wp)
: Tot (read_repr a
    (wp (fun _ -> True)) // (lift_pure_read_pre a wp)
    (fun x -> ~ (wp (fun x' -> ~ (x == x')))) // (lift_pure_read_post a wp)
    (fun _ -> False) // (lift_pure_read_post_err a wp))
    l
  )
= (| lift_pure_read_spec a wp f_pure, lift_pure_read_impl a wp f_pure l |)

sub_effect PURE ~> ERead = lift_pure_read

let test_read_if
  (inv: memory_invariant)
  (f: unit -> Read bool (True) (fun _ -> True) inv)
: Read bool (True) (fun _ -> True) inv
= if f ()
  then false
  else false

let test_read1
  (inv: memory_invariant)
  (f: unit -> Read bool (True) (fun _ -> True) inv)
: Read bool (True) (fun _ -> True) inv
= let x = f () in
  false

let test_read2
  (inv: memory_invariant)
  (f: unit -> Read bool (True) (fun _ -> True) inv)
: Read bool (True) (fun _ -> True) inv
= let x = f () in
  let x = f () in
  false

let test_read3
  (inv: memory_invariant)
  (f: unit -> Read bool (True) (fun _ -> True) inv)
: Read bool (True) (fun _ -> True) inv
= let x = f () in
  let x = f () in
  let x = f () in
  false

let failwith_spec
  (a: Type)
  (s: string)
: Tot (read_repr_spec a True (fun _ -> False) (fun _ -> True))
= fun _ -> Error s

inline_for_extraction
val failwith_impl
  (a: Type)
  (inv: memory_invariant)
  (s: string)
: Tot (read_repr_impl a True (fun _ -> False) (fun _ -> True) inv (failwith_spec a s))

inline_for_extraction
let failwith_repr
  (a: Type)
  (inv: memory_invariant)
  (s: string)
: Tot (read_repr a True (fun _ -> False) (fun _ -> True) inv)
= (| _, failwith_impl a inv s |)

inline_for_extraction
let failwith
  (#a: Type)
  (#inv: memory_invariant)
  (s: string)
: ERead a True (fun _ -> False) (fun _ -> True) inv
= ERead?.reflect (failwith_repr a inv s)

inline_for_extraction
val rptr: Type0
val valid_rptr (p: parser) : memory_invariant -> rptr -> GTot Type0

let ptr (p: parser) (inv: memory_invariant) =
  (x: rptr { valid_rptr p inv x })

val deref_spec (#p: parser) (#inv: memory_invariant) (x: ptr p inv) : GTot (dfst p)

inline_for_extraction
val mk_ptr
  (p: parser)
  (inv: memory_invariant)
  (b: B.buffer u8)
  (len: U32.t { len == B.len b })
: Pure (ptr p inv)
  (requires (valid_buffer p inv.h0 b /\ inv.lwrite `B.loc_disjoint` B.loc_buffer b))
  (ensures (fun res -> deref_spec res == buffer_contents p inv.h0 b))

inline_for_extraction
val buffer_of_ptr
  (#p: parser)
  (#inv: memory_invariant)
  (x: ptr p inv)
: Tot (bl: (B.buffer u8 & U32.t) {
    let (b, len) = bl in
    B.len b == len /\
    valid_buffer p inv.h0 b /\
    inv.lwrite `B.loc_disjoint` B.loc_buffer b /\
    deref_spec x == buffer_contents p inv.h0 b
  })

val valid_rptr_frame
  (#p: parser) (#inv: memory_invariant) (x: ptr p inv) (inv' : memory_invariant)
: Lemma
  (requires (
    inv `memory_invariant_includes` inv'
  ))
  (ensures (
    valid_rptr p inv' x /\
    deref_spec #p #inv' x == deref_spec #p #inv x
  ))
  [SMTPatOr [
    [SMTPat (inv `memory_invariant_includes` inv'); SMTPat (valid_rptr p inv x)];
    [SMTPat (inv `memory_invariant_includes` inv'); SMTPat (valid_rptr p inv' x)];
  ]]

inline_for_extraction
val deref_impl
  (#p: parser)
  (#inv: memory_invariant)
  (r: leaf_reader p)
  (x: ptr p inv)
: Tot (read_repr_impl (dfst p) True (fun res -> res == deref_spec x) (fun _ -> False) inv (fun _ -> Correct (deref_spec x)))

inline_for_extraction
let deref_repr
  (#p: parser)
  (#inv: memory_invariant)
  (r: leaf_reader p)
  (x: ptr p inv)
: Tot (read_repr (dfst p) True (fun res -> res == deref_spec x) (fun _ -> False) inv)
= (| (fun _ -> Correct (deref_spec x)), deref_impl r x |)

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
: Tot (read_repr_impl (ptr p2 inv) (lens.clens_cond (deref_spec x)) (fun res -> lens.clens_cond (deref_spec x) /\ deref_spec res == lens.clens_get (deref_spec x)) (fun _ -> False) inv (fun _ -> Correct (access_spec g x)))

inline_for_extraction
let access_repr
  (#p1 #p2: parser)
  (#lens: clens (dfst p1) (dfst p2))
  (#inv: memory_invariant)
  (#g: gaccessor p1 p2 lens)
  (a: accessor g)
  (x: ptr p1 inv)
: Tot (read_repr (ptr p2 inv) (lens.clens_cond (deref_spec x)) (fun res -> lens.clens_cond (deref_spec x) /\ deref_spec res == lens.clens_get (deref_spec x)) (fun _ -> False) inv)
= (| (fun _ -> Correct (access_spec g x)), access_impl a x |)

inline_for_extraction
let access
  (#p1 #p2: parser)
  (#lens: clens (dfst p1) (dfst p2))
  (#inv: memory_invariant)
  (#g: gaccessor p1 p2 lens)
  (a: accessor g)
  (x: ptr p1 inv)
: Read (ptr p2 inv) (lens.clens_cond (deref_spec x)) (fun res -> lens.clens_cond (deref_spec x) /\ deref_spec res == lens.clens_get (deref_spec x)) inv
= Read?.reflect (access_repr a x)

// unfold
let validate_pre
  (inv: memory_invariant)
  (b: B.buffer U8.t)
: Tot pure_pre
=
  inv.lwrite `B.loc_disjoint` B.loc_buffer b /\
  B.live inv.h0 b

// unfold
let validate_post
  (p: parser)
  (inv: memory_invariant)
  (b: B.buffer U8.t)
: Tot (pure_post' (ptr p inv & U32.t) (validate_pre inv b))
= fun (x, pos) ->
    valid_pos p inv.h0 b 0ul pos /\
    deref_spec x == contents p inv.h0 b 0ul pos

// unfold
let validate_post_err
  (p: parser)
  (inv: memory_invariant)
  (b: B.buffer U8.t)
: Tot (pure_post_err (validate_pre inv b))
= fun _ -> forall pos . ~ (valid_pos p inv.h0 b 0ul pos)

val validate_spec
  (p: parser)
  (inv: memory_invariant)
  (b: B.buffer U8.t)
: Tot (read_repr_spec (ptr p inv & U32.t) (validate_pre inv b) (validate_post p inv b) (validate_post_err p inv b))

inline_for_extraction
val validate_impl
  (#p: parser)
  (v: validator p)
  (inv: memory_invariant)
  (b: B.buffer U8.t)
  (len: U32.t { B.len b == len })
: Tot (read_repr_impl _ _ _ _ inv (validate_spec p inv b))

inline_for_extraction
let validate_repr
  (#p: parser)
  (v: validator p)
  (inv: memory_invariant)
  (b: B.buffer U8.t)
  (len: U32.t { B.len b == len })
: Tot (read_repr (ptr p inv & U32.t) (validate_pre inv b) (validate_post p inv b) (validate_post_err p inv b) inv)
= (| _, validate_impl v inv b len |)

inline_for_extraction
let validate
  (#p: parser)
  (v: validator p)
  (inv: memory_invariant)
  (b: B.buffer U8.t)
  (len: U32.t { B.len b == len })
: ERead (ptr p inv & U32.t) (validate_pre inv b) (validate_post p inv b) (validate_post_err p inv b) inv
= ERead?.reflect (validate_repr v inv b len)


let pre_t
  (rin: parser)
: Tot Type
= dfst rin -> GTot Type0

let post_t
  (a: Type)
  (rin: parser)
  (rout: parser)
  (pre: pre_t rin)
: Tot Type
= (x: dfst rin (* { pre x } *) ) -> (res: a) -> dfst rout -> GTot Type0

let post_err_t
  (rin: parser)
  (pre: pre_t rin)
: Tot Type
= (x: dfst rin (* { pre x } *) ) -> GTot Type0

inline_for_extraction
let repr_spec (a:Type u#x) (r_in: parser) (r_out: parser) (pre: pre_t r_in) (post: post_t a r_in r_out pre) (post_err: post_err_t r_in pre) : Tot (Type u#x) =
  (v_in: dfst r_in) ->
  Ghost (result (a & dfst r_out))
  (requires (pre v_in))
  (ensures (fun res ->
    match res with
    | Correct (v, v_out) -> post v_in v v_out /\ size r_in v_in <= size r_out v_out
    | Error _ -> post_err v_in
  ))

noeq
type iresult (a: Type u#x) : Type u#x =
| ICorrect: (res: a) -> (pos' : U32.t) -> iresult a
| IError of string
| IOverflow

unfold
let repr_impl_post
  (a:Type u#x)
  (r_in: parser)
  (r_out: parser)
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
    valid_pos r_in h b 0ul pos1 /\
    B.modifies (B.loc_buffer b) h h' /\ (
    let v_in = contents r_in h b 0ul pos1 in
    pre v_in /\
    begin match spec v_in, res with
    | Correct (v, v_out), ICorrect v' pos2 ->
      U32.v pos1 <= U32.v pos2 /\
      valid_pos (r_out) h' b 0ul pos2 /\
      v' == v /\
      v_out == contents (r_out) h' b 0ul pos2
    | Correct (v, v_out), IOverflow ->
      size (r_out) v_out > B.length b
    | Error s, IError s' ->
      s == s'
    | Error _, IOverflow ->
      (* overflow happened in implementation before specification could reach error *)
      True
    | _ -> False
    end
  )

let buffer_offset
  (#t: Type)
  (b: B.buffer t)
: Tot Type0
= pos1: U32.t { U32.v pos1 <= B.length b }

inline_for_extraction
val repr_impl
  (a:Type u#x)
  (r_in: parser)
  (r_out: parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (post_err: post_err_t r_in pre)
  (l: memory_invariant)
  (spec: repr_spec a r_in r_out pre post post_err)
: Tot Type0

inline_for_extraction
val mk_repr_impl
  (a:Type u#x)
  (r_in: parser)
  (r_out: parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (post_err: post_err_t r_in pre)
  (l: memory_invariant)
  (spec: repr_spec a r_in r_out pre post post_err)
  (impl: (
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
  ))
: Tot (repr_impl a r_in r_out pre post post_err l spec)

inline_for_extraction
let repr
  (a: Type u#x)
  (r_in: parser) (r_out: parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (post_err: post_err_t r_in pre)
  (l: memory_invariant)
: Tot (Type u#x)
= dtuple2 (repr_spec a r_in r_out pre post post_err) (repr_impl a r_in r_out pre post post_err l)

let return_spec
  (a:Type) (x:a) (r: parser)
: Tot (repr_spec a r r (fun _ -> True) (fun v_in x' v_out -> x' == x /\ v_out == v_in) (fun _ -> False))
= fun c -> Correct (x, c)

inline_for_extraction
val return_impl
  (a:Type) (x:a) (r: parser)
  (l: memory_invariant)
: Tot (repr_impl a (r) r _ _ _ l (return_spec a x r))

inline_for_extraction
let returnc
  (a:Type) (x:a) (r: parser) (l: memory_invariant)
: Tot (repr a (r) r (fun _ -> True) (fun v_in x' v_out -> x' == x /\ v_out == v_in) (fun _ -> False) l)
= (| return_spec a x r, return_impl a x r l |)

let bind_spec (a:Type) (b:Type)
  (r_in_f:parser) (r_out_f: parser)
  (pre_f: pre_t r_in_f) (post_f: post_t a r_in_f r_out_f pre_f)
  (post_err_f: post_err_t r_in_f pre_f)
  (r_out_g: parser)
  (pre_g: (x:a) -> pre_t (r_out_f)) (post_g: (x:a) -> post_t b (r_out_f) r_out_g (pre_g x))
  (post_err_g: (x:a) -> post_err_t (r_out_f) (pre_g x))
  (f_bind_spec:repr_spec a r_in_f r_out_f pre_f post_f post_err_f)
  (g:(x:a -> repr_spec b (r_out_f) r_out_g (pre_g x) (post_g x) (post_err_g x)))
: Tot (repr_spec b r_in_f r_out_g
    (fun v_in -> pre_f v_in /\ (forall (x: a) v_out . post_f v_in x v_out ==> pre_g x v_out)) // (bind_pre a r_in_f r_out_f pre_f post_f pre_g)
    (fun v_in y v_out -> exists x v_out_f . pre_f v_in /\ post_f v_in x v_out_f /\ post_g x v_out_f y v_out) // (bind_post a b r_in_f r_out_f pre_f post_f r_out_g pre_g post_g)
    (fun v_in -> 
      pre_f v_in /\ (
        post_err_f v_in \/ (
        exists x v_out_f . post_f v_in x v_out_f /\ post_err_g x v_out_f
    ))) // (bind_post_err a r_in_f r_out_f pre_f post_f post_err_f pre_g post_err_g))
  )
= fun c ->
  match f_bind_spec c with
  | Correct (x, cf) ->
    g x cf
  | Error e -> Error e

inline_for_extraction
val bind_impl
  (a:Type) (b:Type)
  (r_in_f:parser) (r_out_f: parser)
  (pre_f: pre_t r_in_f) (post_f: post_t a r_in_f r_out_f pre_f)
  (post_err_f: post_err_t r_in_f pre_f)
  (r_out_g: parser)
  (pre_g: (x:a) -> pre_t (r_out_f)) (post_g: (x:a) -> post_t b (r_out_f) r_out_g (pre_g x))
  (post_err_g: (x:a) -> post_err_t (r_out_f) (pre_g x))
  (f_bind_impl:repr_spec a r_in_f r_out_f pre_f post_f post_err_f)
  (g:(x:a -> repr_spec b (r_out_f) r_out_g (pre_g x) (post_g x) (post_err_g x)))
  (l: memory_invariant)
  (f' : repr_impl a r_in_f r_out_f pre_f post_f post_err_f l f_bind_impl)
  (g' : (x: a -> repr_impl b (r_out_f) r_out_g (pre_g x) (post_g x) (post_err_g x) l (g x)))
: Tot (repr_impl b r_in_f r_out_g _ _ _ l (bind_spec a b r_in_f r_out_f pre_f post_f post_err_f r_out_g pre_g post_g post_err_g f_bind_impl g))

inline_for_extraction
let bind (a:Type) (b:Type)
  (r_in_f:parser) (r_out_f: parser)
  (pre_f: pre_t r_in_f) (post_f: post_t a r_in_f r_out_f pre_f)
  (post_err_f: post_err_t r_in_f pre_f)
  (r_out_g: parser)
  (pre_g: (x:a) -> pre_t (r_out_f)) (post_g: (x:a) -> post_t b (r_out_f) r_out_g (pre_g x))
  (post_err_g: (x:a) -> post_err_t (r_out_f) (pre_g x))
  (l: memory_invariant)
  (f_bind : repr a r_in_f r_out_f pre_f post_f post_err_f l)
  (g : (x: a -> repr b (r_out_f) r_out_g (pre_g x) (post_g x) (post_err_g x) l))
: Tot (repr b r_in_f r_out_g
    (fun v_in -> pre_f v_in /\ (forall (x: a) v_out . post_f v_in x v_out ==> pre_g x v_out)) // (bind_pre a r_in_f r_out_f pre_f post_f pre_g)
    (fun v_in y v_out -> exists x v_out_f . pre_f v_in /\ post_f v_in x v_out_f /\ post_g x v_out_f y v_out) // (bind_post a b r_in_f r_out_f pre_f post_f r_out_g pre_g post_g)
    (fun v_in -> 
      pre_f v_in /\ (
        post_err_f v_in \/ (
        exists x v_out_f . post_f v_in x v_out_f /\ post_err_g x v_out_f
    ))) // (bind_post_err a r_in_f r_out_f pre_f post_f post_err_f pre_g post_err_g))
    l
  )
= (| bind_spec a b r_in_f r_out_f pre_f post_f post_err_f r_out_g pre_g post_g post_err_g (dfst f_bind) (fun x -> dfst (g x)), bind_impl a b r_in_f r_out_f pre_f post_f post_err_f r_out_g pre_g post_g post_err_g (dfst f_bind) (fun x -> dfst (g x)) l (dsnd f_bind) (fun x -> dsnd (g x)) |)

unfold
let subcomp_spec_cond
  (a:Type)
  (r_in:parser) (r_out: parser)
  (pre: pre_t r_in) (post: post_t a r_in r_out pre) (post_err: post_err_t r_in pre)
  (pre': pre_t r_in) (post': post_t a r_in r_out pre') (post_err': post_err_t r_in pre')
: GTot Type0
= (forall v_in . pre' v_in ==> pre v_in) /\
  (forall v_in x v_out . (pre' v_in /\ post v_in x v_out) ==> post' v_in x v_out) /\
  (forall v_in . (pre' v_in /\ post_err v_in) ==> post_err' v_in)

unfold
let subcomp_cond
  (a:Type)
  (r_in:parser) (r_out: parser)
  (pre: pre_t r_in) (post: post_t a r_in r_out pre) (post_err: post_err_t r_in pre)
  (pre': pre_t r_in) (post': post_t a r_in r_out pre') (post_err': post_err_t r_in pre')
  (l: memory_invariant)
  (l' : memory_invariant)
: GTot Type0
= l `memory_invariant_includes` l' /\
  subcomp_spec_cond a r_in r_out pre post post_err pre' post' post_err'

let subcomp_spec (a:Type)
  (r_in:parser) (r_out: parser)
  (pre: pre_t r_in) (post: post_t a r_in r_out pre) (post_err: post_err_t r_in pre)
  (pre': pre_t r_in) (post': post_t a r_in r_out pre') (post_err': post_err_t r_in pre')
  (f_subcomp:repr_spec a r_in r_out pre post post_err)
: Pure (repr_spec a r_in r_out pre' post' post_err')
  (requires (subcomp_spec_cond a r_in r_out pre post post_err pre' post' post_err'))
  (ensures (fun _ -> True))
= (fun x -> f_subcomp x)

inline_for_extraction
val subcomp_impl (a:Type)
  (r_in:parser) (r_out: parser)
  (pre: pre_t r_in) (post: post_t a r_in r_out pre) (post_err: post_err_t r_in pre)
  (pre': pre_t r_in) (post': post_t a r_in r_out pre') (post_err': post_err_t r_in pre')
  (l:memory_invariant)
  (l' : memory_invariant)
  (f_subcomp_spec:repr_spec a r_in r_out pre post post_err)
  (f_subcomp:repr_impl a r_in r_out pre post post_err l f_subcomp_spec)
  (sq: squash (subcomp_cond a r_in r_out pre post post_err pre' post' post_err' l l'))
: Tot (repr_impl a r_in r_out pre' post' post_err' l' (subcomp_spec a r_in r_out pre post post_err pre' post' post_err' f_subcomp_spec))

inline_for_extraction
let subcomp (a:Type)
  (r_in:parser) (r_out: parser)
  (pre: pre_t r_in) (post: post_t a r_in r_out pre) (post_err: post_err_t r_in pre)
  (pre': pre_t r_in) (post': post_t a r_in r_out pre') (post_err': post_err_t r_in pre')
  (l:memory_invariant)
  (l' : memory_invariant)
  (f_subcomp:repr a r_in r_out pre post post_err l)
: Pure (repr a r_in r_out pre' post' post_err' l')
  (requires (subcomp_cond a r_in r_out pre post post_err pre' post' post_err' l l'))
  (ensures (fun _ -> True))
= (| subcomp_spec a r_in r_out pre post post_err pre' post' post_err' (dfst f_subcomp),
     subcomp_impl a r_in r_out pre post post_err pre' post' post_err' l l' (dfst f_subcomp) (dsnd f_subcomp) ()
  |)

let if_then_else (a:Type)
  (r_in:parser) (r_out: parser)
  (pre_f pre_g: pre_t r_in)
  (post_f: post_t a r_in r_out pre_f)
  (post_g: post_t a r_in r_out pre_g)
  (post_err_f: post_err_t r_in pre_f)
  (post_err_g: post_err_t r_in pre_g)
  (l:memory_invariant)
  (f_ifthenelse:repr a r_in r_out pre_f post_f post_err_f l)
  (g:repr a r_in r_out pre_g post_g post_err_g l)
  (p:Type0)
: Tot Type
= repr a r_in r_out
    (fun v_in -> (p ==> pre_f v_in) /\ ((~ p) ==> pre_g v_in)) // (if_then_else_pre r_in pre_f pre_g p)
    (fun v_in x v_out -> (p ==> post_f v_in x v_out) /\ ((~ p) ==> post_g v_in x v_out)) // (if_then_else_post a r_in r_out pre_f pre_g post_f post_g p)
    (fun v_in -> (p ==> post_err_f v_in) /\ ((~ p) ==> post_err_g v_in)) // (if_then_else_post_err r_in pre_f pre_g post_err_f post_err_g p)
    l

[@@smt_reifiable_layered_effect]
reifiable reflectable total
layered_effect {
  EWrite : a:Type -> (pin: parser) -> (pout: (parser)) -> (pre: pre_t pin) -> (post: post_t a pin pout pre) -> (post_err: post_err_t pin pre) -> (memory_invariant) -> Effect
  with
  repr = repr;
  return = returnc;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}

effect Write
  (a:Type)
  (pin: parser)
  (pout: (parser))
  (pre: pre_t pin)
  (post: post_t a pin pout pre)
  (inv: memory_invariant)
= EWrite a pin pout pre post (fun _ -> False) inv

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

let lift_read_spec
  (a: Type)
  (pre: pure_pre)
  (post: pure_post' a pre)
  (post_err: pure_post_err pre)
  (inv: memory_invariant)
  (r: parser)
  (f_read_spec: read_repr a pre post post_err inv)
: Tot (repr_spec a r (r)
    (fun _ -> pre) // (lift_read_pre pre r)
    (fun st x st' -> st == st' /\ post x) // (lift_read_post a pre post r)
    (fun _ -> post_err ()) // (lift_read_post_err pre post_err r))
  )
= fun st -> 
  match dfst f_read_spec () with
  | Correct res -> Correct (res, st)
  | Error e -> Error e

val lift_read_impl
  (a: Type)
  (pre: pure_pre)
  (post: pure_post' a pre)
  (post_err: pure_post_err pre)
  (inv: memory_invariant)
  (r: parser)
  (f_read_spec: read_repr a pre post post_err inv)
: Tot (repr_impl a r (r) _ _ _ inv (lift_read_spec a pre post post_err inv r f_read_spec))

let lift_read
  (a: Type)
  (pre: pure_pre)
  (post: pure_post' a pre)
  (post_err: pure_post_err pre)
  (inv: memory_invariant)
  (r: parser)
  (f_read_spec: read_repr a pre post post_err inv)
: Tot (repr a r (r)
    (fun _ -> pre) // (lift_read_pre pre r)
    (fun st x st' -> st == st' /\ post x) // (lift_read_post a pre post r)
    (fun _ -> post_err ()) // (lift_read_post_err pre post_err r))
    inv
  )
= (| lift_read_spec a pre post post_err inv r f_read_spec, lift_read_impl a pre post post_err inv r f_read_spec |)

sub_effect ERead ~> EWrite = lift_read

unfold
let destr_repr_spec
  (a:Type u#x)
  (r_in: parser)
  (r_out: parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (post_err: post_err_t r_in pre)
  (l: memory_invariant)
  ($f_destr_spec: unit -> EWrite a r_in r_out pre post post_err l)
: Tot (repr_spec a r_in r_out pre post post_err)
= dfst (reify (f_destr_spec ()))

inline_for_extraction
let destr_repr_impl
  (a:Type u#x)
  (r_in: parser)
  (r_out: parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (post_err: post_err_t r_in pre)
  (l: memory_invariant)
  (f_destr_spec: unit -> EWrite a r_in r_out pre post post_err l)
: Tot (repr_impl a r_in r_out pre post post_err l (destr_repr_spec a r_in r_out pre post post_err l f_destr_spec))
= dsnd (reify (f_destr_spec ()))

inline_for_extraction
unfold
let mk_repr
  (a:Type u#x)
  (r_in: parser)
  (r_out: parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (post_err: post_err_t r_in pre)
  (l: memory_invariant)
  (spec: repr_spec a r_in r_out pre post post_err)
  (impl: repr_impl a r_in r_out pre post post_err l spec)
  ()
: EWrite a r_in r_out pre post post_err l
= EWrite?.reflect (| spec, impl |)

let frame_out
  (a: Type)
  (frame: parser)
  (p: (parser))
: Tot parser
= frame `star` p

let frame_pre
  (frame: parser)
  (pre: pre_t emp)
: Tot (pre_t frame)
= fun _ -> pre ()

let frame_post
  (a: Type)
  (frame: parser)
  (pre: pre_t emp)
  (p: parser)
  (post: post_t a emp p pre)
: Tot (post_t a frame (frame_out a frame p) (frame_pre frame pre))
= fun v_in v (v_in', v_out) -> v_in == v_in' /\ post () v v_out

let frame_post_err
  (frame: parser)
  (pre: pre_t emp)
  (post_err: post_err_t emp pre)
: Tot (post_err_t frame (frame_pre frame pre))
= fun _ -> post_err ()

let frame_spec
  (a: Type)
  (frame: parser)
  (pre: pre_t emp)
  (p: parser)
  (post: post_t a emp p pre)
  (post_err: post_err_t emp pre)
  (l: memory_invariant)
  (inner: unit -> EWrite a emp p pre post post_err l)
: Tot (repr_spec a frame (frame_out a frame p) (frame_pre frame pre) (frame_post a frame pre p post) (frame_post_err frame pre post_err))
= fun fr ->
  match destr_repr_spec a emp p pre post post_err l inner () with
  | Correct (v, w) -> Correct (v, (fr, w))
  | Error e -> Error e

inline_for_extraction
val frame_impl
  (a: Type)
  (frame: parser)
  (pre: pre_t emp)
  (p: parser)
  (post: post_t a emp p pre)
  (post_err: post_err_t emp pre)
  (l: memory_invariant)
  (inner: unit -> EWrite a emp p pre post post_err l)
: Tot (repr_impl a frame (frame_out a frame p) (frame_pre frame pre) (frame_post a frame pre p post) (frame_post_err frame pre post_err) l (frame_spec a frame pre p post post_err l inner))

inline_for_extraction
let frame'
  (a: Type)
  (frame: parser)
  (pre: pre_t emp)
  (p: parser)
  (post: post_t a emp p pre)
  (post_err: post_err_t emp pre)
  (l: memory_invariant)
  (inner: unit -> EWrite a emp p pre post post_err l)
: Tot (unit -> EWrite a frame (frame_out a frame p) (frame_pre frame pre) (frame_post a frame pre p post) (frame_post_err frame pre post_err) l)
= mk_repr
    a frame (frame_out a frame p) (frame_pre frame pre) (frame_post a frame pre p post) (frame_post_err frame pre post_err) l
    (frame_spec a frame pre p post post_err l inner)
    (frame_impl a frame pre p post post_err l inner)

inline_for_extraction
let frame
  (a: Type)
  (frame: parser)
  (pre: pre_t emp)
  (p: parser)
  (post: post_t a emp p pre)
  (post_err: post_err_t emp pre)
  (l: memory_invariant)
  (inner: unit -> EWrite a emp p pre post post_err l)
: EWrite a frame (frame_out a frame p) (frame_pre frame pre) (frame_post a frame pre p post) (frame_post_err frame pre post_err) l
= frame' a frame pre p post post_err l inner ()

let elem_writer_spec
  (p: parser)
  (x: dfst p)
: Tot (repr_spec unit emp (p) (fun _ -> True) (fun _ _ y -> y == x) (fun _ -> False))
= fun _ -> Correct ((), x)

inline_for_extraction
val elem_writer_impl
  (#p: parser)
  (w: leaf_writer p)
  (l: memory_invariant)
  (x: dfst p)
: Tot (repr_impl unit emp (p) (fun _ -> True) (fun _ _ y -> y == x) (fun _ -> False) l (elem_writer_spec p x))

inline_for_extraction
let start
  (#p: parser)
  (w: leaf_writer p)
  (#l: memory_invariant)
  (x: dfst p)
: Write unit emp (p) (fun _ -> True) (fun _ _ y -> y == x) l
= mk_repr
    unit emp (p) (fun _ -> True) (fun _ _ y -> y == x) (fun _ -> False) l
    (elem_writer_spec p x)
    (elem_writer_impl w l x)
    ()

#push-options "--z3rlimit 64"

#restart-solver

let append
  (#fr: parser)
  (#p: parser)
  (w: leaf_writer p)
  (#l: memory_invariant)
  (x: dfst p)
: Write unit fr (fr `star` p) (fun _ -> True) (fun w _ (w', x') -> w' == w /\ x' == x) l
= frame unit fr (fun _ -> True) (p) (fun _ _ x' -> x' == x) (fun _ -> False) l (fun _ -> start w x)

#pop-options

let write_two_ints
  (l: memory_invariant)
  (x y: U32.t)
: Write unit emp (parse_u32 `star` parse_u32) (fun _ -> True) (fun _ _ (x', y') -> x' == x /\ y' == y) l
= start write_u32 x;
  append write_u32 y

let write_two_ints_2
  (l: memory_invariant)
  (x y: U32.t)
  ()
: Write unit emp (parse_u32 `star` parse_u32) (fun _ -> True) (fun _ _ _ -> True) l
= start write_u32 x;
  append write_u32 y

let write_two_ints_2_lemma_1
  (l: memory_invariant)
  (x y: U32.t)
: Lemma
  (destr_repr_spec unit emp (parse_u32 `star` parse_u32) (fun _ -> True) (fun _ _ _ -> True) (fun _ -> False) l (write_two_ints_2 l x y) () == Correct ((), (x, y)) )
= ()

let write_two_ints_2_lemma_2
  (l: memory_invariant)
  (x y: U32.t)
: Lemma
  (True)
= assert (dfst (reify (write_two_ints_2 l x y ())) () == Correct ((), (x, y)))

let write_two_ints_ifthenelse
  (l: memory_invariant)
  (x y: U32.t)
: Write unit emp (parse_u32 `star` parse_u32) (fun _ -> True) (fun _ _ (x', y') -> x' == x /\ y' == (if U32.v x < U32.v y then x else y)) l
= if x `U32.lt` y
  then begin
    start write_u32 x;
    append write_u32 x
  end else begin
    start write_u32 x;
    append write_u32 y
  end

let write_two_ints_ifthenelse_2_aux
  (l: memory_invariant)
  (x y: U32.t)
  ()
: Write unit emp (parse_u32 `star` parse_u32) (fun _ -> True) (fun _ _ _ -> True) l
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
  (destr_repr_spec unit emp (parse_u32 `star` parse_u32) (fun _ -> True) (fun _ _ _ -> True) (fun _ -> False) l (write_two_ints_ifthenelse_2_aux l x y) () == Correct ((), (x, (if U32.v x < U32.v y then x else y))) )
= ()

unfold
let recast_writer_post
  (a:Type u#x)
  (r_in: parser)
  (r_out: parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (post_err: post_err_t r_in pre)
  (l: memory_invariant)
  (f: unit -> EWrite a r_in r_out pre post post_err l)
: Tot (post_t a r_in r_out pre)
=
  fun v_in v v_out -> pre v_in /\ destr_repr_spec a r_in r_out pre post post_err l f v_in == Correct (v, v_out) /\ post v_in v v_out

unfold
let recast_writer_post_err
  (a:Type u#x)
  (r_in: parser)
  (r_out: parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (post_err: post_err_t r_in pre)
  (l: memory_invariant)
  (f: unit -> EWrite a r_in r_out pre post post_err l)
: Tot (post_err_t r_in pre)
=
  fun v_in -> pre v_in /\ Error? (destr_repr_spec a r_in r_out pre post post_err l f v_in) /\ post_err v_in

let recast_writer_spec
  (a:Type u#x)
  (r_in: parser)
  (r_out: parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (post_err: post_err_t r_in pre)
  (l: memory_invariant)
  (f: unit -> EWrite a r_in r_out pre post post_err l)
: Tot (repr_spec a r_in r_out pre (recast_writer_post a r_in r_out pre post post_err l f) (recast_writer_post_err a r_in r_out pre post post_err l f))
= fun v_in -> destr_repr_spec a r_in r_out pre post post_err l f v_in

inline_for_extraction
val recast_writer_impl
  (a:Type u#x)
  (r_in: parser)
  (r_out: parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (post_err: post_err_t r_in pre)
  (l: memory_invariant)
  (f: unit -> EWrite a r_in r_out pre post post_err l)
: Tot (repr_impl a r_in r_out pre (recast_writer_post a r_in r_out pre post post_err l f) (recast_writer_post_err a r_in r_out pre post post_err l f) l (recast_writer_spec a r_in r_out pre post post_err l f))

inline_for_extraction
let recast_writer'
  (a:Type u#x)
  (r_in: parser)
  (r_out: parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (post_err: post_err_t r_in pre)
  (l: memory_invariant)
  (f: unit -> EWrite a r_in r_out pre post post_err l)
: Tot (unit -> EWrite a r_in r_out pre (recast_writer_post a r_in r_out pre post post_err l f) (recast_writer_post_err a r_in r_out pre post post_err l f) l)
= mk_repr a r_in r_out pre (recast_writer_post a r_in r_out pre post post_err l f) (recast_writer_post_err a r_in r_out pre post post_err l f) l
    (recast_writer_spec a r_in r_out pre post post_err l f)
    (recast_writer_impl a r_in r_out pre post post_err l f)

inline_for_extraction
let recast_writer
  (a:Type u#x)
  (r_in: parser)
  (r_out: parser)
  (pre: pre_t r_in)
  (post: post_t a r_in r_out pre)
  (post_err: post_err_t r_in pre)
  (l: memory_invariant)
  ($f: unit -> EWrite a r_in r_out pre post post_err l)
: EWrite a r_in r_out pre (recast_writer_post a r_in r_out pre post post_err l f) (recast_writer_post_err a r_in r_out pre post post_err l f) l
= recast_writer' a r_in r_out pre post post_err l f ()

let write_two_ints_ifthenelse_2
  (l: memory_invariant)
  (x y: U32.t)
: Write unit emp (parse_u32 `star` parse_u32)
    (fun _ -> True)
    (fun _ _ (x', y') -> x' == x /\ y' == (if U32.v x < U32.v y then x else y))
    l
= write_two_ints_ifthenelse_2_aux_lemma l x y;
  recast_writer _ _ _ _ _ _ _ (write_two_ints_ifthenelse_2_aux l x y)

unfold
let frame2_pre
  (frame: parser)
  (ppre: parser)
  (pre: pre_t ppre)
: Tot (pre_t (frame `star` ppre))
= fun (_, x) -> pre x

unfold
let frame2_post
  (a: Type)
  (frame: parser)
  (ppre: parser)
  (pre: pre_t ppre)
  (p: parser)
  (post: post_t a ppre p pre)
: Tot (post_t a (frame `star` ppre) (frame_out a frame p) (frame2_pre frame ppre pre))
= fun (v_frame, v_in) v (v_frame', v_out) -> v_frame == v_frame' /\ post v_in v v_out

unfold
let frame2_post_err
  (frame: parser)
  (ppre: parser)
  (pre: pre_t ppre)
  (post_err: post_err_t ppre pre)
: Tot (post_err_t (frame `star` ppre) (frame2_pre frame ppre pre))
= fun (_, x) -> post_err x

let frame2_spec
  (a: Type)
  (frame: parser)
  (ppre: parser)
  (pre: pre_t ppre)
  (p: parser)
  (post: post_t a ppre p pre)
  (post_err: post_err_t ppre pre)
  (l: memory_invariant)
  (inner: unit -> EWrite a ppre p pre post post_err l)
: Tot (repr_spec a (frame `star` ppre) (frame_out a frame p) (frame2_pre frame ppre pre) (frame2_post a frame ppre pre p post) (frame2_post_err frame ppre pre post_err))
= fun (fr, w_in) ->
  match destr_repr_spec a ppre p pre post post_err l inner w_in with
  | Correct (v, w) -> Correct (v, (fr, w))
  | Error e -> Error e

inline_for_extraction
val frame2_impl
  (a: Type)
  (frame: parser)
  (ppre: parser)
  (pre: pre_t ppre)
  (p: parser)
  (post: post_t a ppre p pre)
  (post_err: post_err_t ppre pre)
  (l: memory_invariant)
  (inner: unit -> EWrite a ppre p pre post post_err l)
: Tot (repr_impl a (frame `star` ppre) (frame_out a frame p) (frame2_pre frame ppre pre) (frame2_post a frame ppre pre p post) (frame2_post_err frame ppre pre post_err) l (frame2_spec a frame ppre pre p post post_err l inner))

inline_for_extraction
let frame2'
  (a: Type)
  (frame: parser)
  (ppre: parser)
  (pre: pre_t ppre)
  (p: parser)
  (post: post_t a ppre p pre)
  (post_err: post_err_t ppre pre)
  (l: memory_invariant)
  (inner: unit -> EWrite a ppre p pre post post_err l)
: Tot (unit -> EWrite a (frame `star` ppre) (frame_out a frame p) (frame2_pre frame ppre pre) (frame2_post a frame ppre pre p post) (frame2_post_err frame ppre pre post_err) l)
= mk_repr
    a (frame `star` ppre) (frame_out a frame p) (frame2_pre frame ppre pre) (frame2_post a frame ppre pre p post) (frame2_post_err frame ppre pre post_err) l
    (frame2_spec a frame ppre pre p post post_err l inner)
    (frame2_impl a frame ppre pre p post post_err l inner)

inline_for_extraction
let frame2
  (a: Type)
  (frame: parser)
  (ppre: parser)
  (pre: pre_t ppre)
  (p: parser)
  (post: post_t a ppre p pre)
  (post_err: post_err_t ppre pre)
  (l: memory_invariant)
  ($inner: unit -> EWrite a ppre p pre post post_err l)
: EWrite a (frame `star` ppre) (frame_out a frame p) (frame2_pre frame ppre pre) (frame2_post a frame ppre pre p post) (frame2_post_err frame ppre pre post_err) l
= frame2' a frame ppre pre p post post_err l inner ()

noeq
type valid_synth_t
  (p1: parser)
  (p2: parser)
  (precond: pre_t p1)
  (f: (x: dfst p1 { precond x }) -> GTot (dfst p2))
= {
    valid_synth_valid:
      (h: HS.mem) ->
      (b: B.buffer U8.t) ->
      (pos: U32.t) ->
      (pos' : U32.t) ->
      Lemma
      (requires (
        valid_pos p1 h b pos pos' /\
        precond (contents p1 h b pos pos')
      ))
      (ensures (
        valid_pos p1 h b pos pos' /\ (
        let x = contents p1 h b pos pos' in
        precond x /\
        valid_pos p2 h b pos pos' /\
        contents p2 h b pos pos' == f x
      )));
    valid_synth_size:
      (x: dfst p1 { precond x }) ->
      Lemma
      (size p1 x == size p2 (f x))
  }

let valid_synth_spec
  (p1: parser)
  (p2: parser)
  (precond: pre_t p1)
  (f: (x: dfst p1 { precond x }) -> GTot (dfst p2))
  (v: valid_synth_t p1 p2 precond f)
: Tot (repr_spec unit p1 (p2) precond (fun vin _ vout -> precond vin /\ f vin == vout) (fun _ -> False))
= fun vin ->
    v.valid_synth_size vin;
    Correct ((), f vin)

inline_for_extraction
val valid_synth_impl
  (p1: parser)
  (p2: parser)
  (precond: pre_t p1)
  (f: (x: dfst p1 { precond x }) -> GTot (dfst p2))
  (v: valid_synth_t p1 p2 precond f)
  (inv: memory_invariant)
: Tot (repr_impl unit p1 (p2) precond (fun vin _ vout -> precond vin /\ f vin == vout) (fun _ -> False) inv (valid_synth_spec p1 p2 precond f v))

inline_for_extraction
let valid_synth_repr
  (p1: parser)
  (p2: parser)
  (precond: pre_t p1)
  (f: (x: dfst p1 { precond x }) -> GTot (dfst p2))
  (v: valid_synth_t p1 p2 precond f)
  (inv: memory_invariant)
: Tot (repr unit p1 (p2) precond (fun vin _ vout -> precond vin /\ f vin == vout) (fun _ -> False) inv)
= (| _, valid_synth_impl p1 p2 precond f v inv |)

inline_for_extraction
let valid_synth
  (p1: parser)
  (p2: parser)
  (precond: pre_t p1)
  (f: (x: dfst p1 { precond x }) -> GTot (dfst p2))
  (inv: memory_invariant)
  (v: valid_synth_t p1 p2 precond f)
: Write unit p1 (p2) precond (fun vin _ vout -> precond vin /\ f vin == vout) inv
= EWrite?.reflect (valid_synth_repr p1 p2 precond f v inv)

inline_for_extraction
val cast
  (p1: parser)
  (p2: parser)
  (precond: pre_t p1)
  (f: (x: dfst p1 { precond x }) -> GTot (dfst p2))
  (v: valid_synth_t p1 p2 precond f)
  (inv: memory_invariant)
  (x1: ptr p1 inv { precond (deref_spec x1) })
: Tot (x2: ptr p2 inv {
    deref_spec x2 == f (deref_spec x1)
  })

let valid_synth_star_assoc_1
  (p1 p2 p3: parser)
: Tot (valid_synth_t ((p1 `star` p2) `star` p3) (p1 `star` (p2 `star` p3)) (fun _ -> True) (fun ((x1, x2), x3) -> (x1, (x2, x3))))
= {
    valid_synth_valid = (fun h b pos pos' ->
      let pos3 = valid_star_inv_spec h (p1 `star` p2) p3 b pos pos' in
      let pos2 = valid_star_inv_spec h p1 p2 b pos pos3 in
      valid_star p2 p3 h b pos2 pos3 pos';
      valid_star p1 (p2 `star` p3) h b pos pos2 pos'
    );
    valid_synth_size = (fun _ -> ());
  }

let valid_synth_star_assoc_2
  (p1 p2 p3: parser)
: Tot (valid_synth_t (p1 `star` (p2 `star` p3)) ((p1 `star` p2) `star` p3) (fun _ -> True) (fun (x1, (x2, x3)) -> ((x1, x2), x3)))
= {
    valid_synth_valid = (fun h b pos pos' ->
      let pos2 = valid_star_inv_spec h p1 (p2 `star` p3) b pos pos' in
      let pos3 = valid_star_inv_spec h p2 p3 b pos2 pos' in
      valid_star p1 p2 h b pos pos2 pos3;
      valid_star (p1 `star` p2) p3 h b pos pos3 pos'
    );
    valid_synth_size = (fun _ -> ());
  }

let check_precond_t
  (p1: parser)
  (precond: pre_t p1)
: Tot Type
=
  (b: B.buffer U8.t) ->
  (len: U32.t { B.len b == len }) ->
  (pos: U32.t) ->
  (pos' : U32.t) ->
  HST.Stack bool
  (requires (fun h ->
    valid_pos p1 h b pos pos'
  ))
  (ensures (fun h res h' ->
    B.modifies B.loc_none h h' /\
    (res == true <==> precond (contents p1 h b pos pos'))
  ))

inline_for_extraction
val check_precond_repr
  (p1: parser)
  (precond: pre_t p1)
  (c: check_precond_t p1 precond)
  (inv: memory_invariant)
: Tot (repr unit p1 (p1) precond (fun vin _ vout -> vin == vout /\ precond vin) (fun vin -> ~ (precond vin)) inv)

inline_for_extraction
let check_precond
  (p1: parser)
  (precond: pre_t p1)
  (c: check_precond_t p1 precond)
  (inv: memory_invariant)
: EWrite unit p1 (p1) precond (fun vin _ vout -> vin == vout /\ precond vin) (fun vin -> ~ (precond vin)) inv
= EWrite?.reflect (check_precond_repr p1 precond c inv)
