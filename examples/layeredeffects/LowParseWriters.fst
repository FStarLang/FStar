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
: Ghost Type0
  (requires True)
  (ensures (fun _ ->
    B.live h b /\
    U32.v pos <= U32.v pos' /\
    U32.v pos' <= B.length b
  ))

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

inline_for_extraction
let repr_spec (a:Type u#x) (r_in: parser) (r_out:a -> parser) : Tot (Type u#x) =
  (v_in: dfst r_in) ->
  GTot (v: a & dfst (r_out v))

inline_for_extraction
let repr_impl (a:Type u#x) (r_in: parser) (r_out:a -> parser) (b: B.buffer U8.t) (spec: repr_spec a r_in r_out) : Tot Type0 =
  (pos1: U32.t { U32.v pos1 <= B.length b }) ->
  HST.Stack (a & U32.t)
    (requires (fun h ->
      valid_pos r_in h b 0ul pos1
    ))
    (ensures (fun h (v, pos2) h' ->
      U32.v pos1 <= U32.v pos2 /\
      valid_pos (r_out v) h' b 0ul pos2 /\
      B.modifies (B.loc_buffer_from_to b 0ul pos2) h h' /\
      spec (contents r_in h b 0ul pos1) ==
        (| v, contents (r_out v) h' b 0ul pos2 |)
    ))

(* FIXME: WHY WHY WHY can't I index `repr` with the buffer when I define the WRITE effect below? *)
// assume val buf: B.buffer U8.t

type u8 : Type0 = U8.t

inline_for_extraction
let repr
  (a: Type u#x)
  (r_in: parser) (r_out:a -> parser)
  (buf:B.buffer u8)
: Tot (Type u#x)
= dtuple2 (repr_spec a r_in r_out) (repr_impl a r_in r_out buf)

let return_spec
  (a:Type) (x:a) (r: a -> parser)
: Tot (repr_spec a (r x) r)
= fun c -> (| x, c |)

inline_for_extraction
let return_impl
  (a:Type) (x:a) (r: a -> parser)
  (b: B.buffer u8)
: Tot (repr_impl a (r x) r b (return_spec a x r))
= fun pos1 -> (x, pos1)

inline_for_extraction
let returnc
  (a:Type) (x:a) (r: a -> parser) (buf:B.buffer u8)
: Tot (repr a (r x) r buf)
= (| return_spec a x r, return_impl a x r buf |)

let bind_spec (a:Type) (b:Type)
  (r_in_f:parser) (r_out_f:a -> parser)
  (r_out_g:b -> parser)
  (f:repr_spec a r_in_f r_out_f) (g:(x:a -> repr_spec b (r_out_f x) r_out_g))
: Tot (repr_spec b r_in_f r_out_g)
= fun c ->
  let (| x, cf |) = f c in
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
  (r_out_g:b -> parser)
  (f:repr_spec a r_in_f r_out_f)
  (g:(x:a -> repr_spec b (r_out_f x) r_out_g))
  (buf: B.buffer u8)
  (f' : repr_impl a r_in_f r_out_f buf f)
  (g' : (x: a -> repr_impl b (r_out_f x) r_out_g buf (g x)))
: Tot (repr_impl b r_in_f r_out_g buf (bind_spec a b r_in_f r_out_f r_out_g f g))
= fun pos ->
  match f' pos with
  | (x, posf) -> g' x posf

inline_for_extraction
let bind (a:Type) (b:Type)
  (r_in_f: parser) (r_out_f:a -> parser)
  (r_out_g:b -> parser) (buf:B.buffer u8)
  (f:repr a r_in_f r_out_f buf) (g:(x:a -> repr b (r_out_f x) r_out_g buf))
: Tot (repr b r_in_f r_out_g buf)
= (| bind_spec a b r_in_f r_out_f r_out_g (dfst f) (fun x -> dfst (g x)), bind_impl a b r_in_f r_out_f r_out_g (dfst f) (fun x -> dfst (g x)) buf (dsnd f) (fun x -> dsnd (g x)) |)

inline_for_extraction
let subcomp (a:Type)
  (r_in:parser) (r_out:a -> parser) (buf:B.buffer u8)
  (f:repr a r_in r_out buf)
: (repr a r_in r_out buf)
= f

let if_then_else (a:Type)
  (r_in:parser) (r_out:a -> parser) (buf:B.buffer u8)
  (f:repr a r_in r_out buf) (g:repr a r_in r_out buf)
  (p:Type0)
: Type
= repr a r_in r_out buf

#push-options "--print_universes"

reifiable reflectable
layered_effect {
  WRITE : a:Type -> parser -> (a -> parser) -> B.buffer u8 -> Effect
  with
  repr = repr;
  return = returnc;
  bind = bind;
  subcomp = subcomp;
  if_then_else = if_then_else
}

let wp_true (a: Type) (wp: pure_wp a) : GTot Type0 = wp (fun _ -> True)

let lift_pure_rst_spec
  (a:Type) (wp:pure_wp a { wp_true a wp }) (r:parser) (f:unit -> PURE a wp)
: Tot (repr_spec a r (fun _ -> r))
= fun v -> (| f (), v |)

let lift_pure_rst_impl
  (a:Type) (wp:pure_wp a { wp_true a wp }) (r:parser) (f:unit -> PURE a wp)
: Tot (repr_impl a r (fun _ -> r) buf (lift_pure_rst_spec a wp r f))
= fun pos ->
    FStar.Monotonic.Pure.wp_monotonic_pure ();
    (f (), pos)

let lift_pure_rst (a:Type) (wp:pure_wp a) (r:parser) (f:unit -> PURE a wp)
: Pure (repr a r (fun _ -> r))
  (requires wp (fun _ -> True))
  (ensures fun _ -> True)
= (| lift_pure_rst_spec a wp r f, lift_pure_rst_impl a wp r f |)

sub_effect PURE ~> WRITE = lift_pure_rst

assume
val star' (#t1 #t2: Type) (p1: parser' t1) (p2: parser' t2) : Tot (parser' (t1 & t2))

let star (p1 p2: parser) : Tot parser = (| (dfst p1 & dfst p2), star' (dsnd p1) (dsnd p2) |)

(*
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
  [SMTPat (valid_pos p1 h b pos1 pos2); SMTPat (valid_pos p2 h b pos2 pos3)]

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
  [SMTPatOr [
    [SMTPat (valid_pos p h b pos pos'); SMTPat (B.modifies l h h')];
    [SMTPat (valid_pos p h' b pos pos'); SMTPat (B.modifies l h h')];
  ]]
  

(*

assume
val emp' : parser' unit

let emp : parser = (| unit, emp' |)

assume
val valid_pos_emp
  (h: HS.mem)
  (b: B.buffer U8.t)
  (pos: U32.t)
  (pos' : U32.t)
: Lemma
  (valid_pos emp h b pos pos' <==> (B.live h b /\ pos' == pos /\ U32.v pos <= B.length b))
  [SMTPat (valid_pos emp h b pos pos')]




let push'


let if_then_else (a:Type)
  (r_in:resource) (r_out:a -> resource) (b:Type0)
  (f:repr a r_in r_out b) (g:repr a r_in r_out b)
  (p:Type0)
: Type
= repr a r_in r_out b


let return (#a:Type) (#r:a -> resource) (x:a)
: RSTATE a (r x) r True
= RSTATE?.reflect (returnc a x r)

assume val wp_monotonic_pure (_:unit)
  : Lemma
    (forall (a:Type) (wp:pure_wp a).
       (forall (p q:pure_post a).
          (forall (x:a). p x ==> q x) ==>
          (wp p ==> wp q)))

let lift_pure_rst (a:Type) (wp:pure_wp a) (r:resource) (f:unit -> PURE a wp)
: Pure (repr a r (fun _ -> r) True)
  (requires wp (fun _ -> True))
  (ensures fun _ -> True)
= wp_monotonic_pure ();
  fun _ -> f ()

sub_effect PURE ~> RSTATE = lift_pure_rst


assume val emp : resource

assume val array : Type0
assume val array_resource (a:array) : resource

assume val alloc (_:unit) : RSTATE array emp array_resource True

let test ()
: RSTATE array emp array_resource True
= let ptr = alloc () in
  return ptr

type t =
  | C : t
  | D : t

assume val rst_unit (_:unit) : RSTATE unit emp (fun _ -> emp) True

let test_match (x:t) : RSTATE unit emp (fun _ -> emp) True =
  match x with
  | C -> rst_unit ()
  | D -> rst_unit ()


(*
 * Following example showcases a bug in checking match terms for layered effects
 *
 * When typechecking the pattern `C a x`, we generate a term with projectors and discriminators
 *   for each of the pattern bvs, a and x in this case, and those terms are then lax checked
 * Crucially when lax checking pat_bv_tm for `x`, `a` must be in the environement,
 *   earlier it wasn't
 *)

noeq
type m : Type -> Type =
| C1 : a:Type -> x:a -> m a
| D1 : a:Type -> x:a -> m a

let test_match2 (a:Type) (f:m a) : RSTATE unit emp (fun _ -> emp) True
= match f with
  | C1 a x -> rst_unit ()
  | D1 a x -> rst_unit ()


assume val false_pre (_:squash False) : RSTATE unit emp (fun _ -> emp) True

[@@expect_failure]
let test_false_pre () : RSTATE unit emp (fun _ -> emp) True
= false_pre ()


/// Test that bind precondition is checked

assume val f_test_bind (_:unit) : RSTATE unit emp (fun _ -> emp) True
assume val g_test_bind (_:unit) : RSTATE unit emp (fun _ -> emp) False

[@@expect_failure]
let test_bind () : RSTATE unit emp (fun _ -> emp) True
= f_test_bind ();
  g_test_bind ()
