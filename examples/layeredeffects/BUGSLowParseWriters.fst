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

module BUGSLowParseWriters

let memory_invariant : Type0 = nat

(*
// also makes the `assert False` at the bottom succeed
noeq
type memory_invariant : Type0 = | Meminv

// this one will make that `assert False` fail:
let memory_invariant : Type0 = unit
*)

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


let read_repr_spec (a:Type u#x) (pre: pure_pre) (post: pure_post' a pre) (post_err: pure_post_err pre)  : Tot (Type u#x) =
  unit ->
  Ghost (result a)
  (requires pre)
  (ensures (fun res ->
    match res with
    | Correct v -> post v
    | Error _ -> post_err ()
  ))

noeq
type read_repr
  (a:Type u#x)
  (pre: pure_pre)
  (post: pure_post' a pre)
  (post_err: pure_post_err pre)
  (l: memory_invariant)
= | ReadRepr:
     spec: read_repr_spec a pre post post_err ->
     read_repr a pre post post_err l

let read_return_spec
  (a:Type) (x:a)
: Tot (read_repr_spec a True (fun res -> res == x) (fun _ -> False))
= fun _ -> Correct x

let read_return
  (a:Type) (x:a) (inv: memory_invariant)
: Tot (read_repr a True (fun res -> res == x) (fun _ -> False) inv)
= ReadRepr (read_return_spec a x)

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
= ReadRepr (read_bind_spec  a b pre_f post_f post_err_f pre_g post_g post_err_g (ReadRepr?.spec f_bind) (fun x -> ReadRepr?.spec (g x)))

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
= read_subcomp_spec_cond a pre post post_err pre' post' post_err'

let read_subcomp_spec (a:Type)
  (pre: pure_pre) (post: pure_post' a pre) (post_err: pure_post_err pre)
  (pre': pure_pre) (post': pure_post' a pre') (post_err': pure_post_err pre')
  (f_subcomp:read_repr_spec a pre post post_err)
: Pure (read_repr_spec a pre' post' post_err')
  (requires (read_subcomp_spec_cond a pre post post_err pre' post' post_err'))
  (ensures (fun _ -> True))
= (fun x -> f_subcomp x)

let read_subcomp (a:Type)
  (pre: pure_pre) (post: pure_post' a pre) (post_err: pure_post_err pre)
  (pre': pure_pre) (post': pure_post' a pre') (post_err': pure_post_err pre')
  (l:memory_invariant)
  (l' : memory_invariant)
  (f_subcomp:read_repr a pre post post_err l)
: Pure (read_repr a pre' post' post_err' l')
  (requires (read_subcomp_cond a pre post post_err pre' post' post_err' l l'))
  (ensures (fun _ -> True))
= ReadRepr (read_subcomp_spec a pre post post_err pre' post' post_err' (ReadRepr?.spec f_subcomp))

let read_if_then_else (a:Type)
  (pre_f pre_g: pure_pre)
  (post_f: pure_post' a pre_f)
  (post_g: pure_post' a pre_g)
  (post_err_f: pure_post_err pre_f)
  (post_err_g: pure_post_err pre_g)
  (l:memory_invariant)
  (f_ifthenelse:read_repr a pre_f post_f post_err_f l)
  (g:read_repr a pre_g post_g post_err_g l)
  (p:bool)
: Tot Type
= read_repr a
    ((p ==> pre_f) /\ ((~ p) ==> pre_g)) // (read_if_then_else_pre pre_f pre_g p)
    (fun x -> (p ==> post_f x) /\ ((~ p) ==> post_g x)) // (read_if_then_else_post a pre_f pre_g post_f post_g p)
    (fun _ -> (p ==> post_err_f ()) /\ ((~ p) ==> post_err_g ())) // (read_if_then_else_post_err pre_f pre_g post_err_f post_err_g p)
    l

[@@allow_informative_binders]
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

let lift_pure_read (a:Type) (wp:pure_wp a)
  (l: memory_invariant)
  (f_pure:eqtype_as_type unit -> PURE a wp)
: Pure (read_repr a
    (wp (fun _ -> True)) // (lift_pure_read_pre a wp)
    (fun x -> ~ (wp (fun x' -> ~ (x == x')))) // (lift_pure_read_post a wp)
    (fun _ -> False) // (lift_pure_read_post_err a wp))
    l
  )
  (requires (pure_wp_mono a wp))
  (ensures (fun _ -> True))
= ReadRepr (lift_pure_read_spec a wp f_pure)

sub_effect PURE ~> ERead = lift_pure_read

let reify_read_spec
  (a:Type u#x)
  (pre: pure_pre)
  (post: pure_post' a pre)
  (post_err: pure_post_err pre)
  (l: memory_invariant)
  ($r: unit -> ERead a pre post post_err l)
: GTot (read_repr_spec a pre post post_err)
= ReadRepr?.spec (reify (r ()))

let read_bind_spec'
  (inv: memory_invariant)
  (a b: Type)
  (f: (unit -> Read a True (fun _ -> True) inv))
  (g: (a -> unit -> Read b True (fun _ -> True) inv))
: GTot (result b)
=
   match reify_read_spec _ _ _ _ _ f () with
    | Correct x -> reify_read_spec _ _ _ _ _ (g x) ()

let read_bind_impl'
  (inv: memory_invariant)
  (a b: Type)
  (f: (unit -> Read a True (fun _ -> True) inv))
  (g: (a -> unit -> Read b True (fun _ -> True) inv))
  ()
: Read b True (fun _ -> True) inv
= let x = f () in g x ()

[@@expect_failure]
let read_bind_correct
  (inv: memory_invariant)
  (a b: Type)
  (f: (unit -> Read a True (fun _ -> True) inv))
  (g: (a -> unit -> Read b True (fun _ -> True) inv))
: Lemma
      (reify_read_spec _ _ _ _ _ (read_bind_impl' inv a b f g) () ==
        read_bind_spec' inv a b f g)
= let _ = reify_read_spec _ _ _ _ _ (read_bind_impl' inv a b f g) () in
  assert False
