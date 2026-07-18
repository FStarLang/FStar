(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: G. Martinez, N. Swamy
*)

module SealedModel

open FStar.Tactics.Effect

noeq
type sealed (a : Type u#aa) =
  | Seal of (unit -> TacS a)
  (* Note: using TacS which implies the program
  never raises an exception. For a real model of
  `sealed` it should also not loop, but we can't
  specify that here. *)

(* The main axiom in this module: assuming any two functions
at type `unit -> Tac a` are equal. This should be unobservable
in a pure context. *)
assume
val unobs_axiom (#a:Type u#aa) (f g : unit -> Tac a) : Lemma (f == g)

let sealed_singl (#a:Type) (x y : sealed a) : Lemma (x == y) =
  let Seal f = x in
  let Seal g = y in
  unobs_axiom f g

let seal (#a : Type u#aa) (x:a) : Tot (sealed a) =
  Seal (fun () -> x)

let unseal (#a : Type u#aa) (s : sealed a) : TacS a =
  let Seal f = s in
  f ()

(* NOTE: there is nothing saying the value of type `a`
that the function receives precedes s, or anything
similar. See below for what goes wrong if so. *)
let map_seal
  (#a : Type u#aa) (b : Type u#bb)
  (s : sealed a)
  (f : a -> TacS b)
: Tot (sealed b)
=
  Seal (fun () -> f (unseal s))

let bind_seal
  (#a : Type u#aa) (b : Type u#bb)
  (s : sealed a)
  (f : a -> TacS (sealed b))
: Tot (sealed b)
=
  Seal (fun () -> unseal (f (unseal s)))

(* Q: Does `x` precede `seal x`?

   We cannot really assume that, as it interacts badly
   with the fact that all seals are equal whenever an
   inductive contains sealed values of itself. For instance:
*)
noeq
type t =
  | X of sealed t
  | Y

(* If for a value `x : t` we have `x << seal x`, then we
can prove that `x` must be `Y`, which is definitely unexpected. *)

let prec_no_x (x : t) (_ : squash (x << seal x)) : Lemma (x == Y) =
  if X? x then (
    let X s = x in
    assert (s << x);
    sealed_singl s (seal x);
    (* At this point we have s << x << seal x, but s == seal x, so s << s *)
    assert False
  )

(* If the map function above had the type:

        let map_seal
          (#a : Type u#aa) (b : Type u#bb)
          (s : sealed a)
(*see:*)  (f : (x:a{x << s}) -> TacS b)
        : Tot (sealed b)
        =
          Seal (fun () -> f (unseal s))

then `f` could assume that it will never receive
an `X`, but that's just false. *)

type tx = x:t{X? x}

let contra_map_seal_precedes
      (map_seal : (
          (#a : Type0) -> (#b : Type0) ->
          (s : sealed a) ->
          (f : (x:a{x << s}) -> TacS b) ->
          Tot (sealed b)))
      : sealed int =
  let s : sealed t = seal (X (seal Y)) in
  let f (x:t{x << s}) : TacS int =
    match x with
    | X s' ->
      sealed_singl s (seal x);
      prec_no_x x ();
      false_elim ()
    | Y ->
      123
  in
  (* This call must crash *)
  map_seal s f
