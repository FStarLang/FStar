(*
   Copyright 2026 Microsoft Research

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
module Pulse.Extrinsic.HeapLang.Contexts

open Pulse.Extrinsic.HeapLang
module E = Pulse.Extrinsic.HeapLang.Semantics
module M = Pulse.Extrinsic.HeapLang.Memory
module W = Pulse.Extrinsic.WP

let plug (#a #b:ty) (k:context a b) (e:E.packed_expr) : E.packed_expr =
  let E.Pack t e = e in
  if t = a then E.Pack b (fill k e) else E.Pack t e

let resume (#a #b:ty) (k:context a b) (v:E.packed_value) =
  let E.PackValue t v = v in plug k (E.Pack t (Val v))

let steps (#a #b:ty) (k:context a b)
  (e next:E.packed_expr) (h h':M.heap) (spawned:list E.packed_expr)
  : Lemma
      (requires E.packed_step e h next h' spawned)
      (ensures E.packed_step (plug k e) h (plug k next) h' spawned)
  = let E.Pack t bound = e in
    eliminate exists (bound':expr [] t) (children:list E.thread).
      next == E.Pack t bound' /\ spawned == E.pack_threads children /\
      (exists (_:E.step bound h bound' h' children). True)
    with (
      if t = a then (
        eliminate exists (s:E.step bound h bound' h' children). True with (
          let E.ContextStep #_ #_ inner #head #_ #head' #_ #_ hs = s in
          E.fill_compose k inner head;
          E.fill_compose k inner head';
          E.pack_step (E.ContextStep (E.compose k inner) hs)
        )
      )
    )

let inversion (#a #b:ty) (k:context a b)
  (e next:E.packed_expr) (h h':M.heap) (spawned:list E.packed_expr)
  : Lemma
      (requires E.packed_to_val e == None /\ E.packed_step (plug k e) h next h' spawned)
      (ensures exists e'. next == plug k e' /\ E.packed_step e h e' h' spawned)
  = let E.Pack t bound = e in
    if t = a then (
      eliminate exists (next':expr [] b) (children:list E.thread).
        next == E.Pack b next' /\ spawned == E.pack_threads children /\
        (exists (_:E.step (fill k bound) h next' h' children). True)
      with (
        eliminate exists (s:E.step (fill k bound) h next' h' children). True with (
          E.invert_fill k bound s;
          eliminate exists (bound':expr [] a).
            next' == fill k bound' /\ (exists (_:E.step bound h bound' h' children). True)
          with (
            eliminate exists (s':E.step bound h bound' h' children). True with (
              E.pack_step s';
              introduce exists e'. next == plug k e' /\ E.packed_step e h e' h' spawned
              with (E.Pack a bound') and ()
            )
          )
        )
      )
    ) else (
      introduce exists e'. next == plug k e' /\ E.packed_step e h e' h' spawned
      with next and (
        eliminate exists (bound':expr [] t) (children:list E.thread).
          next == E.Pack t bound' /\ spawned == E.pack_threads children /\
          (exists (_:E.step bound h bound' h' children). True)
        with ()
      )
    )

let make_context (#a #b:ty) (k:context a b) : W.context E.language = {
  plug = plug k;
  resume = resume k;
  values = (
    introduce forall e v. E.packed_to_val e == Some v ==> plug k e == resume k v
    with (let E.Pack t e = e in match e with | Val _ -> () | _ -> ())
  );
  nonvalues = (
    introduce forall e. E.packed_to_val e == None ==> E.packed_to_val (plug k e) == None
    with (
      let E.Pack t e = e in
      if t = a then (if to_val e == None then E.fill_not_value k e)
    )
  );
  steps = (
    introduce forall e h e' h' spawned. E.packed_step e h e' h' spawned ==>
      E.packed_step (plug k e) h (plug k e') h' spawned
    with (if E.packed_step e h e' h' spawned then steps k e e' h h' spawned)
  );
  inversion = (
    introduce forall e h next h' spawned.
      E.packed_to_val e == None /\ E.packed_step (plug k e) h next h' spawned ==>
      (exists e'. next == plug k e' /\ E.packed_step e h e' h' spawned)
    with (
      if E.packed_to_val e == None /\ E.packed_step (plug k e) h next h' spawned
      then inversion k e next h h' spawned
    )
  );
}

let let_context (#a #b:ty) (body:expr [a] b) = make_context (LetCtx Hole body)
let seq_context (#b:ty) (rest:expr [] b) = make_context (SeqCtx Hole rest)
