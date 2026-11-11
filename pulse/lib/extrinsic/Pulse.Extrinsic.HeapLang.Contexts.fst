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

let let_plug (#a #b:ty) (body:expr [a] b) (e:E.packed_expr) : E.packed_expr =
  let E.Pack t e = e in
  if t = a then E.Pack b (Let e body) else E.Pack t e

let let_resume (#a #b:ty) (body:expr [a] b) (v:E.packed_value) =
  let E.PackValue t v = v in let_plug body (E.Pack t (Val v))

let let_steps (#a #b:ty) (body:expr [a] b)
  (e next:E.packed_expr) (h h':M.heap) (spawned:list E.packed_expr)
  : Lemma
      (requires E.packed_step e h next h' spawned)
      (ensures E.packed_step (let_plug body e) h (let_plug body next) h' spawned)
  = let E.Pack t bound = e in
    eliminate exists (bound':expr [] t) (children:list E.thread).
      next == E.Pack t bound' /\ spawned == E.pack_threads children /\
      (exists (_:E.step bound h bound' h' children). True)
    with (
      if t = a then (
        eliminate exists (s:E.step bound h bound' h' children). True with (
          let E.ContextStep #_ #_ k #_ #_ #_ #_ #_ hs = s in
          E.pack_step (E.ContextStep (E.LetCtx k body) hs)
        )
      )
    )

let let_inversion (#a #b:ty) (body:expr [a] b)
  (e next:E.packed_expr) (h h':M.heap) (spawned:list E.packed_expr)
  : Lemma
      (requires E.packed_to_val e == None /\ E.packed_step (let_plug body e) h next h' spawned)
      (ensures exists e'. next == let_plug body e' /\ E.packed_step e h e' h' spawned)
  = let E.Pack t bound = e in
    if t = a then (
      eliminate exists (next':expr [] b) (children:list E.thread).
        next == E.Pack b next' /\ spawned == E.pack_threads children /\
        (exists (_:E.step (Let bound body) h next' h' children). True)
      with (
        eliminate exists (s:E.step (Let bound body) h next' h' children). True with (
          E.invert_let bound body s;
          eliminate exists (bound':expr [] a).
            next' == Let bound' body /\ (exists (_:E.step bound h bound' h' children). True)
          with (
            eliminate exists (s':E.step bound h bound' h' children). True with (
              E.pack_step s';
              introduce exists e'. next == let_plug body e' /\ E.packed_step e h e' h' spawned
              with (E.Pack a bound') and ()
            )
          )
        )
      )
    ) else (
      eliminate exists (bound':expr [] t) (children:list E.thread).
        next == E.Pack t bound' /\ spawned == E.pack_threads children /\
        (exists (_:E.step bound h bound' h' children). True)
      with (
        introduce exists e'. next == let_plug body e' /\ E.packed_step e h e' h' spawned
        with next and ()
      )
    )

let let_context (#a #b:ty) (body:expr [a] b) : W.context E.language = {
  plug = let_plug body;
  resume = let_resume body;
  values = (
    introduce forall e v. E.packed_to_val e == Some v ==> let_plug body e == let_resume body v
    with (let E.Pack t e = e in match e with | Val _ -> () | _ -> ())
  );
  nonvalues = (
    introduce forall e. E.packed_to_val e == None ==> E.packed_to_val (let_plug body e) == None
    with (let E.Pack t e = e in ())
  );
  steps = (
    introduce forall e h e' h' spawned. E.packed_step e h e' h' spawned ==>
      E.packed_step (let_plug body e) h (let_plug body e') h' spawned
    with (if E.packed_step e h e' h' spawned then let_steps body e e' h h' spawned)
  );
  inversion = (
    introduce forall e h next h' spawned.
      E.packed_to_val e == None /\ E.packed_step (let_plug body e) h next h' spawned ==>
      (exists e'. next == let_plug body e' /\ E.packed_step e h e' h' spawned)
    with (
      if E.packed_to_val e == None /\ E.packed_step (let_plug body e) h next h' spawned
      then let_inversion body e next h h' spawned
    )
  );
}

let seq_plug (#b:ty) (rest:expr [] b) (e:E.packed_expr) : E.packed_expr =
  let E.Pack t e = e in
  if t = TUnit then E.Pack b (Seq e rest) else E.Pack t e

let seq_resume (#b:ty) (rest:expr [] b) (v:E.packed_value) =
  let E.PackValue t v = v in seq_plug rest (E.Pack t (Val v))

let seq_steps (#b:ty) (rest:expr [] b)
  (e next:E.packed_expr) (h h':M.heap) (spawned:list E.packed_expr)
  : Lemma
      (requires E.packed_step e h next h' spawned)
      (ensures E.packed_step (seq_plug rest e) h (seq_plug rest next) h' spawned)
  = let E.Pack t first = e in
    eliminate exists (first':expr [] t) (children:list E.thread).
      next == E.Pack t first' /\ spawned == E.pack_threads children /\
      (exists (_:E.step first h first' h' children). True)
    with (
      if t = TUnit then (
        eliminate exists (s:E.step first h first' h' children). True with (
          let E.ContextStep #_ #_ k #_ #_ #_ #_ #_ hs = s in
          E.pack_step (E.ContextStep (E.SeqCtx k rest) hs)
        )
      )
    )

let seq_inversion (#b:ty) (rest:expr [] b)
  (e next:E.packed_expr) (h h':M.heap) (spawned:list E.packed_expr)
  : Lemma
      (requires E.packed_to_val e == None /\ E.packed_step (seq_plug rest e) h next h' spawned)
      (ensures exists e'. next == seq_plug rest e' /\ E.packed_step e h e' h' spawned)
  = let E.Pack t first = e in
    if t = TUnit then (
      eliminate exists (next':expr [] b) (children:list E.thread).
        next == E.Pack b next' /\ spawned == E.pack_threads children /\
        (exists (_:E.step (Seq first rest) h next' h' children). True)
      with (
        eliminate exists (s:E.step (Seq first rest) h next' h' children). True with (
          E.invert_seq first rest s;
          eliminate exists (first':E.thread).
            next' == Seq first' rest /\ (exists (_:E.step first h first' h' children). True)
          with (
            eliminate exists (s':E.step first h first' h' children). True with (
              E.pack_step s';
              introduce exists e'. next == seq_plug rest e' /\ E.packed_step e h e' h' spawned
              with (E.Pack TUnit first') and ()
            )
          )
        )
      )
    ) else (
      eliminate exists (first':expr [] t) (children:list E.thread).
        next == E.Pack t first' /\ spawned == E.pack_threads children /\
        (exists (_:E.step first h first' h' children). True)
      with (
        introduce exists e'. next == seq_plug rest e' /\ E.packed_step e h e' h' spawned
        with next and ()
      )
    )

let seq_context (#b:ty) (rest:expr [] b) : W.context E.language = {
  plug = seq_plug rest;
  resume = seq_resume rest;
  values = (
    introduce forall e v. E.packed_to_val e == Some v ==> seq_plug rest e == seq_resume rest v
    with (let E.Pack t e = e in match e with | Val _ -> () | _ -> ())
  );
  nonvalues = (
    introduce forall e. E.packed_to_val e == None ==> E.packed_to_val (seq_plug rest e) == None
    with (let E.Pack t e = e in ())
  );
  steps = (
    introduce forall e h e' h' spawned. E.packed_step e h e' h' spawned ==>
      E.packed_step (seq_plug rest e) h (seq_plug rest e') h' spawned
    with (if E.packed_step e h e' h' spawned then seq_steps rest e e' h h' spawned)
  );
  inversion = (
    introduce forall e h next h' spawned.
      E.packed_to_val e == None /\ E.packed_step (seq_plug rest e) h next h' spawned ==>
      (exists e'. next == seq_plug rest e' /\ E.packed_step e h e' h' spawned)
    with (
      if E.packed_to_val e == None /\ E.packed_step (seq_plug rest e) h next h' spawned
      then seq_inversion rest e next h h' spawned
    )
  );
}
