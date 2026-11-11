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
module Pulse.Extrinsic.Language

(** Operational vocabulary shared by WP and adequacy, independent of HeapLang
    and separation assertions. A primitive step may update shared state and
    spawn threads. The only required law is that values do not step.

    [pool_step] nondeterministically selects any runnable thread. [execution]
    counts scheduler steps, not logical levels. [safe] asks that every thread
    is a value or can step; [main_returns] observes thread zero without claiming
    that its children have terminated. No fairness assumption is built in. *)
open FStar.List.Tot

noeq
type language = {
  expr: Type0;
  value: Type0;
  state: Type u#4;
  to_val: expr -> option value;
  prim_step: expr -> state -> expr -> state -> list expr -> prop;
  values_stuck: squash (
    forall e s e' s' spawned.
      Some? (to_val e) ==> ~ (prim_step e s e' s' spawned));
}

let reducible (l:language) (e:l.expr) (s:l.state) : prop =
  exists e' s' spawned. l.prim_step e s e' s' spawned

let not_stuck (l:language) (e:l.expr) (s:l.state) : prop =
  Some? (l.to_val e) \/ reducible l e s

let step_not_value (l:language) (e:l.expr) (s:l.state)
  (e':l.expr) (s':l.state) (spawned:list l.expr)
  : Lemma (requires l.prim_step e s e' s' spawned)
          (ensures l.to_val e == None)
  = let _ = l.values_stuck in
    match l.to_val e with | None -> () | Some _ -> ()

noeq
type config (l:language) = {
  threads: list l.expr;
  state: l.state;
}

// Keep terminated threads in place, so thread zero remains the main thread.
noeq
type pool_step (l:language) : config l -> config l -> Type u#4 =
  | Schedule:
      before:list l.expr ->
      e:l.expr ->
      after:list l.expr ->
      s:l.state ->
      e':l.expr ->
      s':l.state ->
      spawned:list l.expr ->
      squash (l.prim_step e s e' s' spawned) ->
      pool_step l
        { threads = before @ (e :: after); state = s }
        { threads = before @ (e' :: (after @ spawned)); state = s' }

noeq
type execution (l:language) : nat -> config l -> config l -> Type u#4 =
  | Done: c:config l -> execution l 0 c c
  | Step:
      #n:nat ->
      #c0:config l ->
      #c1:config l ->
      #c2:config l ->
      pool_step l c0 c1 ->
      execution l n c1 c2 ->
      execution l (n + 1) c0 c2

let safe (l:language) (c:config l) : prop =
  forall e. FStar.List.Tot.memP e c.threads ==> not_stuck l e c.state

let main_returns (l:language) (c:config l) (v:l.value) : prop =
  match c.threads with
  | [] -> False
  | e :: _ -> l.to_val e == Some v
