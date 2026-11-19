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

(** Unlike main_returns, termination here includes every spawned thread. *)
let terminated (l:language) (c:config l) : prop =
  forall e. memP e c.threads ==> Some? (l.to_val e)

(** Safety of all finite execution prefixes, including the empty prefix. *)
let safe_execution (l:language) (c:config l) : prop =
  forall (n:nat) (last:config l) (run:execution l n c last). safe l last

(** A finite run reaches the requested horizon, or all threads finish sooner.
    This is existence of an execution, not an executable scheduler. *)
let runs_for (l:language) (n:nat) (c:config l) : prop =
  exists (k:nat) (last:config l) (run:execution l k c last).
    k <= n /\ safe l last /\ (k == n \/ terminated l last)

let progress (l:language) (c:config l)
  : Lemma (requires safe l c)
      (ensures terminated l c \/ (exists next. nonempty (pool_step l c next)))
  = if terminated l c then ()
    else (
      eliminate exists e. memP e c.threads /\ l.to_val e == None with (
        FStar.List.Tot.Properties.lemma_split_using c.threads e;
        let before, rest = split_using c.threads e in
        match rest with
        | [] -> ()
        | _ :: after ->
          eliminate exists e' s' spawned. l.prim_step e c.state e' s' spawned with (
            let next = { threads = before @ (e' :: (after @ spawned)); state = s' } in
            let step = Schedule before e after c.state e' s' spawned () in
            introduce exists next. nonempty (pool_step l c next)
            with next and (
              introduce exists (step:pool_step l c next). True with step and ()
            )
          )
      )
    )

let rec safe_execution_runs (l:language) (n:nat) (c:config l)
  : Lemma (requires safe_execution l c) (ensures runs_for l n c)
      (decreases n)
  = eliminate forall (k:nat) (last:config l) (run:execution l k c last).
      safe l last with 0 c (Done c);
    if n = 0 || terminated l c then (
      introduce exists (k:nat) (last:config l) (run:execution l k c last).
        k <= n /\ safe l last /\ (k == n \/ terminated l last)
      with 0 c (Done c) and ()
    ) else (
      progress l c;
      eliminate exists next. nonempty (pool_step l c next) with (
        eliminate exists (step:pool_step l c next). True with (
          introduce forall (k:nat) (last:config l) (run:execution l k next last).
            safe l last
          with (
            eliminate forall (k:nat) (last:config l) (run:execution l k c last).
              safe l last with (k + 1) last (Step step run)
          );
          safe_execution_runs l (n - 1) next;
          eliminate exists (k:nat) (last:config l) (run:execution l k next last).
            k <= n - 1 /\ safe l last /\ (k == n - 1 \/ terminated l last)
          with (
            introduce exists (k:nat) (last:config l) (run:execution l k c last).
              k <= n /\ safe l last /\ (k == n \/ terminated l last)
            with (k + 1) last (Step step run) and ()
          )
        )
      )
    )
