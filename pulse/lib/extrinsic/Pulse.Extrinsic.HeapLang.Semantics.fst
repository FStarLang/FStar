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
module Pulse.Extrinsic.HeapLang.Semantics

open Pulse.Extrinsic.HeapLang
module M = Pulse.Extrinsic.HeapLang.Memory
module L = Pulse.Extrinsic.Language
module H = PulseCore.Heap

let thread = expr [] TUnit

noeq
type head_step : #t:ty -> expr [] t -> M.heap -> expr [] t -> M.heap -> list thread -> Type u#4 =
  | Beta: #a:ty -> #b:ty -> v:value a -> body:expr [a] b -> h:M.heap ->
      head_step (Let (Val v) body) h (substitute v body) h []
  | Branch: #t:ty -> b:bool -> e1:expr [] t -> e2:expr [] t -> h:M.heap ->
      head_step (If (Val b) e1 e2) h (if b then e1 else e2) h []
  | Sequence: #t:ty -> e:expr [] t -> h:M.heap ->
      head_step (Seq (Val ()) e) h e h []
  | Plus: x:int -> y:int -> h:M.heap ->
      head_step (Add (Val x) (Val y)) h (Val (x + y)) h []
  | Equal: x:int -> y:int -> h:M.heap ->
      head_step (Eq (Val x) (Val y)) h (Val (x = y)) h []
  | New: v:int -> r:H.core_ref -> h:M.heap -> h':M.heap ->
      squash (M.allocation h v r h') ->
      head_step (Alloc (Val v)) h (Val r) h' []
  | Read: r:H.core_ref -> v:int -> h:M.heap ->
      squash (M.contents h r v) ->
      head_step (Load (Val r)) h (Val v) h []
  | Write: r:H.core_ref -> v:int -> h:M.heap -> h':M.heap ->
      squash (M.store h r v h') ->
      head_step (Store (Val r) (Val v)) h (Val ()) h' []
  | CompareExchange: r:H.core_ref -> expected:int -> desired:int ->
      success:bool -> h:M.heap -> h':M.heap ->
      squash (M.cas h r expected desired success h') ->
      head_step (Cas (Val r) (Val expected) (Val desired)) h (Val success) h' []
  | Spawn: e:thread -> h:M.heap ->
      head_step (Fork e) h (Val ()) h [e]
  | Unroll: c:expr [] TBool -> body:thread -> h:M.heap ->
      head_step (While c body) h
        (If c (Seq body (While c body)) (Val ())) h []

noeq
type step : #t:ty -> expr [] t -> M.heap -> expr [] t -> M.heap -> list thread -> Type u#4 =
  | ContextStep:
      #a:ty -> #b:ty ->
      k:context a b ->
      #e:expr [] a -> #h:M.heap -> #e':expr [] a -> #h':M.heap -> #spawned:list thread ->
      head_step e h e' h' spawned ->
      step (fill k e) h (fill k e') h' spawned

let head_not_value (#t:ty) (#e #e':expr [] t) (#h #h':M.heap) (#spawned:list thread)
  (s:head_step e h e' h' spawned)
  : Lemma (to_val e == None)
  = match s with
    | Beta _ _ _ | Branch _ _ _ _ | Sequence _ _ | Plus _ _ _
    | Equal _ _ _ | New _ _ _ _ _ | Read _ _ _ _ | Write _ _ _ _ _
    | CompareExchange _ _ _ _ _ _ _ | Spawn _ _ | Unroll _ _ _ -> ()

let fill_not_value (#a #b:ty) (k:context a b) (e:expr [] a)
  : Lemma (requires to_val e == None)
          (ensures to_val (fill k e) == None)
  = match k with
    | Hole -> ()
    | _ -> ()

let step_not_value (#t:ty) (#e #e':expr [] t) (#h #h':M.heap) (#spawned:list thread)
  (s:step e h e' h' spawned)
  : Lemma (to_val e == None)
  = let ContextStep #_ #_ k #head #_ #_ #_ #_ s = s in
    head_not_value s;
    fill_not_value k head

let head_redex (#t:ty) (e:expr [] t) : bool =
  match e with
  | Let e _ | If e _ _ | Seq e _ | Alloc e | Load e -> Some? (to_val e)
  | Add e1 e2 | Eq e1 e2 | Store e1 e2 ->
      Some? (to_val e1) && Some? (to_val e2)
  | Cas e1 e2 e3 -> Some? (to_val e1) && Some? (to_val e2) && Some? (to_val e3)
  | Fork _ | While _ _ -> true
  | _ -> false

let context_head (#a #b:ty) (k:context a b) (e:expr [] a)
  : Lemma (requires to_val e == None /\ head_redex (fill k e))
          (ensures Hole? k)
  = match k with
    | Hole -> ()
    | LetCtx k _ -> fill_not_value k e
    | IfCtx k _ _ -> fill_not_value k e
    | SeqCtx k _ -> fill_not_value k e
    | AddLeft k _ -> fill_not_value k e
    | AddRight _ k -> fill_not_value k e
    | EqLeft k _ -> fill_not_value k e
    | EqRight _ k -> fill_not_value k e
    | AllocCtx k -> fill_not_value k e
    | LoadCtx k -> fill_not_value k e
    | StoreLeft k _ -> fill_not_value k e
    | StoreRight _ k -> fill_not_value k e
    | CasRef k _ _ -> fill_not_value k e
    | CasExpected _ k _ -> fill_not_value k e
    | CasDesired _ _ k -> fill_not_value k e

let invert_head (#t:ty) (#e #e':expr [] t) (#h #h':M.heap) (#spawned:list thread)
  (s:step e h e' h' spawned)
  : Lemma (requires head_redex e)
          (ensures exists (_:head_step e h e' h' spawned). True)
  = let ContextStep #_ #_ k #head #_ #_ #_ #_ hs = s in
    head_not_value hs;
    context_head k head;
    match k with
    | Hole ->
        introduce exists (_:head_step e h e' h' spawned). True with hs and ()
    | _ -> ()

let invert_let (#a #b:ty) (bound:expr [] a) (body:expr [a] b)
  (#next:expr [] b) (#h #h':M.heap) (#spawned:list thread)
  (s:step (Let bound body) h next h' spawned)
  : Lemma
      (requires to_val bound == None)
      (ensures exists (bound':expr [] a).
        next == Let bound' body /\ (exists (_:step bound h bound' h' spawned). True))
  = let ContextStep #_ #_ k #head #_ #head' #_ #_ hs = s in
    match k with
    | Hole -> let Beta _ _ _ = hs in ()
    | LetCtx inner _ ->
        introduce exists (bound':expr [] a).
          next == Let bound' body /\ (exists (_:step bound h bound' h' spawned). True)
        with (fill inner head') and (
          introduce exists (_:step bound h (fill inner head') h' spawned). True
          with (ContextStep inner hs) and ()
        )
    | _ -> ()

let invert_seq (#t:ty) (first:thread) (rest:expr [] t)
  (#next:expr [] t) (#h #h':M.heap) (#spawned:list thread)
  (s:step (Seq first rest) h next h' spawned)
  : Lemma
      (requires to_val first == None)
      (ensures exists (first':thread).
        next == Seq first' rest /\ (exists (_:step first h first' h' spawned). True))
  = let ContextStep #_ #_ k #head #_ #head' #_ #_ hs = s in
    match k with
    | Hole -> let Sequence _ _ = hs in ()
    | SeqCtx inner _ ->
        introduce exists (first':thread).
          next == Seq first' rest /\ (exists (_:step first h first' h' spawned). True)
        with (fill inner head') and (
          introduce exists (_:step first h (fill inner head') h' spawned). True
          with (ContextStep inner hs) and ()
        )
    | _ -> ()

let rec compose (#a #b #c:ty) (outer:context b c) (inner:context a b)
  : Tot (context a c) (decreases outer)
  = match outer with
    | Hole -> inner
    | LetCtx k body -> LetCtx (compose k inner) body
    | IfCtx k yes no -> IfCtx (compose k inner) yes no
    | SeqCtx k rest -> SeqCtx (compose k inner) rest
    | AddLeft k right -> AddLeft (compose k inner) right
    | AddRight left k -> AddRight left (compose k inner)
    | EqLeft k right -> EqLeft (compose k inner) right
    | EqRight left k -> EqRight left (compose k inner)
    | AllocCtx k -> AllocCtx (compose k inner)
    | LoadCtx k -> LoadCtx (compose k inner)
    | StoreLeft k right -> StoreLeft (compose k inner) right
    | StoreRight left k -> StoreRight left (compose k inner)
    | CasRef k expected desired -> CasRef (compose k inner) expected desired
    | CasExpected r k desired -> CasExpected r (compose k inner) desired
    | CasDesired r expected k -> CasDesired r expected (compose k inner)

let rec fill_compose (#a #b #c:ty) (outer:context b c) (inner:context a b) (e:expr [] a)
  : Lemma (fill (compose outer inner) e == fill outer (fill inner e)) (decreases outer)
  = match outer with
    | Hole -> ()
    | LetCtx k _ -> fill_compose k inner e
    | IfCtx k _ _ -> fill_compose k inner e
    | SeqCtx k _ -> fill_compose k inner e
    | AddLeft k _ -> fill_compose k inner e
    | AddRight _ k -> fill_compose k inner e
    | EqLeft k _ -> fill_compose k inner e
    | EqRight _ k -> fill_compose k inner e
    | AllocCtx k -> fill_compose k inner e
    | LoadCtx k -> fill_compose k inner e
    | StoreLeft k _ -> fill_compose k inner e
    | StoreRight _ k -> fill_compose k inner e
    | CasRef k _ _ -> fill_compose k inner e
    | CasExpected _ k _ -> fill_compose k inner e
    | CasDesired _ _ k -> fill_compose k inner e

let head_is_redex (#t:ty) (#e #e':expr [] t) (#h #h':M.heap) (#spawned:list thread)
  (s:head_step e h e' h' spawned)
  : Lemma (head_redex e)
  = match s with
    | Beta _ _ _ | Branch _ _ _ _ | Sequence _ _ | Plus _ _ _
    | Equal _ _ _ | New _ _ _ _ _ | Read _ _ _ _ | Write _ _ _ _ _
    | CompareExchange _ _ _ _ _ _ _ | Spawn _ _ | Unroll _ _ _ -> ()

let rec invert_fill (#a #b:ty) (k:context a b) (e:expr [] a)
  (#next:expr [] b) (#h #h':M.heap) (#spawned:list thread)
  (s:step (fill k e) h next h' spawned)
  : Lemma
      (requires to_val e == None)
      (ensures exists (e':expr [] a).
        next == fill k e' /\ (exists (_:step e h e' h' spawned). True))
      (decreases k)
  = let ContextStep #_ #_ actual #head #_ #head' #_ #_ hs = s in
    head_not_value hs;
    match k with
    | Hole ->
        introduce exists (e':expr [] a).
          next == fill k e' /\ (exists (_:step e h e' h' spawned). True)
        with next and (
          introduce exists (_:step e h next h' spawned). True with s and ())
    | LetCtx inner _ ->
        fill_not_value inner e;
        (match actual with
         | Hole -> head_is_redex hs
         | LetCtx actual_inner _ -> invert_fill inner e (ContextStep actual_inner hs)
         | _ -> ())
    | IfCtx inner _ _ ->
        fill_not_value inner e;
        (match actual with
         | Hole -> head_is_redex hs
         | IfCtx actual_inner _ _ -> invert_fill inner e (ContextStep actual_inner hs)
         | _ -> ())
    | SeqCtx inner _ ->
        fill_not_value inner e;
        (match actual with
         | Hole -> head_is_redex hs
         | SeqCtx actual_inner _ -> invert_fill inner e (ContextStep actual_inner hs)
         | _ -> ())
    | AddLeft inner _ ->
        fill_not_value inner e;
        (match actual with
         | Hole -> head_is_redex hs
         | AddLeft actual_inner _ -> invert_fill inner e (ContextStep actual_inner hs)
         | _ -> ())
    | AddRight _ inner ->
        fill_not_value inner e;
        (match actual with
         | Hole -> head_is_redex hs
         | AddRight _ actual_inner -> invert_fill inner e (ContextStep actual_inner hs)
         | AddLeft actual_inner _ -> fill_not_value actual_inner head
         | _ -> ())
    | EqLeft inner _ ->
        fill_not_value inner e;
        (match actual with
         | Hole -> head_is_redex hs
         | EqLeft actual_inner _ -> invert_fill inner e (ContextStep actual_inner hs)
         | _ -> ())
    | EqRight _ inner ->
        fill_not_value inner e;
        (match actual with
         | Hole -> head_is_redex hs
         | EqRight _ actual_inner -> invert_fill inner e (ContextStep actual_inner hs)
         | EqLeft actual_inner _ -> fill_not_value actual_inner head
         | _ -> ())
    | AllocCtx inner ->
        fill_not_value inner e;
        (match actual with
         | Hole -> head_is_redex hs
         | AllocCtx actual_inner -> invert_fill inner e (ContextStep actual_inner hs)
         | _ -> ())
    | LoadCtx inner ->
        fill_not_value inner e;
        (match actual with
         | Hole -> head_is_redex hs
         | LoadCtx actual_inner -> invert_fill inner e (ContextStep actual_inner hs)
         | _ -> ())
    | StoreLeft inner _ ->
        fill_not_value inner e;
        (match actual with
         | Hole -> head_is_redex hs
         | StoreLeft actual_inner _ -> invert_fill inner e (ContextStep actual_inner hs)
         | _ -> ())
    | StoreRight _ inner ->
        fill_not_value inner e;
        (match actual with
         | Hole -> head_is_redex hs
         | StoreRight _ actual_inner -> invert_fill inner e (ContextStep actual_inner hs)
         | StoreLeft actual_inner _ -> fill_not_value actual_inner head
         | _ -> ())
    | CasRef inner _ _ ->
        fill_not_value inner e;
        (match actual with
         | Hole -> head_is_redex hs
         | CasRef actual_inner _ _ -> invert_fill inner e (ContextStep actual_inner hs)
         | _ -> ())
    | CasExpected _ inner _ ->
        fill_not_value inner e;
        (match actual with
         | Hole -> head_is_redex hs
         | CasExpected _ actual_inner _ -> invert_fill inner e (ContextStep actual_inner hs)
         | CasRef actual_inner _ _ -> fill_not_value actual_inner head
         | _ -> ())
    | CasDesired _ _ inner ->
        fill_not_value inner e;
        (match actual with
         | Hole -> head_is_redex hs
         | CasDesired _ _ actual_inner -> invert_fill inner e (ContextStep actual_inner hs)
         | CasRef actual_inner _ _ -> fill_not_value actual_inner head
         | CasExpected _ actual_inner _ -> fill_not_value actual_inner head
         | _ -> ())

let transition (#t:ty) (e next:expr [] t) (spawned:list thread) (h:M.heap) : prop =
  (exists (_:step e h next h spawned). True) /\
  (forall (next':expr [] t) (h':M.heap) (spawned':list thread).
    (exists (_:step e h next' h' spawned'). True) ==>
    next' == next /\ h' == h /\ spawned' == spawned)

let head_transition (#t:ty) (#e #next:expr [] t) (#h:M.heap) (#spawned:list thread)
  (hs:head_step e h next h spawned)
  (unique: (next':expr [] t -> h':M.heap -> spawned':list thread ->
    head_step e h next' h' spawned' ->
    Lemma (next' == next /\ h' == h /\ spawned' == spawned)))
  : Lemma (requires head_redex e) (ensures transition e next spawned h)
  = introduce exists (_:step e h next h spawned). True
    with (ContextStep Hole hs) and ();
    introduce forall (next':expr [] t) (h':M.heap) (spawned':list thread).
      (exists (_:step e h next' h' spawned'). True) ==>
      next' == next /\ h' == h /\ spawned' == spawned
    with (
      introduce (exists (_:step e h next' h' spawned'). True) ==>
        next' == next /\ h' == h /\ spawned' == spawned
      with (
        eliminate exists (s:step e h next' h' spawned'). True with (
          invert_head s;
          eliminate exists (hs':head_step e h next' h' spawned'). True
          with unique next' h' spawned' hs'
        )
      )
    )

let read_transition (r:H.core_ref) (v:int) (h:M.heap)
  : Lemma (requires M.contents h r v)
          (ensures transition (Load (Val r)) (Val v) [] h)
  = head_transition (Read r v h ()) (fun _ _ _ hs ->
      let Read _ actual _ _ = hs in M.contents_unique h r v actual)

let beta_transition (#a #b:ty) (v:value a) (body:expr [a] b) (h:M.heap)
  : Lemma (transition (Let (Val v) body) (substitute v body) [] h)
  = head_transition (Beta v body h) (fun _ _ _ hs -> let Beta _ _ _ = hs in ())

let sequence_transition (#t:ty) (rest:expr [] t) (h:M.heap)
  : Lemma (transition (Seq (Val ()) rest) rest [] h)
  = head_transition (Sequence rest h) (fun _ _ _ hs -> let Sequence _ _ = hs in ())

let add_transition (x y:int) (h:M.heap)
  : Lemma (transition (Add (Val x) (Val y)) (Val (x + y)) [] h)
  = head_transition (Plus x y h) (fun _ _ _ hs -> let Plus _ _ _ = hs in ())

let fork_transition (child:thread) (h:M.heap)
  : Lemma (transition (Fork child) (Val ()) [child] h)
  = head_transition (Spawn child h) (fun _ _ _ hs -> let Spawn _ _ = hs in ())

let eq_transition (x y:int) (h:M.heap)
  : Lemma (transition (Eq (Val x) (Val y)) (Val (x = y)) [] h)
  = head_transition (Equal x y h) (fun _ _ _ hs -> let Equal _ _ _ = hs in ())

let if_transition (#t:ty) (b:bool) (yes no:expr [] t) (h:M.heap)
  : Lemma (transition (If (Val b) yes no) (if b then yes else no) [] h)
  = head_transition (Branch b yes no h) (fun _ _ _ hs -> let Branch _ _ _ _ = hs in ())

let let_transition (#a #b:ty) (bound next:expr [] a) (body:expr [a] b)
  (spawned:list thread) (h:M.heap)
  : Lemma
      (requires to_val bound == None /\ transition bound next spawned h)
      (ensures transition (Let bound body) (Let next body) spawned h)
  = eliminate exists (s:step bound h next h spawned). True with (
      let ContextStep #_ #_ k #_ #_ #_ #_ #_ hs = s in
      introduce exists (_:step (Let bound body) h (Let next body) h spawned). True
      with (ContextStep (LetCtx k body) hs) and ()
    );
    introduce forall (next':expr [] b) (h':M.heap) (spawned':list thread).
      (exists (_:step (Let bound body) h next' h' spawned'). True) ==>
      next' == Let next body /\ h' == h /\ spawned' == spawned
    with (
      introduce (exists (_:step (Let bound body) h next' h' spawned'). True) ==>
        next' == Let next body /\ h' == h /\ spawned' == spawned
      with (
        eliminate exists (s:step (Let bound body) h next' h' spawned'). True
        with invert_let bound body s
      )
    )

let seq_transition (#t:ty) (first next:thread) (rest:expr [] t)
  (spawned:list thread) (h:M.heap)
  : Lemma
      (requires to_val first == None /\ transition first next spawned h)
      (ensures transition (Seq first rest) (Seq next rest) spawned h)
  = eliminate exists (s:step first h next h spawned). True with (
      let ContextStep #_ #_ k #_ #_ #_ #_ #_ hs = s in
      introduce exists (_:step (Seq first rest) h (Seq next rest) h spawned). True
      with (ContextStep (SeqCtx k rest) hs) and ()
    );
    introduce forall (next':expr [] t) (h':M.heap) (spawned':list thread).
      (exists (_:step (Seq first rest) h next' h' spawned'). True) ==>
      next' == Seq next rest /\ h' == h /\ spawned' == spawned
    with (
      introduce (exists (_:step (Seq first rest) h next' h' spawned'). True) ==>
        next' == Seq next rest /\ h' == h /\ spawned' == spawned
      with (
        eliminate exists (s:step (Seq first rest) h next' h' spawned'). True
        with invert_seq first rest s
      )
    )

noeq
type packed_expr =
  | Pack: t:ty -> expr [] t -> packed_expr

noeq
type packed_value =
  | PackValue: t:ty -> value t -> packed_value

let packed_to_val (e:packed_expr) : option packed_value =
  let Pack t e = e in
  match to_val e with
  | None -> None
  | Some v -> Some (PackValue t v)

let pack_threads (es:list thread) : list packed_expr =
  FStar.List.Tot.map (Pack TUnit) es

let packed_step (e:packed_expr) (h:M.heap) (e':packed_expr) (h':M.heap)
  (spawned:list packed_expr) : prop =
  let Pack t e = e in
  exists (next:expr [] t) (children:list thread).
    e' == Pack t next /\ spawned == pack_threads children /\
    (exists (_:step e h next h' children). True)

let pack_step
  (#t:ty) (#e #e':expr [] t) (#h #h':M.heap) (#spawned:list thread)
  (s:step e h e' h' spawned)
  : Lemma (packed_step (Pack t e) h (Pack t e') h' (pack_threads spawned))
  = introduce exists (next:expr [] t) (children:list thread).
      Pack t e' == Pack t next /\ pack_threads spawned == pack_threads children /\
      (exists (_:step e h next h' children). True)
    with e' spawned and (
      introduce exists (_:step e h e' h' spawned). True with s and ()
    )

let language : L.language = {
  expr = packed_expr;
  value = packed_value;
  state = M.heap;
  to_val = packed_to_val;
  prim_step = packed_step;
  values_stuck = (
    introduce forall e h e' h' spawned.
      Some? (packed_to_val e) ==> ~ (packed_step e h e' h' spawned)
    with (
      let Pack t e = e in
      introduce Some? (packed_to_val (Pack t e)) ==>
        not (packed_step (Pack t e) h e' h' spawned) with (
        introduce (packed_step (Pack t e) h e' h' spawned) ==> False with (
          eliminate exists (next:expr [] t) (children:list thread).
            e' == Pack t next /\ spawned == pack_threads children /\
            (exists (_:step e h next h' children). True)
          with (
            eliminate exists (s:step e h next h' children). True
            with step_not_value s
          )
        )
      )
    )
  );
}

let pack_transition (#t:ty) (e next:expr [] t) (spawned:list thread) (h:M.heap)
  : Lemma
      (requires transition e next spawned h)
      (ensures L.reducible language (Pack t e) h /\
        (forall e' h' spawned'.
          packed_step (Pack t e) h e' h' spawned' ==>
          e' == Pack t next /\ h' == h /\ spawned' == pack_threads spawned))
  = eliminate exists (s:step e h next h spawned). True with (
      pack_step s;
      introduce exists e' h' children. language.L.prim_step (Pack t e) h e' h' children
      with (Pack t next) h (pack_threads spawned) and ()
    );
    introduce forall e' h' spawned'.
      packed_step (Pack t e) h e' h' spawned' ==>
      e' == Pack t next /\ h' == h /\ spawned' == pack_threads spawned
    with (
      introduce packed_step (Pack t e) h e' h' spawned' ==>
        e' == Pack t next /\ h' == h /\ spawned' == pack_threads spawned
      with (
        eliminate exists (next':expr [] t) (children:list thread).
          e' == Pack t next' /\ spawned' == pack_threads children /\
          (exists (_:step e h next' h' children). True)
        with ()
      )
    )

let atomic_result (#t:ty) (e:expr [] t) (h:M.heap) (v:value t) (h':M.heap) : prop =
  L.reducible language (Pack t e) h /\
  (forall next state spawned.
    packed_step (Pack t e) h next state spawned ==>
    packed_to_val next == Some (PackValue t v) /\ state == h' /\ spawned == [])

let head_atomic (#t:ty) (#e:expr [] t) (#h #h':M.heap) (#v:value t)
  (hs:head_step e h (Val v) h' [])
  (unique: (next:expr [] t -> state:M.heap -> spawned:list thread ->
    head_step e h next state spawned ->
    Lemma (next == Val v /\ state == h' /\ spawned == [])))
  : Lemma (requires head_redex e) (ensures atomic_result e h v h')
  = pack_step (ContextStep Hole hs);
    introduce exists next state spawned. language.L.prim_step (Pack t e) h next state spawned
    with (Pack t (Val v)) h' [] and ();
    introduce forall next state spawned.
      packed_step (Pack t e) h next state spawned ==>
      packed_to_val next == Some (PackValue t v) /\ state == h' /\ spawned == []
    with (
      introduce packed_step (Pack t e) h next state spawned ==>
        packed_to_val next == Some (PackValue t v) /\ state == h' /\ spawned == []
      with (
        eliminate exists (e':expr [] t) (children:list thread).
          next == Pack t e' /\ spawned == pack_threads children /\
          (exists (_:step e h e' state children). True)
        with (
          eliminate exists (s:step e h e' state children). True with (
            invert_head s;
            eliminate exists (hs':head_step e h e' state children). True
            with unique e' state children hs'
          )
        )
      )
    )

let store_atomic (r:H.core_ref) (v:int) (h h':M.heap)
  : Lemma (requires M.store h r v h')
          (ensures atomic_result (Store (Val r) (Val v)) h () h')
  = head_atomic (Write r v h h' ()) (fun _ state _ hs ->
      let Write _ _ _ _ _ = hs in M.store_unique h r v h' state)

let schedule
  (#t:ty) (#e #e':expr [] t) (#h #h':M.heap) (#spawned:list thread)
  (before after:list packed_expr)
  (s:step e h e' h' spawned)
  : L.pool_step language
      { L.threads = FStar.List.Tot.append before (Pack t e :: after); L.state = h }
      { L.threads = FStar.List.Tot.append before
          (Pack t e' :: FStar.List.Tot.append after (pack_threads spawned)); L.state = h' }
  = pack_step s;
    L.Schedule before (Pack t e) after h (Pack t e') h' (pack_threads spawned) ()
