(*
   Copyright 2024 Microsoft Research

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

module Pulse.Lib.Task
#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.SpinLock
open FStar.Tactics
open FStar.Preorder
open Pulse.Lib.Pledge
open Pulse.Lib.Trade
open Pulse.Class.Duplicable

open Pulse.Lib.SpinLock

module RTC   = FStar.ReflexiveTransitiveClosure
module FRAP  = Pulse.Lib.FractionalAnchoredPreorder
module AR    = Pulse.Lib.AnchoredReference
module Big   = Pulse.Lib.BigReference
module Ghost = Pulse.Lib.GhostReference

noeq
type task_state : Type0 =
  | Ready    : task_state
  | Running  : task_state
  | Done     : task_state
  | Claimed  : task_state

let unclaimed (s : task_state) : task_state =
  match s with
  | Claimed -> Done
  | x -> x

let v (s : task_state) : int =
  match s with
  | Ready -> 0
  | Running -> 1
  | Done -> 2
  | Claimed -> 3
  
let p_st : preorder task_state = fun x y -> b2t (v x <= v y)

let anchor_rel : FRAP.anchor_rel p_st =
  fun (x y : task_state) ->
    match x, y with
    | Ready, Claimed -> False
    | x, y -> squash (p_st x y)

let anchor_rel_refl (x:task_state) :
  Lemma (anchor_rel x x) [SMTPat (anchor_rel x x)]
  =
  assert_norm (anchor_rel Ready Ready);
  assert_norm (anchor_rel Running Running);
  assert_norm (anchor_rel Done Done);
  assert_norm (anchor_rel Claimed Claimed)

let state_res
  (pre : slprop)
  (post : slprop)
  (g_state : AR.ref task_state p_st anchor_rel)
  (st : task_state)
=
  match st with
  | Ready -> pre
  | Running -> emp
  | Done -> post
  | Claimed -> AR.anchored g_state Claimed

noeq
type handle : Type0 = {
  state   : ref task_state;
  g_state : AR.ref task_state p_st anchor_rel; (* these two refs are kept in sync *)
}

let up (x: slprop_ref) : slprop =
  exists* v. slprop_ref_pts_to x v ** v

noeq
type task_t : Type0 = {
  pre :  slprop_ref;
  post : slprop_ref;

  h : handle;

  // thunk : unit -> stt unit pre (fun _ -> up post);
  thunk : Dyn.dyn;
}

let state_pred
  (pre : slprop_ref)
  (post : slprop_ref)
  (h : handle)
: slprop =
  exists* (v_state : task_state).
    pts_to
      h.state
      #(if Running? v_state then 0.5R else 1.0R)
      (unclaimed v_state)
      **
    AR.pts_to h.g_state v_state **
    state_res (up pre) (up post) h.g_state v_state

let task_type (pre post : slprop) : Type0 =
  unit -> stt unit pre (fun _ -> post)

let task_thunk_typing_core (t : task_t) (pre post: slprop) : slprop =
  slprop_ref_pts_to t.pre pre **
  slprop_ref_pts_to t.post post **
  pure (Dyn.dyn_has_ty t.thunk (task_type pre post))

let task_thunk_typing (t : task_t) : slprop =
  exists* pre post. task_thunk_typing_core t pre post

ghost fn task_thunk_typing_dup t
  requires task_thunk_typing t
  ensures task_thunk_typing t ** task_thunk_typing t
{
  unfold task_thunk_typing t;
  with pre post. assert task_thunk_typing_core t pre post;
  unfold task_thunk_typing_core t pre post;
  slprop_ref_share t.pre;
  slprop_ref_share t.post;
  fold task_thunk_typing_core t pre post;
  fold task_thunk_typing_core t pre post;
  fold task_thunk_typing t;
  fold task_thunk_typing t;
}
instance task_thunk_typing_duplicable t : duplicable (task_thunk_typing t) =
  { dup_f = fun _ -> task_thunk_typing_dup t }

let rec all_state_pred
  ( v_runnable : list task_t)
: slprop
= match v_runnable with
  | [] -> emp
  | t :: ts ->
    task_thunk_typing t **
    state_pred t.pre t.post t.h **
    all_state_pred ts

ghost
fn add_one_state_pred
  (t : task_t)
  (v_runnable : list task_t)
  requires task_thunk_typing t
        ** state_pred t.pre t.post t.h
        ** all_state_pred v_runnable
  ensures  all_state_pred (t :: v_runnable)
{
  fold (all_state_pred (t :: v_runnable));
}

ghost
fn take_one_h11
  (t : task_t)
  (v_runnable : list task_t)
  requires all_state_pred (t :: v_runnable)
  ensures task_thunk_typing t
        ** state_pred t.pre t.post t.h
        ** all_state_pred v_runnable
{
  unfold (all_state_pred (t :: v_runnable));
}

(** List preorder and anchor relation. Used for the runnable lists
which are monotonically increasing. **)
let list_extension #a (t0 t1 : list a)
  : prop
  = Cons? t1 /\ t0 == List.Tot.tail t1

let list_preorder #a
  : FStar.Preorder.preorder (list a)
  = FStar.ReflexiveTransitiveClosure.closure list_extension

let list_anchor : FRAP.anchor_rel list_preorder = fun x y -> list_preorder x y /\ True
let list_anchor_refl (x:list task_t)
: Lemma (list_anchor x x)
        [SMTPat (list_anchor x x)]
= assert (list_anchor x x)
    by (T.norm [delta_only [`%list_anchor]; simplify])
let list_preorder_mono_memP (#a:Type) (x:a) (l1 l2:list a)
: Lemma
  (requires List.memP x l1 /\ list_preorder l1 l2)
  (ensures List.memP x l2)
  [SMTPat (list_preorder l1 l2); SMTPat (List.memP x l1)]
= RTC.induct
    list_extension
    (fun l1 l2 -> List.memP x l1 ==> List.memP x l2)
    (fun _ -> ()) (fun _ _ -> ()) (fun _ _ _ -> ())
    l1 l2 ()

let lock_inv
  (runnable   : ref (list task_t))
  (g_runnable : AR.ref (list task_t) list_preorder list_anchor)
: slprop
= 
  exists*
    (v_runnable : list task_t)
  .
    pts_to runnable v_runnable **
    AR.pts_to_full g_runnable v_runnable **
    all_state_pred v_runnable

noeq
type pool_st : Type u#0 = {
  runnable   : ref (list task_t);
  g_runnable : AR.ref (list task_t) list_preorder list_anchor;
  
  lk : lock; // (lock_inv runnable g_runnable);
}

type pool : Type0 = pool_st

let pool_alive (#[exact (`1.0R)] f : perm) (p:pool) : slprop =
  lock_alive p.lk #(f /. 2.0R) (lock_inv p.runnable p.g_runnable)

let state_res' (post : slprop) ( st : task_state) =
  match st with
  | Done -> post
  | Claimed -> emp
  | _ -> pure False

let task_spotted
  (p : pool)
  (t : task_t)
: slprop =
  exists* v_runnable.
    AR.snapshot p.g_runnable v_runnable **
    pure (List.memP t v_runnable)

let gtrade_ty a b extra : Type u#4 =
  unit -> stt_ghost unit [] (extra ** a) (fun _ -> b)
let gtrade_fun a b extra {| duplicable extra |} (f: gtrade_ty a b extra) =
  emp
let gtrade (a b: slprop) : slprop =
  exists* (extra: slprop) (h: duplicable extra) f.
    extra ** gtrade_fun a b extra f

ghost fn gtrade_intro (a b extra: slprop) {| h: duplicable extra |}
    (f: unit -> stt_ghost unit [] (extra ** a) (fun _ -> b))
  requires extra
  ensures gtrade a b
{
  fold gtrade_fun a b extra #h f;
  fold gtrade a b;
}

ghost fn gtrade_dup (a b: slprop)
  requires gtrade a b
  ensures gtrade a b ** gtrade a b
{
  unfold gtrade a b;
  with extra h f. assert gtrade_fun a b extra #h f;
  fold gtrade_fun a b extra #h f;
  dup extra #h ();
  fold gtrade a b;
  fold gtrade a b;
}

instance gtrade_duplicable a b : duplicable (gtrade a b) = { dup_f = fun _ -> gtrade_dup a b }

ghost fn gtrade_elim (a b: slprop)
  requires a ** gtrade a b
  ensures b
{
  unfold gtrade a b;
  with extra h f. assert gtrade_fun a b extra #h f;
  unfold gtrade_fun a b extra #h f;
  let f: gtrade_ty a b extra = f;
  f ();
}

let handle_spotted
  (p : pool)
  (post : slprop)
  (h : handle)
  : slprop =
    exists* (t : task_t).
      task_spotted p t **
      gtrade (up t.post ** later_credit 1) post **
      pure (t.h == h)

ghost
fn intro_task_spotted
    (p : pool)
    (t : task_t)
    (ts : list task_t)
  requires AR.snapshot p.g_runnable ts
        ** pure (List.memP t ts)
  ensures  task_spotted p t
{
  fold (task_spotted p t);
}

ghost
fn intro_handle_spotted
    (p : pool)
    (post: slprop)
    (t : task_t)
    (ts : list task_t)
  requires AR.snapshot p.g_runnable ts
        ** gtrade (up t.post ** later_credit 1) post
        ** pure (List.memP t ts)
  ensures  handle_spotted p post t.h
{
  intro_task_spotted p t ts;
  fold (handle_spotted p post t.h);
}

ghost
fn recall_task_spotted
  (p : pool) (t : task_t) (#ts : list task_t)
  (#f:perm)
  requires AR.pts_to p.g_runnable #f ts ** task_spotted p t
  ensures  AR.pts_to p.g_runnable #f ts ** task_spotted p t
           ** pure (List.memP t ts)
{
  unfold (task_spotted p t);
  AR.recall_snapshot p.g_runnable;
  fold (task_spotted p t);
}

ghost
fn recall_handle_spotted
  (p : pool) (post : slprop) (h : handle) (#ts : list task_t)
  (#f:perm)
  requires AR.pts_to p.g_runnable #f ts ** handle_spotted p post h
  returns  task : erased task_t
  ensures AR.pts_to p.g_runnable #f ts ** handle_spotted p post h **
          gtrade (up task.post ** later_credit 1) post **
          pure (task.h == h /\ List.memP (reveal task) ts)
{
  unfold (handle_spotted p post h);
  with t. assert (task_spotted p t);
  recall_task_spotted p t #ts;
  dup (gtrade (up t.post ** later_credit 1) post) ();
  fold (handle_spotted p post h);
  hide t
}

module SEM = FStar.StrongExcludedMiddle

ghost
fn rec extract_state_pred
  (p : pool) (t : task_t)
  (#ts : list task_t)
  requires all_state_pred ts ** pure (List.memP t ts)
  ensures (state_pred t.pre t.post t.h)
       ** trade (state_pred t.pre t.post t.h) (all_state_pred ts) // trade to put things back together
  decreases ts
{
  match ts {
    [] -> {
      unreachable ()
    }
    t' :: ts' -> {
      let b = SEM.strong_excluded_middle (t == t');
      if not b {
        take_one_h11 t' ts';
        extract_state_pred p t #ts';

        ghost
        fn aux ()
          requires (task_thunk_typing t' ** state_pred t'.pre t'.post t'.h) **
                   all_state_pred ts'
          ensures  all_state_pred ts
        {
          add_one_state_pred t' ts';
        };
        intro_trade (all_state_pred ts') (all_state_pred ts)
                    (task_thunk_typing t' ** state_pred t'.pre t'.post t'.h) aux;

        trade_compose (state_pred t.pre t.post t.h) (all_state_pred ts') (all_state_pred ts);
      } else {
        rewrite each t' as t;
        take_one_h11 t ts';

        ghost
        fn aux (_:unit)
          requires (pure (ts == t'::ts') ** task_thunk_typing t' ** all_state_pred ts')
                ** state_pred t'.pre t'.post t'.h
          ensures all_state_pred ts
        {
          add_one_state_pred t' ts';
        };
        intro_trade (state_pred t.pre t.post t.h) (all_state_pred ts)
                    (pure (ts == t'::ts') ** task_thunk_typing t' ** all_state_pred ts') aux;

        ()
      }
    }
  }
}

let joinable
  (p : pool)
  (post:slprop)
  (h : handle)
: slprop =
  AR.anchored h.g_state Ready **
  handle_spotted p post h **
  later_credit 1

ghost
fn intro_state_pred
  (pre post : slprop_ref)
  (h : handle)
  (v_state : task_state {~(Running? v_state)})
  requires
    pts_to h.state (unclaimed v_state) **
    AR.pts_to h.g_state v_state **
    state_res (up pre) (up post) h.g_state v_state
  ensures state_pred pre post h
{
  fold (state_pred pre post h);
}

ghost
fn intro_state_pred_Running
  (pre post : slprop_ref)
  (h : handle)
  requires
    pts_to h.state #0.5R Running **
    AR.pts_to h.g_state Running **
    state_res (up pre) (up post) h.g_state Running
  ensures state_pred pre post h
{
  rewrite (pts_to h.state #0.5R Running)
       as (pts_to h.state #0.5R (unclaimed Running));
  fold (state_pred pre post h);
}

ghost
fn elim_state_pred
  (pre post : slprop_ref)
  (h : handle)
  requires state_pred pre post h
  returns v_state : erased (task_state)
  ensures
    pts_to h.state #(if Running? v_state then 0.5R else 1.0R) (unclaimed v_state) **
    AR.pts_to h.g_state v_state **
    state_res (up pre) (up post) h.g_state v_state
{
  unfold (state_pred pre post h);
  with v_state. assert (state_res (up pre) (up post) h.g_state v_state);
  hide v_state
}

instance duplicable_slprop_ref_pts_to x y : duplicable (slprop_ref_pts_to x y) = {
  dup_f = (fun _ -> slprop_ref_share x #y)
}

ghost fn gtrade_up (x: slprop_ref) (y: slprop)
  requires slprop_ref_pts_to x y
  ensures gtrade (up x ** later_credit 1) y
{
  ghost fn aux ()
    requires slprop_ref_pts_to x y ** (up x ** later_credit 1)
    ensures y
  {
    unfold up x;
    slprop_ref_gather _;
    later_elim _;
    equiv_comm _ _;
    equiv_elim _ _;
    drop_ (slprop_ref_pts_to _ _);
  };
  gtrade_intro _ _ _ aux;
}

instance non_informative_slprop_ref : Pulse.Lib.NonInformative.non_informative slprop_ref =
  { reveal = (fun (x: erased slprop_ref) -> reveal x) }

fn spawn (p:pool)
    (#pf:perm)
    (#pre : slprop)
    (#post : slprop)
    (f : unit -> stt unit (pre) (fun _ -> post))
    requires pool_alive #pf p ** pre
    returns  h : handle
    ensures  pool_alive #pf p ** joinable p post h
{
  let task_st : task_state = Ready;
  assert (pure (anchor_rel Ready Ready));
  let r_task_st : ref task_state = alloc task_st;
  let gr_task_st : AR.ref task_state p_st anchor_rel = AR.alloc #task_state task_st #p_st #anchor_rel;

  AR.drop_anchor gr_task_st;

  let handle : handle = {
    state = r_task_st;
    g_state = gr_task_st;
  };
  let pre_ref = slprop_ref_alloc pre;
  let post_ref = slprop_ref_alloc post;
  let task : task_t = {
    h = handle;
    pre = pre_ref;
    post = post_ref;
    thunk = Dyn.mkdyn f;
  };
  dup (slprop_ref_pts_to post_ref post) ();
  dup (slprop_ref_pts_to pre_ref pre) ();
  fold task_thunk_typing_core task pre post;
  fold task_thunk_typing task;
  
  (* Probably the fragment above this line can be factored out. *)

  unfold (pool_alive #pf p);
  
  acquire p.lk;
  unfold (lock_inv p.runnable p.g_runnable);
  
  let v_runnable = !p.runnable;

  p.runnable := (task :: v_runnable);
  AR.write_full p.g_runnable (task :: v_runnable);

  rewrite each task_st as Ready;
  rewrite each gr_task_st as task.h.g_state;
  assert (AR.anchored task.h.g_state Ready);

  AR.take_snapshot_full p.g_runnable;

  gtrade_up task.post post;
  assert (pure (List.memP task (task :: v_runnable)));
  // intro_task_spotted p task (task :: v_runnable);
  intro_handle_spotted p post task (task :: v_runnable);

  later_credit_buy 1;
  fold (joinable p post task.h);

  assert (pts_to r_task_st Ready);

  rewrite each r_task_st as handle.state;
  fold up task.pre;
  rewrite (up task.pre)
       as (state_res (up task.pre) (up task.post) gr_task_st Ready);
  rewrite each gr_task_st as handle.g_state;
  rewrite each handle as task.h;
  rewrite each pre_ref as task.pre;
  rewrite each post_ref as task.post;
   
  intro_state_pred task.pre task.post task.h Ready;
  // fold (state_pred #code task.pre task.post task.h);

  add_one_state_pred task v_runnable;

  fold (lock_inv p.runnable p.g_runnable);

  release p.lk;
  fold (pool_alive #pf p);
  
  task.h;
}

ghost
fn claim_done_task
         (#p:pool)
         (#pre : slprop) (#post : slprop)
         (h : handle)
  requires state_res pre post h.g_state Done    ** AR.pts_to h.g_state Done    ** AR.anchored h.g_state Ready
  ensures  state_res pre post h.g_state Claimed ** AR.pts_to h.g_state Claimed ** post
{
  rewrite (state_res pre post h.g_state Done)
       as post;

  AR.lift_anchor h.g_state Ready;

  AR.write_full h.g_state Claimed;

  AR.drop_anchor h.g_state;

  fold (state_res pre post h.g_state Claimed);

  ()
}

fn try_await
         (#p:pool)
         (#post : slprop)
         (h : handle)
         (#f:perm)
  requires pool_alive #f p ** joinable p post h
  returns  ok : bool
  ensures  pool_alive #f p ** (if ok then post else joinable p post h)
{
  unfold (pool_alive #f p);
  acquire p.lk;
  unfold (lock_inv p.runnable p.g_runnable);
  
  unfold (joinable p post h);

  with v_runnable. assert (pts_to p.runnable v_runnable);

  unfold (handle_spotted p post h);

  with t. assert (task_spotted p t);
  AR.drop_anchor p.g_runnable;
  recall_task_spotted p t #v_runnable;
  AR.lift_anchor p.g_runnable _;
  
  extract_state_pred p t #v_runnable;

  let v_state = elim_state_pred t.pre t.post t.h;

  rewrite (pts_to t.h.state #(if Running? v_state then 0.5R else 1.0R) (unclaimed (reveal v_state)))
       as (pts_to h.state #(if Running? v_state then 0.5R else 1.0R) (unclaimed (reveal v_state)));
  let task_st = !h.state;
  
  match task_st {
    Ready -> {
      (* NOOP *)
      rewrite (pts_to h.state (reveal v_state))
           as (pts_to t.h.state (reveal v_state));
      intro_state_pred t.pre t.post t.h Ready;
      elim_trade _ _; // undo extract_state_pred
      fold (lock_inv p.runnable p.g_runnable);
      release p.lk;
      fold (pool_alive #f p);
      fold (handle_spotted p post h);
      fold (joinable p post h);
      false;
    }
    Running -> {
      (* NOOP *)
      rewrite (pts_to h.state #0.5R (reveal v_state))
           as (pts_to t.h.state #0.5R (reveal v_state));
      intro_state_pred_Running t.pre t.post t.h;
      elim_trade _ _; // undo extract_state_pred
      fold (lock_inv p.runnable p.g_runnable);
      release p.lk;
      fold (pool_alive #f p);
      fold (handle_spotted p post h);
      fold (joinable p post h);
      false;
    }
    Done -> {
      (* First prove that ghost state cannot be Claimed,
      due to the anchor *)
      rewrite (AR.pts_to t.h.g_state v_state)
           as (AR.pts_to h.g_state v_state);
      assert (AR.pts_to h.g_state v_state);
      assert (AR.anchored h.g_state Ready);
      AR.recall_anchor h.g_state Ready;
      assert (pure (v_state =!= Claimed));
      assert (pure (v_state == Done));
      rewrite (AR.pts_to h.g_state v_state)
           as (AR.pts_to t.h.g_state v_state);

      (* Now claim it *)
      claim_done_task #p #(up t.pre) #(up t.post) t.h;

      gtrade_elim (up t.post ** later_credit 1) post;
      rewrite (post)
           as (if true then post else joinable p post h);
           
      rewrite (pts_to h.state Done)
           as (pts_to t.h.state (unclaimed Claimed));
      intro_state_pred t.pre t.post t.h Claimed;
      elim_trade _ _; // undo extract_state_pred
      fold (lock_inv p.runnable p.g_runnable);
      release p.lk;
      fold (pool_alive #f p);
      drop_ (task_spotted p t);
      true
    }
    Claimed -> {
      (* Concrete state is never Claimed *)
      unreachable ();
    }
  }
}

let handle_done (h:handle) : slprop =
  exists* (st : task_state).
    pure (st == Done \/ st == Claimed) **
    AR.snapshot h.g_state st

let task_done (t : task_t)  : slprop =
  handle_done t.h

let rec all_tasks_done (ts : list task_t) =
  match ts with
  | [] -> emp
  | t::ts' ->
    task_done t **
    all_tasks_done ts'

let slprop_equiv_refl (v1 v2 : slprop) (_ : squash (v1 == v2)) 
  : slprop_equiv v1 v2 = slprop_equiv_refl _

let helper_tac () : Tac unit =
  apply (`slprop_equiv_refl);
  trefl()

// FIXME: refactor this to provide task_done instead
ghost
fn unfold_all_tasks_done_cons (t : task_t) (ts : list task_t)
  requires all_tasks_done (t :: ts)
  returns  st : task_state
  ensures  pure (st == Done \/ st == Claimed) **
           AR.snapshot t.h.g_state st **
           all_tasks_done ts
{
  // This should not be so hard.
  rewrite
    (all_tasks_done (t :: ts))
  as
    ((exists* (st : task_state).
      pure (st == Done \/ st == Claimed) **
      AR.snapshot t.h.g_state st) **
      all_tasks_done ts)
  by (helper_tac ());
  with st. assert AR.snapshot t.h.g_state st;
  st
}

ghost
fn fold_all_tasks_done_cons (t : task_t) (ts : list task_t)
  (st : task_state)
  requires pure (st == Done \/ st == Claimed) **
           AR.snapshot t.h.g_state st **
           all_tasks_done ts
  ensures  all_tasks_done (t :: ts)
{
  // This should not be so hard.
  rewrite
    ((exists* (st : task_state).
      pure (st == Done \/ st == Claimed) **
      AR.snapshot t.h.g_state st) **
      all_tasks_done ts)
  as
    (all_tasks_done (t :: ts))
  by (helper_tac())
}

instance dup_snapshot
  (#t:Type u#0)
  (#pre : preorder t)
  (#anc : FRAP.anchor_rel pre)
  (r : AR.ref t pre anc)
  (v : t)
: duplicable (AR.snapshot r v) = {
  // TODO: implement in AR module, or tweak
  // take_snapshot to provide a snapshot of a possibly
  // "older" value. In that case this is easy to implement.
  dup_f = (fun _ -> AR.dup_snapshot r);
}

ghost
fn rec all_tasks_done_inst (t : task_t) (ts : list task_t)
  requires all_tasks_done ts ** pure (List.memP t ts)
  ensures  all_tasks_done ts ** task_done t
  decreases ts
{
  match ts {
    [] -> {
      unreachable();
    }
    t' :: ts' -> {
      let b = SEM.strong_excluded_middle (t == t');
      if b {
        rewrite each t' as t;
        let st = unfold_all_tasks_done_cons t ts';
        dup (AR.snapshot t.h.g_state st) ();
        fold (handle_done t.h);
        fold (task_done t);
        fold_all_tasks_done_cons t ts' st;
      } else {
        let st = unfold_all_tasks_done_cons t' ts';
        all_tasks_done_inst t ts';
        fold_all_tasks_done_cons t' ts' st;
      }
    }
  } 
}

let pool_done (p : pool) : slprop =
  exists* ts. AR.pts_to p.g_runnable #0.5R ts ** all_state_pred ts ** all_tasks_done ts

ghost
fn disown_aux
  (#p:pool)
  (#post : slprop)
  (h : handle)
  requires pool_done p ** joinable p post h
  ensures  pool_done p ** post
{
  unfold (pool_done p);
  unfold (joinable p post h);
  unfold (handle_spotted p post h);

  with v_runnable. assert (AR.pts_to p.g_runnable #0.5R v_runnable);
  with t. assert (task_spotted p t);

  recall_task_spotted p t #v_runnable;
  extract_state_pred p t #v_runnable;

  unfold (state_pred t.pre t.post t.h);

  with st. assert (AR.pts_to t.h.g_state st);
  let st = reveal st;
  
  all_tasks_done_inst t v_runnable;

  match st {
    Done -> {
      rewrite (state_res (up t.pre) (up t.post) t.h.g_state Done)
           as up t.post;

      AR.lift_anchor t.h.g_state Ready;
      AR.write_full t.h.g_state Claimed;
      AR.drop_anchor t.h.g_state;

      fold (state_res (up t.pre) (up t.post) t.h.g_state Claimed);
      
      rewrite (pts_to t.h.state Done)
           as (pts_to t.h.state (unclaimed Claimed));
      
      intro_state_pred t.pre t.post t.h Claimed;

      drop_ (task_spotted p t);
      
      elim_trade _ _;
      
      drop_ (task_done t);
      
      gtrade_elim _ _;
      fold (pool_done p);
    }
    Claimed -> {
      assert (AR.anchored h.g_state Ready);
      AR.recall_anchor t.h.g_state Ready;
      unreachable();
    }
    Ready -> {
      unfold (task_done t);
      unfold (handle_done t.h);
      with st. assert (AR.snapshot t.h.g_state st);
      AR.recall_snapshot t.h.g_state;
      unreachable();
    }
    Running -> { 
      unfold (task_done t);
      unfold (handle_done t.h);
      with st. assert (AR.snapshot t.h.g_state st);
      AR.recall_snapshot t.h.g_state;
      unreachable();
    }
  }
}

ghost
fn disown (#p:pool)
      (#post : slprop)
      (h : handle)
  requires joinable p post h
  ensures  pledge [] (pool_done p) (post)
{
  inames_live_empty ();
  make_pledge [] (pool_done p) (post) (joinable p post h)
      (fun _ -> disown_aux #p #post h)
}

fn spawn_ (p:pool)
    (#pf:perm)
    (#pre : slprop)
    (#post : slprop)
    (f : unit -> stt unit (pre) (fun _ -> post))
    requires pool_alive #pf p ** pre
    ensures  pool_alive #pf p ** pledge [] (pool_done p) (post)
{
  let h = spawn p f;
  disown h
}

// Busy waiting version of await
fn await (#p:pool)
         (#post : slprop)
         (h : handle)
         (#f:perm)
  requires pool_alive #f p ** joinable p post h
  ensures  pool_alive #f p ** post
{
  let mut done = false;
  while (let v = !done; (not v))
    invariant b.
      exists* v_done.
        pool_alive #f p **
        pts_to done v_done **
        (if v_done then post else joinable p post h) **
        pure (b == not v_done)
  {
    let b = try_await #p #post h #f;
    done := b;
  };
}

ghost
fn rec pool_done_task_done_aux
      (t : task_t)
      (ts : list task_t)
  requires all_tasks_done ts ** pure (List.memP t ts)
  ensures  all_tasks_done ts ** task_done t
  decreases ts
{
  match ts {
    [] -> {
      unreachable();
    }
    t' :: ts' -> {
      let b = SEM.strong_excluded_middle (t == t');
      if b {
        rewrite each t' as t;
        let st = unfold_all_tasks_done_cons t ts';
        dup (AR.snapshot t.h.g_state st) ();
        fold (handle_done t.h);
        fold (task_done t);
        
        fold_all_tasks_done_cons t ts' st;
      } else {
        (* Must be in the tail *)
        assert (pure (List.memP t ts'));
        let st = unfold_all_tasks_done_cons t' ts';
        pool_done_task_done_aux t ts';
        fold_all_tasks_done_cons t' ts' st;
      }
    }
  }
}

ghost
fn pool_done_handle_done_aux2 (#p:pool)
      (#post : slprop)
      (h : handle)
      (ts : list task_t)
  requires AR.pts_to p.g_runnable #0.5R ts ** all_tasks_done ts ** handle_spotted p post h
  ensures  AR.pts_to p.g_runnable #0.5R ts ** all_tasks_done ts ** handle_done h
{
  let t = recall_handle_spotted p post h #ts;
  pool_done_task_done_aux t ts;
  unfold (task_done t);
  rewrite each t.h as h;
  drop_ (gtrade _ _);
  drop_ (handle_spotted p post h);
}

ghost
fn pool_done_handle_done_aux (#p:pool)
      (#post : slprop)
      (h : handle)
      (_ : unit)
  requires pool_done p ** handle_spotted p post h
  ensures  pool_done p ** handle_done h
{
  unfold (pool_done p);
  pool_done_handle_done_aux2 #p #post h _;
  fold (pool_done p);
}

ghost
fn pool_done_handle_done (#p:pool)
      (#post : slprop)
      (h : handle)
  requires handle_spotted p post h
  ensures pledge [] (pool_done p) (handle_done h)
{
  inames_live_empty();
  make_pledge [] (pool_done p) (handle_done h) (handle_spotted p post h)
    (pool_done_handle_done_aux #p #post h)
}

let vopt (#a:Type) (o : option a) (p : a -> slprop) =
  match o with
  | Some x -> p x
  | None -> emp

ghost
fn intro_vopt_none (#a:Type0) (#p : a -> slprop) ()
  requires emp
  ensures vopt None p
{
  fold (vopt None p);
}

ghost
fn intro_vopt_some (#a:Type0) (x : a) (#p : a -> slprop)
  requires p x
  ensures vopt (Some x) p
{
  fold (vopt (Some x) p);
}

ghost
fn get_vopt (#a:Type0) (#x : a) (#p : a -> slprop) ()
  requires vopt (Some x) p
  ensures p x
{
  unfold vopt (Some x) p;
}

ghost
fn weaken_vopt (#a:Type0) (o : option a)
    (#p1 #p2 : a -> slprop)
    (extra : slprop) // CAUTION: this can be dropped!
    (f : (x:a) -> stt_ghost unit [] (extra ** p1 x) (fun _ -> p2 x))
  requires extra ** vopt o p1
  ensures  vopt o p2
{
  match o {
    None -> {
      unfold (vopt None p1);
      fold (vopt None p2);
      drop_ extra;
      ()
    }
    Some v -> {
      rewrite (vopt o p1) as p1 v;
      f v;
      fold (vopt o p2);
    }
  }
}

(* Called with pool lock taken *)
fn rec grab_work'' (p:pool) (v_runnable : list task_t)
  requires all_state_pred v_runnable
  returns  topt : option task_t
  ensures  all_state_pred v_runnable
        ** vopt topt (fun t ->
             up t.pre ** pts_to t.h.state #0.5R Running ** pure (List.memP t v_runnable) ** task_thunk_typing t)
{
  match v_runnable {
    [] -> {
      // intro_vopt_none;
      // fails with variable not found...

      let topt : option task_t = None #task_t;
      rewrite emp
          as vopt topt (fun t -> up t.pre ** pts_to t.h.state #0.5R Running ** pure (List.memP t v_runnable) ** task_thunk_typing t);
      topt
    }
    t :: ts -> {
      take_one_h11 t ts;
      unfold (state_pred t.pre t.post t.h);
      
      let st = !t.h.state;
      match st {
        Ready -> {
          let topt = Some #task_t t;
          rewrite (emp ** state_res (up t.pre) (up t.post) t.h.g_state Ready)
               as (state_res (up t.pre) (up t.post) t.h.g_state Running ** up t.pre);

          t.h.state := Running;
          AR.write t.h.g_state Running;
          
          Pulse.Lib.Reference.share2 t.h.state;
          dup (task_thunk_typing t) ();

          intro_state_pred_Running t.pre t.post t.h;
          add_one_state_pred t ts;

          rewrite up t.pre ** pts_to t.h.state #0.5R Running ** pure (List.memP t v_runnable) ** task_thunk_typing t
               as vopt topt (fun t -> up t.pre ** pts_to t.h.state #0.5R Running ** pure (List.memP t v_runnable) ** task_thunk_typing t);
          
          topt
        }
        _ -> {
          fold (state_pred t.pre t.post t.h);
          let topt = grab_work'' p ts;
          add_one_state_pred t ts;
          
          (* Weaken the pure inside the vopt *)
          ghost fn weaken (t : task_t)
            requires emp ** (up t.pre ** pts_to t.h.state #0.5R Running ** pure (List.memP t ts) ** task_thunk_typing t)
            ensures  up t.pre ** pts_to t.h.state #0.5R Running ** pure (List.memP t v_runnable) ** task_thunk_typing t
          {
            ()
          };
          weaken_vopt topt emp weaken;

          topt
        }
      }
    }
  }
}


(* Called with pool lock taken *)
fn rec grab_work' (p:pool)
  requires lock_inv p.runnable p.g_runnable
  returns  topt : option task_t
  ensures  lock_inv p.runnable p.g_runnable
        ** vopt topt (fun t ->
             up t.pre ** pts_to t.h.state #0.5R Running ** task_spotted p t ** task_thunk_typing t)
{
  unfold (lock_inv p.runnable p.g_runnable);
  let v_runnable = !p.runnable;
  let topt = grab_work'' p v_runnable;

  AR.take_snapshot_full p.g_runnable;

  (* If Some, the task is spotted *)
  ghost fn spot (t:task_t)
    requires AR.snapshot p.g_runnable v_runnable ** (up t.pre ** pts_to t.h.state #0.5R Running ** pure (List.memP t v_runnable) ** task_thunk_typing t)
    ensures  up t.pre ** pts_to t.h.state #0.5R Running ** task_spotted p t ** task_thunk_typing t
  {
    intro_task_spotted p t v_runnable;
  };
  weaken_vopt topt (AR.snapshot p.g_runnable v_runnable) spot;

  fold (lock_inv p.runnable p.g_runnable);
  topt
}

fn grab_work (p:pool) #f
  requires pool_alive #f p
  returns  topt : option task_t
  ensures  pool_alive #f p
        ** vopt topt (fun t ->
             up t.pre ** pts_to t.h.state #0.5R Running ** task_spotted p t ** task_thunk_typing t)
{
  unfold (pool_alive #f p);
  acquire p.lk;
  let res = grab_work' p;
  release p.lk;
  fold (pool_alive #f p);
  res
}

let undyn pre post (d: Dyn.dyn { Dyn.dyn_has_ty d (task_type pre post) }) : stt unit pre (fun _ -> post) =
  hide_div (fun _ -> let f = Dyn.undyn d in f ())

fn perf_work (t : task_t)
  requires up t.pre ** task_thunk_typing t
  returns  _:unit
  ensures  up t.post
{
  unfold task_thunk_typing t;
  with pre post. assert task_thunk_typing_core t pre post;
  unfold task_thunk_typing_core;
  unfold up;
  slprop_ref_gather t.pre #_ #pre;
  later_credit_buy 1; later_elim _;
  equiv_elim _ _;
  assert pure (Dyn.dyn_has_ty t.thunk (task_type pre post));
  undyn pre post t.thunk;

  fold up t.post; // ????
  drop_ (slprop_ref_pts_to _ _);
}
fn put_back_result (p:pool) #f (t : task_t)
  requires pool_alive #f p **
           task_spotted p t **
           up t.post **
           pts_to t.h.state #0.5R Running
  ensures  pool_alive #f p
{
  unfold (pool_alive #f p);
  acquire p.lk;
  unfold (lock_inv p.runnable p.g_runnable);
  AR.drop_anchor p.g_runnable;
  recall_task_spotted p t;
  AR.lift_anchor p.g_runnable _;
  extract_state_pred p t;

  (* Advance the state and place the post condition back into the pool *)
  assert (state_pred t.pre t.post t.h ** pts_to t.h.state #0.5R Running);
    unfold (state_pred t.pre t.post t.h);
    with v_st. assert (AR.pts_to t.h.g_state v_st);
    pts_to_injective_eq t.h.state;
    assert (pure (v_st == Running));
    rewrite (pts_to t.h.state #(if Running? v_st then 0.5R else 1.0R) (unclaimed v_st))
         as (pts_to t.h.state #0.5R v_st);
    Pulse.Lib.Reference.gather2 t.h.state;
    t.h.state := Done; // Only concrete step (except for mutex taking)
    AR.write t.h.g_state Done;

    rewrite (state_res (up t.pre) (up t.post) t.h.g_state Running) as emp;
    rewrite up t.post as (state_res (up t.pre) (up t.post) t.h.g_state Done);

    intro_state_pred t.pre t.post t.h Done;
  assert (state_pred t.pre t.post t.h);

  (* Restore full pool invariant with trade. *)
  elim_trade _ _;

  fold (lock_inv p.runnable p.g_runnable);
  release p.lk;
  drop_ (task_spotted p t);
  fold (pool_alive #f p);
}

fn do_work_once (#f:perm) (p : pool)
  requires pool_alive #f p
  ensures  pool_alive #f p
{
  let topt = grab_work p;
  match topt {
    None -> {
      rewrite (if Some? topt then up (Some?.v topt).pre else emp)
           as emp;
    }
    Some t -> {
      rewrite each topt as Some t;
      get_vopt #task_t #t ();
      perf_work t;
      put_back_result p t
    }
  }
}


fn rec worker (#f:perm) (p : pool)
  requires pool_alive #f p
  ensures  pool_alive #f p
{
  do_work_once #f p;
  worker p
}

// Await with a bit of helping
fn await_help
         (#p:pool)
         (#post : slprop)
         (h : handle)
         (#f:perm)
  requires pool_alive #f p ** joinable p post h
  ensures  pool_alive #f p ** post
{
  let mut done = false;
  while (let v = !done; (not v))
    invariant b.
      exists* v_done.
        pool_alive #f p **
        pts_to done v_done **
        (if v_done then post else joinable p post h) **
        pure (b == not v_done)
  {
    let b = try_await #p #post h #f;
    done := b;
    if (not b) {
      do_work_once #f p;
    }
  };
}

let ite (b:bool) (p q : slprop) : slprop =
  if b then p else q

fn rec check_if_all_done
  (ts : list task_t)
  requires all_state_pred ts
  returns  b : bool
  ensures  all_state_pred ts ** ite b (all_tasks_done ts) emp
{
  match ts {
    [] -> {
      rewrite emp as (all_tasks_done ts);
      fold (ite true (all_tasks_done ts) emp);
      true;
    }
    t :: ts' -> {
      take_one_h11 t ts';
      unfold (state_pred t.pre t.post t.h);
      let st = !t.h.state;
      match st {
        Done -> {
          let bb = check_if_all_done ts';
          if bb {
            rewrite (ite bb (all_tasks_done ts') emp) as (all_tasks_done ts');
            with g_st. assert (AR.pts_to t.h.g_state g_st);
            assert (pure (g_st == Done \/ g_st == Claimed));
            AR.take_snapshot t.h.g_state;
            fold_all_tasks_done_cons t ts' g_st;
            rewrite (all_tasks_done (t::ts')) as (all_tasks_done ts);
            fold (ite true (all_tasks_done ts) emp);
            fold (state_pred t.pre t.post t.h);
            add_one_state_pred t ts';
            true;
          } else {
            drop_ (ite bb (all_tasks_done ts') emp);
            fold (state_pred t.pre t.post t.h);
            add_one_state_pred t ts';
            rewrite emp as ite false (all_tasks_done ts) emp;
            false;
          }
        }
        Running -> {
          fold (state_pred t.pre t.post t.h);
          add_one_state_pred t ts';
          rewrite emp as ite false (all_tasks_done ts) emp;
          false;
        }
        Ready -> {
          fold (state_pred t.pre t.post t.h);
          add_one_state_pred t ts';
          rewrite emp as ite false (all_tasks_done ts) emp;
          false;
        }
        Claimed -> {
          unreachable();
        }
      }
    }
  }
}

#push-options "--print_implicits"
fn try_await_pool
  (p:pool)
  #is (#f:perm)
  (q : slprop)
  requires pool_alive #f p ** pledge is (pool_done p) q
  returns  b : bool
  ensures  pool_alive #f p ** ite b q (pledge is (pool_done p) q)
{
  unfold (pool_alive #f p);
  acquire p.lk;
  unfold (lock_inv p.runnable p.g_runnable);

  let runnable = !p.runnable;
  let done = check_if_all_done runnable;
  if done {
    rewrite each done as true;
    rewrite (ite true (all_tasks_done runnable) emp)
         as all_tasks_done runnable;

    (* We have permission on the queues + all_tasks_done. Obtain pool_done
    temporarilly to redeem. *)
    AR.drop_anchor p.g_runnable;
    AR.share p.g_runnable;
    fold (pool_done p);
    redeem_pledge _ _ _;
    (*!*) assert q;
    unfold (pool_done p);
    AR.gather p.g_runnable;
    AR.lift_anchor p.g_runnable _;

    fold (ite true q (pledge is (pool_done p) q));
    fold (lock_inv p.runnable p.g_runnable);
    release p.lk;
    fold (pool_alive #f p);

    drop_ (all_tasks_done runnable);

    true
  } else {
    rewrite each done as false;
    rewrite (ite false (all_tasks_done runnable) emp)
         as emp;
    fold (lock_inv p.runnable p.g_runnable);
    release p.lk;
    fold (pool_alive #f p);

    fold (ite false q (pledge is (pool_done p) q));
    false
  }
}

fn await_pool
  (p:pool)
  (#is: inames) (#f: perm)
  (q : slprop)
  requires pool_alive #f p ** pledge is (pool_done p) q
  ensures  pool_alive #f p ** q
{
  let mut done = false;
  fold (ite false q (pledge is (pool_done p) q));
  while (let v = !done; not v)
    invariant b.
      exists* v_done.
        pool_alive #f p **
        pts_to done v_done **
        ite v_done q (pledge is (pool_done p) q) **
        pure (b == not v_done)
  {
    with v_done. assert (pts_to done v_done);
    rewrite each v_done as false;
    unfold (ite false q (pledge is (pool_done p) q));
    let b = try_await_pool p #is #f q;
    done := b;
  };
  with v_done. assert (pts_to done v_done);
  rewrite each v_done as true;
  unfold (ite true q (pledge is (pool_done p) q));
}

fn rec teardown_pool
  (p:pool)
  requires pool_alive p
  ensures  pool_done p
{
  unfold (pool_alive p);
  acquire p.lk;
  unfold (lock_inv p.runnable p.g_runnable);

  let runnable = !p.runnable;
  let b = check_if_all_done runnable;
  if b {
    rewrite ite b (all_tasks_done runnable) emp
         as all_tasks_done runnable;
    AR.drop_anchor p.g_runnable;
    AR.share p.g_runnable;
    fold (pool_done p);

    (* Drop the other ghost half + anchor. *)
    drop_ (AR.pts_to p.g_runnable #0.5R runnable);
    drop_ (AR.anchored p.g_runnable _);

    (* TODO: actually teardown. *)
    drop_ (pts_to p.runnable runnable);
    drop_ (lock_alive _ #0.5R _);
    drop_ (lock_acquired p.lk);
  } else {
    rewrite ite b (all_tasks_done runnable) emp
         as emp;
    (* Spin *)
    fold (lock_inv p.runnable p.g_runnable);
    release p.lk;
    fold (pool_alive p);
    teardown_pool p;
  }
}

ghost
fn share_alive
  (p : pool)
  (f:perm)
  requires pool_alive #f p
  ensures  pool_alive #(f /. 2.0R) p ** pool_alive #(f /. 2.0R) p
{
  unfold (pool_alive #f p);
  Pulse.Lib.SpinLock.share #_ p.lk;
  fold (pool_alive #(f /. 2.0R) p);
  fold (pool_alive #(f /. 2.0R) p);
}

ghost
fn gather_alive
  (p : pool)
  (f:perm)
  requires pool_alive #(f /. 2.0R) p ** pool_alive #(f /. 2.0R) p
  ensures  pool_alive #f p
{
  unfold (pool_alive #(f /. 2.0R) p);
  unfold (pool_alive #(f /. 2.0R) p);
  Pulse.Lib.SpinLock.gather #_ p.lk;
  fold (pool_alive #f p);
}

fn worker_thread (#f:perm) (p : pool)
  requires pool_alive #f p
  ensures emp
{
  worker p;
  drop_ (pool_alive #f p)
}

fn spawn_worker
  (p:pool)
  (#f:perm)
  requires pool_alive #f p
  ensures  emp
{
  fork (fun () -> worker_thread #f p)
}

fn rec spawn_workers
  (p:pool) (#f:perm)
  (n:pos)
  requires pool_alive #f p
  ensures  emp
{
  if (n = 1) {
    spawn_worker p;
  } else {
    share_alive p f;
    spawn_worker p;
    spawn_workers p (n - 1);
  }
}

fn setup_pool
  (n : pos)
  requires emp
  returns p : pool
  ensures pool_alive p
{
  let runnable = Pulse.Lib.Reference.alloc ([] <: list task_t);
  assert (pure (list_preorder #task_t [] [] /\ True));
  let g_runnable = AR.alloc #(list task_t) [] #list_preorder #list_anchor;
  rewrite emp as (all_state_pred []);
  fold (lock_inv runnable g_runnable);
  let lk = new_lock (lock_inv runnable g_runnable);
  let p = {lk; runnable; g_runnable};

  rewrite each lk as p.lk;
  rewrite each g_runnable as p.g_runnable;
  rewrite each runnable as p.runnable;

  Pulse.Lib.SpinLock.share2 p.lk;
  fold (pool_alive p);
  fold (pool_alive p);

  spawn_workers p #1.0R n;

  p
}
