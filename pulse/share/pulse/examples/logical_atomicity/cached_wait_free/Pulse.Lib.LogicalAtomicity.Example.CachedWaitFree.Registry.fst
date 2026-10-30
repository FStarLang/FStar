module Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Registry
#lang-pulse

(**
Ghost failure helping, adapted from cmuparlay's Iris/Rocq CachedWaitFree.v:
https://github.com/cmuparlay/bigatomic-mechanization/blob/251ff8b71e0879f561c729115e972b7a6d3ce0af/theories/CachedWaitFree.v
See LICENSE.Iris for its MIT notice and CAS.fst for the Big Atomics citation.

The reference's AU_cas becomes au below, cas_inv becomes entry_body, and
registry_inv becomes the separating collection entries. publish commits the
winner and help_all plays the role of linearize_cas for the pending losers.
The essential resource is the client's actual continuation: a historical
fact that expected once differed from the value would not suffice to invoke
an arbitrary AU later, after the value may have changed back.

The request log contains only small erased metadata. Each spatial entry owns
its higher-order AU or completed result at the caller's locality. This both
admits non-sendable captured resources and avoids requiring Type0 metadata
to contain arbitrary slprops. Saved-proposition references connect the small
request record to those higher-order results. No client-state sendability,
new ghost-state axiom, or retrospective AU commitment is assumed.
*)

open Pulse.Lib.Pervasives
open Pulse.Lib.ForEvery
module G = Pulse.Lib.GhostReference
module MR = Pulse.Lib.MonotonicGhostRef
module S = FStar.Seq
module H = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Model
module N = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Storage
module M = Pulse.Lib.LogicalAtomicity.Masks
module A = Pulse.Lib.LogicalAtomicity.Atomic
module U = Pulse.Lib.LogicalAtomicity.Update
module L = Pulse.Lib.LogicalAtomicity.Locality
module NonInformative = Pulse.Lib.NonInformative

let model (g:G.ref H.value) v = G.pts_to g #0.5R v
let beta g expected desired old ok =
  model g (if ok then desired else old) ** pure (ok == (old = expected))
instance place_model g v : placeless (model g v) = FStar.Tactics.Typeclasses.solve
instance place_beta g expected desired old ok : placeless (beta g expected desired old ok) =
  FStar.Tactics.Typeclasses.solve

(** Metadata is not ownership of the callback. In particular, success and
failure are names for saved propositions, not independently callable copies
of phi. The exclusive token is held outside the registry until collection. *)
[@@erasable]
noeq type request = {
  expected:H.value;
  desired:H.value;
  caller:loc_id;
  inner:inames;
  credits:nat;
  success:slprop_ref;
  failure:slprop_ref;
  token:G.ref unit;
}
instance non_informative_request : NonInformative.non_informative request = {
  reveal = (fun x -> FStar.Ghost.reveal x) <: NonInformative.revealer request;
}

(** tags is duplicable, but result additionally owns the selected proposition
itself. Thus saved-name agreement cannot manufacture the client's resources. *)
let tags (r:request) (phi:bool -> slprop) =
  slprop_ref_pts_to r.success (phi true) ** slprop_ref_pts_to r.failure (phi false)
let result_at (r:request) (ok:bool) p =
  slprop_ref_pts_to (if ok then r.success else r.failure) p ** p
let result r ok = exists* p. result_at r ok p
instance place_tags r phi : placeless (tags r phi) = FStar.Tactics.Typeclasses.solve
instance dup_tags r phi : duplicable (tags r phi) = FStar.Tactics.Typeclasses.solve

ghost fn pack_result r phi ok
  requires tags r phi ** on r.caller (phi ok)
  ensures on r.caller (result r ok)
{
  ghost_impersonate r.caller (tags r phi ** on r.caller (phi ok))
    (on r.caller (result r ok)) fn _ {
    on_elim (phi ok);
    unfold tags;
    if ok {
      rewrite phi ok as phi true;
      drop_ (slprop_ref_pts_to r.failure (phi false));
      fold result_at r true (phi true);
      fold result r true;
      rewrite result r true as result r ok;
    } else {
      rewrite phi ok as phi false;
      drop_ (slprop_ref_pts_to r.success (phi true));
      fold result_at r false (phi false);
      fold result r false;
      rewrite result r false as result r ok;
    };
    rewrite result r (match ok with | true -> true | false -> false) as result r ok;
    on_intro (result r ok);
  };
}

(** Saved propositions agree only under later. Pay one credit to recover the
original arbitrary phi, rather than assuming equality or discarding it.
The caller eliminates its locality wrapper before invoking this lemma. *)
ghost fn recover_result r phi ok
  requires tags r phi ** result r ok ** later_credit 1
  ensures phi ok
{
  unfold result;
  with p. unfold result_at r ok p;
  unfold tags;
  if ok {
    slprop_ref_gather r.success #p #(phi true);
  } else {
    slprop_ref_gather r.failure #p #(phi false);
  };
  rewrite later (equiv p (phi (match ok with | true -> true | false -> false)))
    as later (equiv p (phi ok));
  later_elim (equiv p (phi ok));
  equiv_elim p (phi ok);
}

ghost fn new_request expected desired caller inner credits phi
  returns r:request
  ensures tags r phi ** G.pts_to r.token () **
    pure (r.expected == expected /\ r.desired == desired /\ r.caller == caller /\
      r.inner == inner /\ r.credits == credits)
{
  let success = slprop_ref_alloc (phi true);
  let failure = slprop_ref_alloc (phi false);
  let token = G.alloc ();
  let r = { expected; desired; caller; inner; credits; success; failure; token };
  rewrite each success as r.success;
  rewrite each failure as r.failure;
  rewrite each token as r.token;
  fold tags r phi;
  r
}
let au g outer (r:request) (phi:bool -> slprop) =
  A.atomic_update outer r.inner r.credits (model g)
    (beta g r.expected r.desired) (fun _ ok -> phi ok)
let held g outer (r:request) phi old =
  on r.caller (A.closing outer r.inner (model g) (au g outer r phi)
    (beta g r.expected r.desired) (fun _ ok -> phi ok) old)
let opened g outer (r:request) phi =
  L.opened r.caller outer r.inner r.credits (model g)
    (beta g r.expected r.desired) (fun _ ok -> phi ok)

ghost fn delay before after pre post
  (f:unit -> M.gaction unit before after pre (fun _ -> post))
  requires pre
  ensures U.fupd before after post
{
  slprop_equivs ();
  U.intro_wand before after emp post pre
    (fun _ -> M.sub_ghost (pre ** emp) (fun _ -> post) (f ()));
  fold U.fupd before after post;
}

let open_request g outer (r:request) phi
  : M.gaction unit outer r.inner
      (on r.caller (au g outer r phi) ** later_credit r.credits)
      (fun _ -> opened g outer r phi) =
  L.open_update r.caller outer r.inner r.credits (model g)
    (beta g r.expected r.desired) (fun _ ok -> phi ok)
let commit g outer (r:request) phi old ok
  : M.gaction unit r.inner outer
      (held g outer r phi old ** beta g r.expected r.desired old ok)
      (fun _ -> on r.caller (phi ok)) =
  L.commit r.caller outer r.inner r.credits (model g)
    (beta g r.expected r.desired) (fun _ ok -> phi ok) old ok
let abort g outer (r:request) phi
  : M.gaction unit r.inner outer (opened g outer r phi)
      (fun _ -> on r.caller (au g outer r phi)) =
  L.abort r.caller outer r.inner r.credits (model g)
    (beta g r.expected r.desired) (fun _ ok -> phi ok)

[@@erasable]
noeq type entry = { req:request; epoch:nat; observed:nat }
type status = | Pending | Done | Collected

(**
State machine for a registered, value-changing request:
  Pending: AU plus opening credits; its observed epoch is still current.
  Done: the first intervening publication committed false; keep that result.
  Collected: the caller exchanged its token for the AU (winner) or result.

Pending -> Collected is used by the successful publisher before it helps
the other entries. Pending -> Done is used for its losers. Done -> Collected
returns a saved failure. Collected owns the token, so a caller still holding
that token cannot encounter Collected without violating full permissions.
Later publications preserve Done results even when values go A--B--A.
*)
let pending g outer r =
  exists* phi. tags r phi ** on r.caller (au g outer r phi) ** later_credit r.credits
let entry_state g outer current (e:entry) st =
  match st with
  | Pending -> pending g outer e.req ** pure (e.epoch == current)
  | Done -> on e.req.caller (result e.req false) ** pure (e.epoch < current)
  | Collected -> G.pts_to e.req.token ()

let entry_body (cells:N.arena) g outer (nodes:S.seq (N.id cells)) (e:entry) =
  pure (e.epoch < S.length nodes /\ S.index nodes e.epoch == e.observed /\
    e.req.expected == N.value cells (S.index nodes e.epoch) /\
    e.req.expected =!= e.req.desired) **
  (exists* st. entry_state g outer (S.length nodes - 1) e st)

let at cells g outer nodes (es:S.seq entry) (i:nat) =
  if i < S.length es then entry_body cells g outer nodes (S.index es i) else emp
(** Unlike additive forall*, forall+ owns every entry separately, permitting
one publication to consume all pending AUs, not merely choose one of them. *)
let entries cells g outer nodes (es:S.seq entry) (n:nat) =
  forall+ (i:nat { i < n }). at cells g outer nodes es i

instance place_entry_state g outer current e st : placeless (entry_state g outer current e st) =
  match st with
  | Pending -> (FStar.Tactics.Typeclasses.solve <: placeless (entry_state g outer current e Pending))
  | Done -> (FStar.Tactics.Typeclasses.solve <: placeless (entry_state g outer current e Done))
  | Collected -> (FStar.Tactics.Typeclasses.solve <: placeless (entry_state g outer current e Collected))
instance place_entry_body cells g outer nodes e : placeless (entry_body cells g outer nodes e) =
  FStar.Tactics.Typeclasses.solve
instance place_at cells g outer nodes es i : placeless (at cells g outer nodes es i) =
  if i < S.length es then place_entry_body cells g outer nodes (S.index es i)
  else placeless_emp
instance send_entries cells g outer nodes es n : is_send (entries cells g outer nodes es n) =
  is_send_forevery (fun (i:nat { i < n }) -> at cells g outer nodes es i)
    #(fun i -> is_send_placeless (at cells g outer nodes es i) #(place_at cells g outer nodes es i))

(** The implementation invariant's name is known only after allocation of
its body. Allocate an empty registry at None; initialize joins the two owner
halves to install Some name exactly once. The shared handle then retains a
persistent snapshot authenticating the outer mask. No recursive invariant
allocation or assumed association between a handle and namespace is needed. *)
let name_order : FStar.Preorder.preorder (option iname) =
  fun x y -> x == None \/ x == y
let mask (name:option iname) =
  match name with | None -> emp_inames | Some i -> add_inv emp_inames i
let extends : FStar.Preorder.preorder (S.seq entry) = fun xs ys -> H.prefix xs ys

[@@erasable]
noeq type registry = {
  owner:MR.mref name_order;
  requests:MR.mref extends;
}
instance non_informative_registry : NonInformative.non_informative registry = {
  reveal = (fun x -> FStar.Ghost.reveal x) <: NonInformative.revealer registry;
}

let content cells g (t:registry) nodes name es =
  MR.pts_to t.owner #0.5R name ** MR.pts_to t.requests #1.0R es **
  entries cells g (mask name) nodes es (S.length es) **
  pure (name == None ==> S.length es == 0)
let body cells g t nodes =
  exists* name es. content cells g t nodes name es
let initialized t name = MR.snapshot t.owner (Some name)
let uninitialized t = MR.pts_to t.owner #0.5R None

instance send_body cells g t nodes : is_send (body cells g t nodes) =
  FStar.Tactics.Typeclasses.solve
instance place_initialized t name : placeless (initialized t name) =
  FStar.Tactics.Typeclasses.solve
instance dup_initialized t name : duplicable (initialized t name) =
  FStar.Tactics.Typeclasses.solve

ghost fn create cells g nodes
  returns t:registry
  ensures body cells g t nodes ** uninitialized t
{
  let owner = MR.alloc #_ #name_order None;
  MR.share owner #None #1.0R #0.5R #0.5R;
  let requests = MR.alloc #_ #extends (S.empty #entry);
  let t = { owner; requests };
  rewrite each owner as t.owner;
  rewrite each requests as t.requests;
  forevery_intro_false #nat (at cells g (mask None) nodes (S.empty #entry));
  forevery_refine_ext #nat (fun i -> i < S.length (S.empty #entry))
    (at cells g (mask None) nodes (S.empty #entry));
  fold entries cells g (mask None) nodes (S.empty #entry) (S.length (S.empty #entry));
  fold content cells g t nodes None (S.empty #entry);
  fold body cells g t nodes;
  fold uninitialized t;
  t
}

ghost fn initialize cells g t nodes name
  requires body cells g t nodes ** uninitialized t
  ensures body cells g t nodes ** initialized t name
{
  unfold body;
  with old es. unfold content cells g t nodes old es;
  unfold uninitialized;
  MR.take_snapshot t.owner #0.5R old;
  MR.recall_snapshot t.owner #0.5R #None #old;
  assert pure (old == None);
  rewrite each old as None;
  MR.gather t.owner #None #0.5R #0.5R;
  rewrite each (0.5R +. 0.5R) as 1.0R;
  MR.update t.owner (Some name);
  MR.share t.owner #(Some name) #1.0R #0.5R #0.5R;
  MR.take_snapshot t.owner #0.5R (Some name);
  drop_ (MR.pts_to t.owner #0.5R (Some name));
  fold initialized t name;
  unfold entries;
  forevery_refine_ext #nat (fun _ -> False) (at cells g (mask None) nodes es);
  forevery_ext (fun (i:nat { False }) -> at cells g (mask None) nodes es i)
    (fun i -> at cells g (mask (Some name)) nodes es i);
  forevery_refine_ext #nat (fun i -> i < S.length es)
    (at cells g (mask (Some name)) nodes es);
  fold entries cells g (mask (Some name)) nodes es (S.length es);
  fold content cells g t nodes (Some name) es;
  fold body cells g t nodes;
}

(** A publication commits every still-pending loser against the NEW value.
The result stays in the registry even after a subsequent A--B--A change. *)
private ghost fn finish_help cells g outer nodes
  (e:entry { e.epoch < S.length nodes - 1 /\ e.epoch < S.length nodes /\
      S.index nodes e.epoch == e.observed /\
      e.req.expected == N.value cells (S.index nodes e.epoch) /\
      e.req.expected =!= e.req.desired }) phi v
  requires tags e.req phi ** on e.req.caller (phi false) ** G.pts_to g #0.5R v
  ensures entry_body cells g outer nodes e ** G.pts_to g #0.5R v
{
  pack_result e.req phi false;
  fold entry_state g outer (S.length nodes - 1) e Done;
  fold entry_body cells g outer nodes e;
}

private ghost fn help_opened cells g outer nodes
  (e:entry { e.epoch < S.length nodes - 1 /\
      e.epoch < S.length nodes /\ S.index nodes e.epoch == e.observed /\
      e.req.expected == N.value cells (S.index nodes e.epoch) /\
      e.req.expected =!= e.req.desired })
  phi (v:H.value { e.req.expected =!= v })
  requires opened g outer e.req phi ** tags e.req phi ** G.pts_to g #0.5R v
  ensures U.fupd e.req.inner outer
    (entry_body cells g outer nodes e ** G.pts_to g #0.5R v)
{
  unfold opened;
  unfold L.opened;
  with old. assert (model g old);
  fold held g outer e.req phi old;
  unfold model;
  // Opening the loser's AU yields the NEW current value, by agreement with
  // the invariant's half. It differs from the registered expected value,
  // so false is justified now, not at the loser's eventual failed CAS.
  G.pts_to_injective_eq g;
  fold model g old;
  fold beta g e.req.expected e.req.desired old false;
  slprop_equivs ();
  delay e.req.inner outer
    ((held g outer e.req phi old ** beta g e.req.expected e.req.desired old false) **
      (tags e.req phi ** G.pts_to g #0.5R v))
    (entry_body cells g outer nodes e ** G.pts_to g #0.5R v)
    (fun _ -> M.bind_ghost
      (M.frame_ghost (tags e.req phi ** G.pts_to g #0.5R v)
        (commit g outer e.req phi old false))
      (fun _ -> M.lift_ghost outer (finish_help cells g outer nodes e phi v)));
}

private ghost fn prepare_help (cells:N.arena) g outer
  (nodes:S.seq (N.id cells) { 0 < S.length nodes })
  (node:N.id cells {
    N.value cells node =!= N.value cells (S.index nodes (S.length nodes - 1)) })
  e
  requires entry_body cells g outer nodes e ** G.pts_to g #0.5R (N.value cells node)
  ensures U.fupd outer outer
    (entry_body cells g outer (S.append nodes (S.create 1 node)) e **
      G.pts_to g #0.5R (N.value cells node))
{
  unfold entry_body;
  with status. assert (entry_state g outer (S.length nodes - 1) e status);
  let st = reveal status;
  let after = S.append nodes (S.create 1 node);
  match st {
    Pending -> {
      rewrite entry_state g outer (S.length nodes - 1) e status
        as entry_state g outer (S.length nodes - 1) e Pending;
      unfold entry_state g outer (S.length nodes - 1) e Pending;
      unfold pending g outer e.req;
      with phi. assert (tags e.req phi ** on e.req.caller (au g outer e.req phi) **
        later_credit e.req.credits);
      assert pure (e.req.expected =!= N.value cells node);
      slprop_equivs ();
      delay outer outer
        ((on e.req.caller (au g outer e.req phi) ** later_credit e.req.credits) **
          (tags e.req phi ** G.pts_to g #0.5R (N.value cells node)))
        (entry_body cells g outer after e ** G.pts_to g #0.5R (N.value cells node))
        (fun _ -> M.bind_ghost
          (M.frame_ghost (tags e.req phi ** G.pts_to g #0.5R (N.value cells node))
            (open_request g outer e.req phi))
          (fun _ -> M.bind_ghost
            (M.lift_ghost e.req.inner (help_opened cells g outer after e phi (N.value cells node)))
            (fun _ -> U.elim_update e.req.inner outer
              (entry_body cells g outer after e ** G.pts_to g #0.5R (N.value cells node)))));
      rewrite each after as S.append nodes (S.create 1 node);
    }
    Done -> {
      rewrite entry_state g outer (S.length nodes - 1) e status
        as entry_state g outer (S.length nodes - 1) e Done;
      unfold entry_state g outer (S.length nodes - 1) e Done;
      fold entry_state g outer (S.length after - 1) e Done;
      fold entry_body cells g outer after e;
      U.return_update outer
        (entry_body cells g outer after e ** G.pts_to g #0.5R (N.value cells node));
      rewrite each after as S.append nodes (S.create 1 node);
    }
    Collected -> {
      rewrite entry_state g outer (S.length nodes - 1) e status
        as entry_state g outer (S.length nodes - 1) e Collected;
      unfold entry_state g outer (S.length nodes - 1) e Collected;
      fold entry_state g outer (S.length after - 1) e Collected;
      fold entry_body cells g outer after e;
      U.return_update outer
        (entry_body cells g outer after e ** G.pts_to g #0.5R (N.value cells node));
      rewrite each after as S.append nodes (S.create 1 node);
    }
  }
}

let help_one (cells:N.arena) g outer
  (nodes:S.seq (N.id cells) { 0 < S.length nodes })
  (node:N.id cells {
    N.value cells node =!= N.value cells (S.index nodes (S.length nodes - 1)) }) e =
  M.bind_ghost (M.lift_ghost outer (prepare_help cells g outer nodes node e))
    (fun _ -> U.elim_update outer outer
      (entry_body cells g outer (S.append nodes (S.create 1 node)) e **
        G.pts_to g #0.5R (N.value cells node)))

private ghost fn split_last cells g outer nodes es (n:nat { n < S.length es })
  requires entries cells g outer nodes es (n + 1)
  ensures entry_body cells g outer nodes (S.index es n) ** entries cells g outer nodes es n
{
  unfold entries;
  forevery_remove' #nat (fun i -> i < n + 1) (at cells g outer nodes es) n;
  forevery_refine_ext #nat (fun i -> i < n) (at cells g outer nodes es);
  fold entries cells g outer nodes es n;
  rewrite at cells g outer nodes es n as entry_body cells g outer nodes (S.index es n);
}

private ghost fn join_last cells g outer nodes es (n:nat { n < S.length es })
  requires entry_body cells g outer nodes (S.index es n) ** entries cells g outer nodes es n
  ensures entries cells g outer nodes es (n + 1)
{
  unfold entries;
  rewrite entry_body cells g outer nodes (S.index es n) as at cells g outer nodes es n;
  forevery_insert #nat #(fun i -> i < n) (at cells g outer nodes es) n;
  forevery_refine_ext #nat (fun i -> i < n + 1) (at cells g outer nodes es);
  fold entries cells g outer nodes es (n + 1);
}

private ghost fn empty_entries cells g outer nodes after es
  requires entries cells g outer nodes es 0
  ensures entries cells g outer after es 0
{
  unfold entries;
  forevery_ext (fun (i:nat { i < 0 }) -> at cells g outer nodes es i)
    (fun i -> at cells g outer after es i);
  fold entries cells g outer after es 0;
}

(** This finite traversal constructs only ghost actions and erases entirely.
Every help_one restores outer before the next AU opens, so different clients
may use overlapping inner masks. The one observable publication step is in
Attempt; its implementation invariant stays open throughout this cleanup. *)
let rec help_all (cells:N.arena) g outer
  (nodes:S.seq (N.id cells) { 0 < S.length nodes })
  (node:N.id cells {
    N.value cells node =!= N.value cells (S.index nodes (S.length nodes - 1)) })
  es (n:nat { n <= S.length es })
  : Tot (M.gaction unit outer outer
      (entries cells g outer nodes es n ** G.pts_to g #0.5R (N.value cells node))
      (fun _ -> entries cells g outer (S.append nodes (S.create 1 node)) es n **
        G.pts_to g #0.5R (N.value cells node)))
      (decreases n)
  =
  if n = 0 then
    M.lift_ghost outer
      (frame_ghost (G.pts_to g #0.5R (N.value cells node))
        (empty_entries cells g outer nodes (S.append nodes (S.create 1 node)) es))
  else
    let k = n - 1 in
    let after = S.append nodes (S.create 1 node) in
    slprop_equivs ();
    M.bind_ghost
      (M.sub_ghost
        (entries cells g outer nodes es n ** G.pts_to g #0.5R (N.value cells node))
        (fun _ -> (entry_body cells g outer nodes (S.index es k) **
          G.pts_to g #0.5R (N.value cells node)) ** entries cells g outer nodes es k)
        (M.lift_ghost outer
          (frame_ghost (G.pts_to g #0.5R (N.value cells node)) (split_last cells g outer nodes es k))))
      (fun _ -> M.bind_ghost
        (M.frame_ghost (entries cells g outer nodes es k) (help_one cells g outer nodes node (S.index es k)))
        (fun _ -> M.bind_ghost
          (M.sub_ghost
            ((entry_body cells g outer after (S.index es k) **
              G.pts_to g #0.5R (N.value cells node)) ** entries cells g outer nodes es k)
            (fun _ -> (entry_body cells g outer after (S.index es k) **
              entries cells g outer after es k) ** G.pts_to g #0.5R (N.value cells node))
            (M.frame_ghost (entry_body cells g outer after (S.index es k))
              (help_all cells g outer nodes node es k)))
          (fun _ -> M.lift_ghost outer
            (frame_ghost (G.pts_to g #0.5R (N.value cells node)) (join_last cells g outer after es k)))))

ghost fn expose cells g t nodes name
  preserves initialized t name
  requires body cells g t nodes
  ensures exists* es. content cells g t nodes (Some name) es
{
  unfold body;
  with owner es. unfold content cells g t nodes owner es;
  dup (initialized t name) ();
  unfold initialized;
  MR.recall_snapshot t.owner #0.5R #owner #(Some name);
  assert pure (owner == Some name);
  rewrite each owner as Some name;
  fold initialized t name;
  fold content cells g t nodes (Some name) es;
}

(** A prefix snapshot makes an index stable as requests are appended. Entries
are never removed from metadata; collection changes only their spatial state.
The receipt combines this persistent lookup evidence with a one-use token. *)
let registration_at t (r:request) observed (es:S.seq entry) (i:nat) =
  MR.snapshot t.requests es **
  pure (i < S.length es /\ (S.index es i).req == r /\ (S.index es i).observed == observed)
let registered t (r:request) observed =
  G.pts_to r.token () **
  (exists* es i. registration_at t r observed es i)

ghost fn register cells g t (nodes:S.seq (N.id cells) { 0 < S.length nodes })
  name es phi (r:request { r.expected == N.value cells (S.index nodes (S.length nodes - 1)) /\
    r.expected =!= r.desired })
  requires content cells g t nodes (Some name) es **
    tags r phi ** on r.caller (au g (mask (Some name)) r phi) **
    later_credit r.credits ** G.pts_to r.token ()
  ensures body cells g t nodes ** registered t r (S.index nodes (S.length nodes - 1))
{
  unfold content;
  let e = { req=r; epoch=S.length nodes - 1; observed=S.index nodes (S.length nodes - 1) };
  rewrite each r as e.req;
  fold pending g (mask (Some name)) e.req;
  fold entry_state g (mask (Some name)) (S.length nodes - 1) e Pending;
  fold entry_body cells g (mask (Some name)) nodes e;
  let es' = S.append es (S.create 1 e);
  unfold entries;
  forevery_ext
    (fun (i:nat { i < S.length es }) -> at cells g (mask (Some name)) nodes es i)
    (fun i -> at cells g (mask (Some name)) nodes es' i);
  rewrite entry_body cells g (mask (Some name)) nodes e
    as at cells g (mask (Some name)) nodes es' (S.length es);
  forevery_insert #nat #(fun i -> i < S.length es)
    (at cells g (mask (Some name)) nodes es') (S.length es);
  forevery_refine_ext #nat (fun i -> i < S.length es')
    (at cells g (mask (Some name)) nodes es');
  fold entries cells g (mask (Some name)) nodes es' (S.length es');
  MR.update t.requests es';
  MR.take_snapshot t.requests #1.0R es';
  rewrite each e.req as r;
  fold registration_at t r (S.index nodes (S.length nodes - 1)) es' (S.length es);
  fold registered t r (S.index nodes (S.length nodes - 1));
  fold content cells g t nodes (Some name) es';
  fold body cells g t nodes;
}

let hole cells g t nodes name es i =
  MR.pts_to t.owner #0.5R (Some name) ** MR.pts_to t.requests #1.0R es **
  (forall+ (j:nat { j < S.length es /\ j =!= i }).
    at cells g (mask (Some name)) nodes es j)

let selected (es:S.seq entry) (i:nat) r observed =
  i < S.length es /\ (S.index es i).req == r /\ (S.index es i).observed == observed

ghost fn select cells g t nodes name es r observed
  preserves registered t r observed
  requires content cells g t nodes (Some name) es
  returns index:nat
  ensures pure (selected es index r observed) **
    hole cells g t nodes name es index **
    at cells g (mask (Some name)) nodes es index
{
  unfold content;
  unfold registered;
  with old i. unfold registration_at t r observed old i;
  dup (MR.snapshot t.requests old) ();
  MR.recall_snapshot t.requests #1.0R #es #old;
  assert pure (i < S.length es /\ S.index es i == S.index old i);
  fold registration_at t r observed old i;
  fold registered t r observed;
  unfold entries;
  forevery_remove' #nat (fun j -> j < S.length es)
    (at cells g (mask (Some name)) nodes es) i;
  fold hole cells g t nodes name es i;
  reveal i
}

ghost fn replace cells g t nodes name es (i:nat { i < S.length es })
  requires hole cells g t nodes name es i **
    entry_body cells g (mask (Some name)) nodes (S.index es i)
  ensures content cells g t nodes (Some name) es
{
  unfold hole;
  rewrite entry_body cells g (mask (Some name)) nodes (S.index es i)
    as at cells g (mask (Some name)) nodes es i;
  forevery_insert #nat #(fun j -> j < S.length es /\ j =!= i)
    (at cells g (mask (Some name)) nodes es) i;
  forevery_refine_ext #nat (fun j -> j < S.length es)
    (at cells g (mask (Some name)) nodes es);
  fold entries cells g (mask (Some name)) nodes es (S.length es);
  fold content cells g t nodes (Some name) es;
}

(** Successful pointer CAS means the observed identity is still current.
Uniqueness of node identities equates the entry's epoch with the current
epoch, ruling out Done. Move its AU out and put its token into Collected,
so help_all cannot also commit the winner as a loser. *)
ghost fn claim (cells:N.arena) g outer
  (nodes:S.seq (N.id cells) { 0 < S.length nodes /\ H.unique nodes })
  (e:entry { e.observed == S.index nodes (S.length nodes - 1) })
  requires entry_body cells g outer nodes e ** G.pts_to e.req.token ()
  ensures entry_body cells g outer nodes e ** pending g outer e.req
{
  unfold entry_body;
  with status. assert (entry_state g outer (S.length nodes - 1) e status);
  let st = reveal status;
  assert pure (e.epoch == S.length nodes - 1);
  match st {
    Pending -> {
      rewrite entry_state g outer (S.length nodes - 1) e status
        as entry_state g outer (S.length nodes - 1) e Pending;
      unfold entry_state g outer (S.length nodes - 1) e Pending;
      fold entry_state g outer (S.length nodes - 1) e Collected;
      fold entry_body cells g outer nodes e;
    }
    Done -> {
      rewrite entry_state g outer (S.length nodes - 1) e status
        as entry_state g outer (S.length nodes - 1) e Done;
      unfold entry_state g outer (S.length nodes - 1) e Done;
      assert pure False;
      unreachable ();
    }
    Collected -> {
      rewrite entry_state g outer (S.length nodes - 1) e status
        as entry_state g outer (S.length nodes - 1) e Collected;
      unfold entry_state g outer (S.length nodes - 1) e Collected;
      G.gather e.req.token;
      G.pts_to_perm_bound e.req.token;
      assert pure False;
      unreachable ();
    }
  }
}

(** Attempt.two_failures establishes the changed-identity premise. Pending
would require this observed identity to remain current, while Collected
would duplicate the token. Only Done remains, with the actual saved phi. *)
ghost fn collect (cells:N.arena) g outer
  (nodes:S.seq (N.id cells) { 0 < S.length nodes })
  (e:entry { e.observed =!= S.index nodes (S.length nodes - 1) })
  requires entry_body cells g outer nodes e ** G.pts_to e.req.token ()
  ensures entry_body cells g outer nodes e ** on e.req.caller (result e.req false)
{
  unfold entry_body;
  with status. assert (entry_state g outer (S.length nodes - 1) e status);
  let st = reveal status;
  match st {
    Pending -> {
      rewrite entry_state g outer (S.length nodes - 1) e status
        as entry_state g outer (S.length nodes - 1) e Pending;
      unfold entry_state g outer (S.length nodes - 1) e Pending;
      assert pure False;
      unreachable ();
    }
    Done -> {
      rewrite entry_state g outer (S.length nodes - 1) e status
        as entry_state g outer (S.length nodes - 1) e Done;
      unfold entry_state g outer (S.length nodes - 1) e Done;
      fold entry_state g outer (S.length nodes - 1) e Collected;
      fold entry_body cells g outer nodes e;
    }
    Collected -> {
      rewrite entry_state g outer (S.length nodes - 1) e status
        as entry_state g outer (S.length nodes - 1) e Collected;
      unfold entry_state g outer (S.length nodes - 1) e Collected;
      G.gather e.req.token;
      G.pts_to_perm_bound e.req.token;
      assert pure False;
      unreachable ();
    }
  }
}

ghost fn take_pending (cells:N.arena) g t
  (nodes:S.seq (N.id cells) { 0 < S.length nodes /\ H.unique nodes })
  name es r
  requires content cells g t nodes (Some name) es **
    registered t r (S.index nodes (S.length nodes - 1))
  ensures content cells g t nodes (Some name) es ** pending g (mask (Some name)) r
{
  let i = select cells g t nodes name es r (S.index nodes (S.length nodes - 1));
  rewrite at cells g (mask (Some name)) nodes es i
    as entry_body cells g (mask (Some name)) nodes (S.index es i);
  unfold registered;
  drop_ (exists* snapshot index.
    registration_at t r (S.index nodes (S.length nodes - 1)) snapshot index);
  rewrite G.pts_to r.token () as G.pts_to (S.index es i).req.token ();
  claim cells g (mask (Some name)) nodes (S.index es i);
  rewrite pending g (mask (Some name)) (S.index es i).req
    as pending g (mask (Some name)) r;
  replace cells g t nodes name es i;
}

ghost fn take_result (cells:N.arena) g t
  (nodes:S.seq (N.id cells) { 0 < S.length nodes })
  name es r (observed:nat { observed =!= S.index nodes (S.length nodes - 1) })
  requires content cells g t nodes (Some name) es ** registered t r observed
  ensures body cells g t nodes ** on r.caller (result r false)
{
  let i = select cells g t nodes name es r observed;
  rewrite at cells g (mask (Some name)) nodes es i
    as entry_body cells g (mask (Some name)) nodes (S.index es i);
  unfold registered;
  drop_ (exists* snapshot index. registration_at t r observed snapshot index);
  rewrite G.pts_to r.token () as G.pts_to (S.index es i).req.token ();
  collect cells g (mask (Some name)) nodes (S.index es i);
  rewrite on (S.index es i).req.caller (result (S.index es i).req false)
    as on r.caller (result r false);
  replace cells g t nodes name es i;
  fold body cells g t nodes;
}

ghost fn change_model g old desired
  requires model g old ** G.pts_to g #0.5R old
  ensures model g desired ** G.pts_to g #0.5R desired
{
  unfold model;
  G.gather g;
  G.write g desired;
  G.share g;
  rewrite each (1.0R /. 2.0R) as 0.5R;
  fold model g desired;
}

private ghost fn restore_after_help cells g t nodes name es
  requires MR.pts_to t.owner #0.5R (Some name) ** MR.pts_to t.requests #1.0R es **
    entries cells g (mask (Some name)) nodes es (S.length es)
  ensures body cells g t nodes
{
  fold content cells g t nodes (Some name) es;
  fold body cells g t nodes;
}

private ghost fn finish_success (cells:N.arena) g t
  (nodes:S.seq (N.id cells) { 0 < S.length nodes })
  (node:N.id cells {
    N.value cells node =!= N.value cells (S.index nodes (S.length nodes - 1)) })
  name es r phi
  requires content cells g t nodes (Some name) es **
    G.pts_to g #0.5R (N.value cells node) ** tags r phi ** on r.caller (phi true)
  ensures U.fupd (mask (Some name)) (mask (Some name))
    (body cells g t (S.append nodes (S.create 1 node)) **
      G.pts_to g #0.5R (N.value cells node) ** on r.caller (result r true))
{
  pack_result r phi true;
  unfold content;
  let outer = mask (Some name);
  let after = S.append nodes (S.create 1 node);
  rewrite each (mask (Some name)) as outer;
  slprop_equivs ();
  delay outer outer
    ((entries cells g outer nodes es (S.length es) ** G.pts_to g #0.5R (N.value cells node)) **
      (MR.pts_to t.owner #0.5R (Some name) ** MR.pts_to t.requests #1.0R es **
        on r.caller (result r true)))
    (body cells g t after ** G.pts_to g #0.5R (N.value cells node) ** on r.caller (result r true))
    (fun _ -> M.bind_ghost
      (M.frame_ghost
        (MR.pts_to t.owner #0.5R (Some name) ** MR.pts_to t.requests #1.0R es **
          on r.caller (result r true))
        (help_all cells g outer nodes node es (S.length es)))
      (fun _ -> M.lift_ghost outer
        (frame_ghost (G.pts_to g #0.5R (N.value cells node) ** on r.caller (result r true))
          (restore_after_help cells g t after name es))));
  rewrite each outer as mask (Some name);
  rewrite each after as S.append nodes (S.create 1 node);
}

private ghost fn success_opened (cells:N.arena) g t
  (nodes:S.seq (N.id cells) { 0 < S.length nodes })
  (node:N.id cells) name es
  (r:request { r.expected == N.value cells (S.index nodes (S.length nodes - 1)) /\
    r.desired == N.value cells node /\ r.expected =!= r.desired }) phi
  requires opened g (mask (Some name)) r phi ** tags r phi **
    G.pts_to g #0.5R (N.value cells (S.index nodes (S.length nodes - 1))) **
    content cells g t nodes (Some name) es
  ensures U.fupd r.inner (mask (Some name))
    (body cells g t (S.append nodes (S.create 1 node)) **
      G.pts_to g #0.5R (N.value cells node) ** on r.caller (result r true))
{
  unfold opened;
  unfold L.opened;
  with old. assert (model g old);
  fold held g (mask (Some name)) r phi old;
  unfold model;
  G.pts_to_injective_eq g;
  fold model g old;
  change_model g old (N.value cells node);
  rewrite model g (N.value cells node) as model g r.desired;
  fold beta g r.expected r.desired old true;
  slprop_equivs ();
  let outer = mask (Some name);
  let after = S.append nodes (S.create 1 node);
  rewrite each (mask (Some name)) as outer;
  delay r.inner outer
    ((held g outer r phi old ** beta g r.expected r.desired old true) **
      (content cells g t nodes (Some name) es ** G.pts_to g #0.5R (N.value cells node) ** tags r phi))
    (body cells g t after ** G.pts_to g #0.5R (N.value cells node) ** on r.caller (result r true))
    (fun _ -> M.bind_ghost
      (M.frame_ghost
        (content cells g t nodes (Some name) es ** G.pts_to g #0.5R (N.value cells node) ** tags r phi)
        (commit g outer r phi old true))
      (fun _ -> M.bind_ghost
        (M.lift_ghost outer (finish_success cells g t nodes node name es r phi))
        (fun _ -> U.elim_update outer outer
          (body cells g t after ** G.pts_to g #0.5R (N.value cells node) ** on r.caller (result r true)))));
  rewrite each outer as mask (Some name);
  rewrite each after as S.append nodes (S.create 1 node);
}

(**
Logical cleanup of a successful physical publication, in this order:
  1. claim the winner's registered AU and mark its entry Collected;
  2. agree on the old value, update both model halves, and commit true;
  3. open every remaining pending AU against the new value and commit false;
  4. restore the registry for the extended publication history.

The physical fields/history have already changed in Attempt.exchange_core.
The old registry is temporarily framed beside them, but the enclosing
single-step runner cannot close the invariant until this cleanup finishes.
*)
ghost fn publish (cells:N.arena) g t
  (nodes:S.seq (N.id cells) { 0 < S.length nodes /\ H.unique nodes })
  (node:N.id cells) name
  (r:request { r.expected == N.value cells (S.index nodes (S.length nodes - 1)) /\
    r.desired == N.value cells node /\ r.expected =!= r.desired })
  preserves initialized t name
  requires body cells g t nodes ** registered t r (S.index nodes (S.length nodes - 1)) **
    G.pts_to g #0.5R (N.value cells (S.index nodes (S.length nodes - 1)))
  ensures U.fupd (mask (Some name)) (mask (Some name))
    (body cells g t (S.append nodes (S.create 1 node)) **
      G.pts_to g #0.5R (N.value cells node) ** on r.caller (result r true))
{
  expose cells g t nodes name;
  with es. assert (content cells g t nodes (Some name) es);
  take_pending cells g t nodes name es r;
  unfold pending;
  with phi. assert (tags r phi ** on r.caller (au g (mask (Some name)) r phi) ** later_credit r.credits);
  slprop_equivs ();
  let outer = mask (Some name);
  let after = S.append nodes (S.create 1 node);
  rewrite each (mask (Some name)) as outer;
  delay outer outer
    ((on r.caller (au g outer r phi) ** later_credit r.credits) **
      (content cells g t nodes (Some name) es ** tags r phi **
        G.pts_to g #0.5R (N.value cells (S.index nodes (S.length nodes - 1)))))
    (body cells g t after ** G.pts_to g #0.5R (N.value cells node) ** on r.caller (result r true))
    (fun _ -> M.bind_ghost
      (M.frame_ghost (content cells g t nodes (Some name) es ** tags r phi **
        G.pts_to g #0.5R (N.value cells (S.index nodes (S.length nodes - 1))))
        (open_request g outer r phi))
      (fun _ -> M.bind_ghost
        (M.lift_ghost r.inner (success_opened cells g t nodes node name es r phi))
        (fun _ -> U.elim_update r.inner outer
          (body cells g t after ** G.pts_to g #0.5R (N.value cells node) ** on r.caller (result r true)))));
  rewrite each outer as mask (Some name);
  rewrite each after as S.append nodes (S.create 1 node);
}
