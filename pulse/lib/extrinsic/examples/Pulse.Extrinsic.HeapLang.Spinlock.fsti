module Pulse.Extrinsic.HeapLang.Spinlock

(** Abstract SOURCE spinlock built on the completion flag protocol.
    handle is shareable; held is exclusive even when resource is emp. Acquire
    transfers held(resource) to the caller, and release requires it back.
    allocate installs the protocol from flag |-> 1 and resource.

    The payload exposure premise is intentional: this is a lock for supported
    timeless/locality-independent resources, not arbitrary higher-order ones.
    with_lock brackets an ordinary multi-step body and returns its result;
    its proof frames the held token throughout that body's execution. *)

open Pulse.Extrinsic.HeapLang
open Pulse.Extrinsic.HeapLang.Notation
module H = PulseCore.Heap
module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof
module C = Pulse.Extrinsic.HeapLang.Logic
module G = Pulse.Extrinsic.Ghost
module J = Pulse.Extrinsic.HeapLang.Join

val held (g:G.name) (resource:S.slprop) : S.slprop
val handle (i:S.iref) (g:G.name) (flag:H.core_ref) (resource:S.slprop) : S.slprop

let acquire_at (#ctx:list ty) (flag:expr ctx TRef) = J.wait_at flag
let release_at (#ctx:list ty) (flag:expr ctx TRef) = J.signal_at flag
let acquire (flag:H.core_ref) = acquire_at (Val #[] flag)
let release (flag:H.core_ref) = release_at (Val #[] flag)
let with_lock_at (#ctx:list ty) (#t:ty) (flag:expr ctx TRef) (body:expr ctx t) : expr ctx t =
  acquire_at flag >>
  (let! result = body in
   release_at (weaken flag) >> result)
let with_lock (#t:ty) (flag:H.core_ref) (body:expr [] t) = with_lock_at (Val flag) body

val duplicate (i:S.iref) (g:G.name) (flag:H.core_ref) (resource:S.slprop)
  : Lemma (handle i g flag resource ==
      S.star (handle i g flag resource) (handle i g flag resource))
val exclusive (g:G.name) (resource:S.slprop)
  : Lemma (S.implies (S.star (held g resource) (held g resource)) (S.pure False))
val held_frame (g:G.name) (resource:S.slprop)
  : Lemma (held g resource == S.star (held g S.emp) resource)

val acquire_correct (i:S.iref) (g:G.name) (flag:H.core_ref) (resource:S.slprop)
  : Lemma
      (requires S.implies (P.exposed resource) resource)
      (ensures P.hoare (handle i g flag resource) (acquire flag)
        (P.constant_post (S.star (handle i g flag resource) (held g resource))))
val release_correct (i:S.iref) (g:G.name) (flag:H.core_ref) (resource:S.slprop)
  : Lemma
      (requires S.implies (P.exposed resource) resource)
      (ensures P.hoare (S.star (handle i g flag resource) (held g resource)) (release flag)
        (P.constant_post (handle i g flag resource)))

val allocate (#t:ty) (flag:H.core_ref) (resource:S.slprop) (e:expr [] t) (q:P.post t)
  (proof:(i:S.iref -> g:G.name -> Lemma (P.hoare (handle i g flag resource) e q)))
  : Lemma
      (requires to_val e == None)
      (ensures P.hoare (S.star (C.points_to flag 1) resource) e q)

val with_lock_correct (#t:ty) (i:S.iref) (g:G.name) (flag:H.core_ref) (resource:S.slprop)
  (body:expr [] t) (q:P.post t)
  : Lemma
      (requires S.implies (P.exposed resource) resource /\
        P.hoare resource body (P.prepend_post resource q))
      (ensures P.hoare (handle i g flag resource) (with_lock flag body)
        (P.prepend_post (handle i g flag resource) q))
