module Refinement.Generic.Effect
(* The goal of this experiment is to define a simple,
   abstract memory model on top of HyperStack.
*)
open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
open Refinement.Generic.Lens

let inv #roots #view (l:hs_lens roots view) (h:HS.mem) =
  l.invariant l.x h

let mods #roots #view (l:hs_lens roots view) (h:HS.mem) =
  mods l.footprint l.snapshot h

let get #roots #view (l:hs_lens roots view) (h:HS.mem{inv l h}) =
  l.l.get h

/// The main computation type provided by this module
///   `RST a r pre post`
///    An abstract computation on pairs layered on top of HyperStack.STATE
effect RST (a:Type)
           (#roots:Type0)
           (#view:Type0)
           (l:hs_lens roots view)
           (pre: view -> Type)
           (post: view -> a -> view -> Type) =
       STATE a
            (fun (k:a -> HS.mem -> Type)
               (h0:HS.mem) ->
               inv l h0 /\
               pre (get l h0) /\
               mods l h0 /\
               (forall (x:a) (h1:HS.mem).
                 inv l h1 /\             //final memory is also in the invariant
                 mods l h1 /\
                 post (get l h0)                //and the user-provided post on pairs
                      x
                      (get l h1) ==>
                k x h1))                        //prove the continuation under this hypothesis

let reader_t
      #roots
      #view
      (l:hs_lens roots view) =
  s:imem (l.invariant l.x) ->
  RST view (snap l s)
  (requires fun _ -> True)
  (ensures fun v0 v v1 ->
    v0 == v /\
    v == v1)

let writer_t
      #roots
      #view
      (l:hs_lens roots view) =
  s:imem (l.invariant l.x) ->
  v:view ->
  RST unit (snap l s)
  (requires fun _ -> True)
  (ensures fun _ _ v1 ->
    v1 == v)
