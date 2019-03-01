module Refinement.Generic
(* The goal of this experiment is to define a simple,
   abstract memory model on top of HyperStack.
*)
open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST
module T = FStar.Tactics.Typeclasses

let inv_t r = HS.mem -> r -> prop

let imem #roots (inv:inv_t roots) (r:roots) = h:HS.mem{inv h r}

noeq
type pre_lens 
       #roots
       (inv:inv_t roots)
       (a:Type) = {
  get: r:roots -> imem inv r -> GTot a;
  put: r:roots -> imem inv r -> a -> GTot (imem inv r)
}

let get_put #roots (#inv:inv_t roots) #a (l:pre_lens inv a) =
  forall r (h:imem inv r).{:pattern (l.put r h (l.get r h))}
    l.put r h (l.get r h) == h

let put_get #roots (#inv:inv_t roots) #a (l:pre_lens inv a) =
  forall r (h:imem inv r) (x:a).{:pattern (l.get r (l.put r h x))}
    l.get r (l.put r h x) == x

let put_put #roots (#inv:inv_t roots) #a (l:pre_lens inv a) =
  forall r (h:imem inv r) (x:a).{:pattern (l.put r (l.put r h x) x)}
    l.put r (l.put r h x) x == l.put r h x

[@(unifier_hint_injective)]
let lens #roots (inv:inv_t roots) (a:Type) =
  l:pre_lens inv a{
    get_put l /\
    put_get l /\
    put_put l
  }

[@unifier_hint_injective]
let rlens #roots (#inv:inv_t roots) (#a:Type) (l:lens inv a) = roots
  
abstract
let l_get #roots (#inv:inv_t roots) (#b:Type0) (l:lens inv b) r h =
  l.get r h

abstract
let l_put #roots (#inv:inv_t roots) (#b:Type0) (l:lens inv b) r h v =
  l.put r h v

let l_get_l_put_lens #roots (#inv:inv_t roots) (#b:Type0) (l:lens inv b)
  : Lemma ((forall r h. {:pattern (l_get l r h)} l_get l r h == l.get r h) /\
           (forall r h v. {:pattern (l_put l r h v)} l_put l r h v == l.put r h v)) = ()    

/// The main computation type provided by this module
///   `RST a r pre post`
///    An abstract computation on pairs layered on top of HyperStack.STATE
effect RST (a:Type)
           (#roots:Type u#1)
           (#inv:inv_t roots)
           (#b:Type0)
           (#l:lens inv b)
           (r:rlens l)
           (pre: b -> Type) 
           (post: b -> a -> b -> Type) =
       STATE a
            (fun (k:a -> HS.mem -> Type)
               (h0:HS.mem) ->
               inv h0 r /\               //expect the initial memory to be in the invariat
               pre (l_get l r h0) /\
               (forall (x:a) (h1:HS.mem).
                 inv h1 r /\             //final memory is also in the invariant
                 post (l_get l r h0)                //and the user-provided post on pairs
                      x
                      (l_get l r h1) ==>
                k x h1))                        //prove the continuation under this hypothesis
