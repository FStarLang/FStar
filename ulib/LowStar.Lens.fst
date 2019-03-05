(*
   Copyright 2008-2019 Microsoft Research

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
module LowStar.Lens
open FStar.HyperStack.ST
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

(* This module provides a more abstract way of verifying Low*
   programs.

   Rather than working directly with hyperstacks, one can reason via a
   `lens` that provides a view of a hyperstack as a store containing
   just a n-tuple of a user's choice.

   The main technical idea is to use a lens-indexed effect, `LensST`,
   a thin layer on top of FStar.HyperStack.ST.Stack, which allows
   writing specification using just the view on the hyperstack, rather
   than the full hyperstack itself, while also systematically
   enforcing the invariants of the lens.

   So far, we do not require the full generality of lenses. However,
   the framework is setup to permit moving in that direction, should
   we need it.

   We focus primarily on the `get` operation, to support viewing a
   hyperstack fragment more abstractly and operations that mutate the
   hyperstack are specified in terms of `get` operation on the new
   state rather than a `put`.

   The main type of this module is an `hs_lens a b`, a hyperstack
   lens. The first index `a` is typically some set of "roots" into a
   hyperstack, e.g, one or more pointers. The second index `b` is the
   view of the hyperstack reachable from those roots.

   An `hs_lens` also encapsulates various invariants on the
   hyperstack, e.g., the liveness of the roots etc. and is done in a
   way to enable composition via products: i.e., given an `h1:hs_lens
   a b` and `h2:hs_lens c d`, under suitable separation conditions,
   one can build a product lens `hs_lens (a & c) (b & d)`.

   Finally, the module provides the hs_lens-indexed effect `LensST`.
*)

(* We start with the basic definitions of lenses *)

/// `get_t` and `put_t`:
///
/// The type of the lens operations between a pair of types Note,
/// these lenses are for specification only, i.e., they are ghost
/// operators
let get_t a b = a -> GTot b
let put_t a b = b -> a -> GTot a

/// `get_put`: The main useful law
/// You get what you put
let get_put (get:get_t 'a 'b) (put:put_t 'a 'b) =
  forall (a:'a) (b:'b).{:pattern (get (put b a))}
    get (put b a) == b

/// `put_get`: A law for eliminating redundant writes
/// Putting what you got is a noop
let put_get (get:get_t 'a 'b) (put:put_t 'a 'b) =
  forall (a:'a).{:pattern (put (get a) a)}
    put (get a) a == a

/// `put_put`: Another law for eliminating redundant writes
let put_put (get:get_t 'a 'b) (put:put_t 'a 'b) =
  forall (a:'a) (b1 b2:'b). {:pattern (put b2 (put b1 a))}
    put b2 (put b1 a) == put b2 a

/// `lens`: A triple of a `get`, `put` and the laws
///
/// Note, so far, we only require the `get_put` law
noeq
type lens 'a 'b = {
  get: get_t 'a 'b;
  put: put_t 'a 'b;
  lens_laws: squash (
    get_put get put //  /\
    // put_get get put /\
    // put_put get put
  )
}

unfold
let get (l:lens 'a 'b) (x:'a) : GTot 'b =
  match l with
  | {get=get} -> get x

unfold
let put (l:lens 'a 'b) (x:'a) (y:'b) : GTot 'a =
  match l with
  | {put=put} -> put y x

(* Now, we work towards defining `hs_lens`, a lens on hyperstacks *)

/// `imem inv`:
///
/// A refinement of hyperstacks satisifying the invariant `inv`
/// We will mainly use lenses between `imem inv` and some type `a`
let imem inv = m:HS.mem{inv m}

/// `eloc` : A convenient abbreviation for an erased location
let eloc = Ghost.erased B.loc

/// `as_loc`: Coercing an `eloc` to a `loc`
let as_loc (x:eloc) : GTot B.loc = Ghost.reveal x

(* Rather than the lens laws, more useful in the Low* setting are laws
   that describe the action of `get` and `put` in terms of existing
   Low* concepts, e.g., footprints in terms of `loc`; modifies clauses
   etc.  *)

/// `get_reads_loc el get`: States that `get` only depends on the `el`
///   fragment of a hyperstack
let get_reads_loc #b #inv (el:eloc) (get:get_t (imem inv) b) =
  forall (h0 h1:imem inv) loc. {:pattern  (B.modifies loc h0 h1); (get h1)}
    B.loc_disjoint (as_loc el) loc /\
    B.modifies loc h0 h1 ==>
    get h0 == get h1

/// `put_modifies_loc el put`: States that `put` only mutates the `el`
///   fragment of a hyperstack
let put_modifies_loc #b #inv (el:eloc) (put:put_t (imem inv) b) =
  forall (h0:imem inv) (v:b).{:pattern (put v h0)}
    B.modifies (as_loc el) h0 (put v h0)

/// `invariant_reads_loc el inv`: States that the invariant `inv`
///   only depends on the `el` fragment of a hyperstack
let invariant_reads_loc inv (el:eloc) =
  forall h0 h1 loc.{:pattern (B.modifies loc h0 h1); (inv h1)}
    inv h0 /\
    B.loc_disjoint (as_loc el) loc /\
    B.modifies loc h0 h1 ==>
    inv h1

/// `imem_lens inv b loc` is a lens between an `imem inv` and `b`
/// whose footprint is loc
let imem_lens inv b loc =
  l:lens (imem inv) b {
    get_reads_loc loc l.get /\
    put_modifies_loc loc l.put /\
    invariant_reads_loc inv loc
  }

(* A distinctive feature of the setup here is the encapsulation of
   modifies clauses. See the definition of the `RST` effect for more
   details on how it is used.

   The main idea is that when creating an `hs_lens`, we record within
   it a memory snapshot. All state modifications are stated with
   respect to this snapshot, rather than relating the pre/post states
   of each sub-computation. This frees client programs from reasoning
   about the transitive composition of the modifies clauses.
*)


/// `hs_lens a b`:
///
///    Encapsulates an `imem_lens` between a fragment of a hyperstack
///    reachable from `x:a` and its view `b`.
noeq
type hs_lens a b = {
  footprint: eloc;                        //footprint of get, put, inv
  invariant: a -> HS.mem -> Type0;          //invariant, typically liveness
  x:a;                                    //root of the hyperstack fragment
  snapshot:imem (invariant x);            //initial state (see above and LowStar.Lens.Effect)
  l:imem_lens (invariant x) b footprint   //the imem_lens itself
}

/// `snap`: Updating the memory snapshot
let snap (l:hs_lens 'a 'b) (h:imem (l.invariant l.x))
  : hs_lens 'a 'b
  = {l with snapshot = h}

/// `mods l h`: Abstract modifies, relating a lens for a hyperstack
///
/// I see `mods l` as a unary invariant on hyperstack's rather than
/// the usual binary relation `modifies loc`.
///
/// The unary relation frees clients from reasoning about composition
/// of adjacent modifies clauses
abstract
let mods (l:hs_lens 'a 'b) (h:HS.mem) =
  B.modifies (as_loc l.footprint) l.snapshot h /\
  FStar.HyperStack.ST.equal_domains l.snapshot h

(* We now get to the definition of the lens-indexed effect, LensST *)
/// `inv`: a slightly more abstract way to state the invariant
/// of an `hs_lens`
abstract
let inv #roots #view (l:hs_lens roots view) (h:HS.mem) =
  l.invariant l.x h /\
  mods l h

/// `view`: a slightly more abstract way to apply the lens's view to a
/// hyperstack
abstract
let view #roots #view (l:hs_lens roots view) (h:imem (inv l)) =
  l.l.get h

/// The main computation type provided by this module
///   `LensST a r pre post`
///    An abstract computation on pairs layered on top of HyperStack.STATE
effect LensST (a:Type)
           (#roots:Type0)
           (#v:Type0)
           (l:hs_lens roots v)
           (pre: v -> Type)
           (post: v -> a -> v -> Type) =
       STATE a
            (fun (k:a -> HS.mem -> Type)
               (h0:HS.mem) ->
               inv l h0 /\               //Require the lens invariant
               pre (view l h0) /\        //Require the pre-condition on the view
               (forall (x:a) (h1:HS.mem).
                 inv l h1 /\                          //Ensure the lens invariant
                 post (view l h0) x (view l h1) ==>   //Ensure the post-condition on the view
                 k x h1))                            //prove the  continuation under this hypothesis

/// `reveal_inv`: Revealing the abstract invariant
let reveal_inv ()
  : Lemma ((forall #a #b (l:hs_lens a b) h. {:pattern inv l h}
            inv l h <==>
            (l.invariant l.x h /\
             B.modifies (as_loc l.footprint) l.snapshot h /\
             FStar.HyperStack.ST.equal_domains l.snapshot h)) /\
           (forall #a #b (l:hs_lens a b) h. {:pattern view l h}
             view l h == l.l.get h))
  = ()


/// `with_snapshot t pre post`:
///
///    A computation in `LensST` which supports updating the snapshot
///
///    This is a technical device, not intended for typical use in
///    client code, but is useful in libraries that provide support for
///    composing and de-composing hs_lenses.
let with_snapshot #a #b (lens:hs_lens a b) result pre post =
  s:imem (lens.invariant lens.x) ->
  LensST result (snap lens s) pre post

/// `for_n`: A simple for-loop, for i in [0 .. n)
let for_n (#a #b:_) (#lens:hs_lens a b)
          (n:nat)
          (inv: nat -> b -> prop)
          (f: (i:nat{i<n}
              -> LensST unit lens
                (requires fun b -> inv i b)
                (ensures fun b0 _ b1 -> inv (i + 1) b1)))
   : LensST unit lens
     (requires fun b0 -> inv 0 b0)
     (ensures fun b0 _ b1 -> inv n b1)
   = let rec aux (i:nat{i <= n})
       : LensST unit lens
           (inv i)
           (fun _ _ -> inv n)
       = if i = n then ()
         else (f i; aux (i + 1))
     in
     aux 0
