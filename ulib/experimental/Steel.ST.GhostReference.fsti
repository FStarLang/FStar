(*
   Copyright 2021 Microsoft Research

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
module Steel.ST.GhostReference
open FStar.Ghost
open Steel.ST.Util

(** This module provides a *ghost* reference whose ownership is
    controlled using fractional permissions.

    Most of its functionality is identical to Steel.ST.Reference,
    except it uses the STGhost effect.
*)


/// The main ref type.
///
/// It's in universe zero, so refs can be stored in the heap, you can
/// have [ref (ref a)] etc.
///
/// The type is marked erasable, so [ref a] values are extracted to [()]
[@@ erasable]
val ref (a:Type u#0)
  : Type u#0

/// The main representation predicate
val pts_to (#a:_)
           (r:ref a)
           ([@@@smt_fallback] p:perm)
           ([@@@smt_fallback] v:a)
  : vprop

/// A ref can point to at most one value
val pts_to_injective_eq (#a:_)
                        (#u:_)
                        (#p #q:_)
                        (#v0 #v1:a)
                        (r:ref a)
  : STGhost unit u
      (pts_to r p v0 `star` pts_to r q v1)
      (fun _ -> pts_to r p v0 `star` pts_to r q v0)
      (requires True)
      (ensures fun _ -> v0 == v1)

/// A permission is always no greater than one
val pts_to_perm (#a: _) (#u: _) (#p: _) (#v: _) (r: ref a)
  : STGhost unit u
      (pts_to r p v)
      (fun _ -> pts_to r p v)
      True
      (fun _ -> p `lesser_equal_perm` full_perm)

/// Allocating a ghost reference, with an erased initial value
val alloc (#a:Type)
          (#u:_)
          (x:erased a)
  : STGhostT (ref a) u
      emp
      (fun r -> pts_to r full_perm x)

/// Reading a ghost reference only provides an erased value
val read (#a:Type)
         (#u:_)
         (#p:perm)
         (#v:erased a)
         (r:ref a)
  : STGhost (erased a) u
      (pts_to r p v)
      (fun x -> pts_to r p x)
      (requires True)
      (ensures fun x -> x == v)

/// Updating the contents of a fully owned ghost reference with an
/// erased value
val write (#a:Type)
          (#u:_)
          (#v:erased a)
          (r:ref a)
          (x:erased a)
  : STGhostT unit u
      (pts_to r full_perm v)
      (fun _ -> pts_to r full_perm x)

/// Splitting ownership of a ghost reference
val share (#a:Type)
          (#u:_)
          (#p:perm)
          (#x:erased a)
          (r:ref a)
  : STGhostT unit u
      (pts_to r p x)
      (fun _ -> pts_to r (half_perm p) x `star`
             pts_to r (half_perm p) x)

/// Combining ownership of a ghost reference
///  -- the ensures clause internalizes a use of pts_to_injective_eq
val gather (#a:Type)
           (#u:_)
           (#p0 #p1:perm)
           (#x0 #x1:erased a)
           (r:ref a)
  : STGhost unit u
      (pts_to r p0 x0 `star` pts_to r p1 x1)
      (fun _ -> pts_to r (sum_perm p0 p1) x0)
      (requires True)
      (ensures fun _ -> x0 == x1)

/// Technically, a ghost reference need not be freed (since it is
/// never allocated anyway). But, we provide a free nonetheless. It is
/// equivalent to just dropping the predicate.
val free (#a:Type0)
         (#u:_)
         (#v:erased a)
         (r:ref a)
  : STGhostT unit u
      (pts_to r full_perm v)
      (fun _ -> emp)

/// Executes a code block with a ghost reference temporarily
/// allocated. This function is declared in the `STF` effect so
/// that the pre- and post-resources can be properly inferred by the
/// Steel tactic from the caller's context.
///
/// By virtue of `alloc` and `free` being STGhost
/// functions, `with_local init body` simply extracts as `body _`.
///
/// This combinator is defined only to mirror its Steel.ST.Reference
/// counterpart.
inline_for_extraction
let with_local
  (#t: Type)
  (init: Ghost.erased t)
  (#pre: vprop)
  (#ret_t: Type)
  (#post: ret_t -> vprop)
  (body: (r: ref t) ->
    STT ret_t
    (pts_to r full_perm init `star` pre)
    (fun v -> exists_ (pts_to r full_perm) `star` post v)
  )
: STF ret_t pre post True (fun _ -> True)
= let r = alloc init in
  let v = body r in
  let _ = elim_exists () in
  free r;
  return v
