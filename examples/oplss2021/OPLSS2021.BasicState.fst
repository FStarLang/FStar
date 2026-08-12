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
module OPLSS2021.BasicState

(** This example shows how to code up a simple state monad
    and package it as an effect *)

/// `st a s` the type of s-reading/writing computation
///  returning an a
let st (a:Type) (s:Type0) = s -> a & s

/// Promoting a pure `x:a` to an stateful computation
let return (a:Type) (x:a) s
  : st a s
  = fun s -> x, s

/// Sequentially composing two stateful computations
let bind a b s (f:st a s) (g:a -> st b s)
  : st b s
  = fun s ->
      let x, s' = f s in
      g x s'

let get #s () : st s s = fun s -> s, s
let put #s (x:s) : st unit s = fun s -> (), s
// let incr : st unit int = x <-- get; (if x = 0 then put (x + 1) else put x) 
 module F = FStar.FunctionalExtensionality

/// Prove the monad laws, if you like, but F* will not require it
let left_unit a b s (x:a) (f: a -> st b s)
  : Lemma (bind a b s (return _ x _) f `F.feq` f x)
  = ()

let right_unit a s (f:st a s)
  : Lemma (bind a a s f (fun x -> return _ x _) `F.feq` f)
  = ()

let assoc a b c s (f:st a s) (g:a -> st b s) (h:b -> st c s)
  : Lemma (bind _ _ _ (bind _ _ _ f g) h `F.feq`
           bind _ _ _ f (fun x -> bind _ _ _ (g x) h))
  = ()

/// F* used to let you package such a monad up as an *effect*, indexed by
/// the state type, with `get` and `put` as effect actions:
///
///   total reflectable reifiable effect {
///     ST (a:Type) (s:Type0) with { repr = st; return; bind; get; put }
///   }
///
/// Effects are now just names, specified by a pre- and a postcondition.
/// An effect definition survives only to guide extraction and
/// reification, it may not be indexed, and it may only declare `repr`,
/// `return` and `bind` --- there are no actions.
///
/// So we program with `bind` directly.  The `let!` notation makes that
/// pleasant, and it is really all the effect gave us here.

let ( let! ) (#a #b:Type) (#s:Type0) (f:st a s) (g:a -> st b s)
  : st b s
  = bind a b s f g

/// A pure computation is a stateful one that does not touch the state
let lift_pure_st (a:Type) (s:Type0) (f : unit -> a)
  : st a s
  = fun s -> f (), s

/// Now we get to write stateful terms in a direct syntax
let test (x:int) : st int int =
  let! y = get () in
  let! _ = put (x + y) in
  return _ y _

let incr () : st unit int =
  let! x = get () in
  put (x + 1)
