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

total // Enforce termination of ST programs
reflectable // Allow coercing `st a s` functions to `ST a s` computations
reifiable // Allow coercing `ST a s` computations to `st a s` functions
effect {
  ST (a:Type) (s:Type0)
  with {
  repr = st;      // the underlying representation is `st a s`
  return; // with the return and bind shown above
  bind;
  get;
  put
 }
}

/// Some actions for our new effect

// let g #s : st s s = fun s -> s, s
// /// get: read the current state
// let get #s ()
//   : ST s s
//   = ST?.reflect g

// let p #s x : st unit s = fun _ -> (), x
// /// put: write the current state
// let put #s (x:s)
//   : ST unit s
//   = ST?.reflect (p x)

/// One technicality:
///
/// Pure terms in F* are given the type `pure a wp`
/// where (wp : (a -> prop) -> prop)
/// is a WP transformer for pure computations
///
/// `pure a wp` is the type of a conditionally pure term it is
/// equivalent to `Tot a`, but only when `wp (fun _ -> True)` is
/// provable
let pure a wp = unit -> PURE a wp

/// We need a way to lift such pure computations
/// into our new effect
let lift_pure_st a s wp (f : pure a wp)
  : Pure (st a s)
         (requires wp (fun _ -> True))
         (ensures fun _ -> True)
  = fun s -> f(), s

/// This tells F* how to lift PURE a wp
/// terms to our new effect ST
sub_effect PURE ~> ST = lift_pure_st

/// Now we get to write ST terms in a direct syntax and F* elaborates
/// them internally using the monadic definitions we've given
let test (x:int) : ST int int = 
  let y = ST?.get () in
  ST?.put (x + y);
  y

let incr () : ST unit int = ST?.put (ST?.get() + 1)
/// Now, all that work just to define a plain state monad doesn't seem
/// like adding much beyond plain old do notation
///
/// But, we'll see next how this helps when defining fancier indexed
/// effects
