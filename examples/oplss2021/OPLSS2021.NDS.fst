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
module OPLSS2021.NDS

(** An effect of nondeterminism and state **)

/// An infinite tape of booleans
let tape = nat -> bool

/// The representation of our effect
///    Takes the tape, a curent position on the tape, and an initial state
///    Returns a result, a new position on the tape, and an new state
let nds (a:Type) (s:Type0) =
  tape -> nat -> s -> a & s & nat

let return (a:Type) (x:a) s
  : nds a s
  = fun t n s -> x, s, n

let bind a b s (f:nds a s) (g:a -> nds b s)
  : nds b s
  = fun t n s ->
      let x, s', n' = f t n s in
      g x t n' s'

/// F* used to package such a monad up as an *effect*, indexed by the
/// state type:
///
///   total reflectable effect {
///     NDS (a:Type) ([@@@effect_param] st:Type0) with {repr = nds; return; bind}
///   }
///
/// Effects are now just names, specified by a pre- and a postcondition,
/// and an effect definition (which only guides extraction and
/// reification) may not be indexed.  So we program with `bind` directly;
/// the `let!` notation makes that pleasant.

let ( let! ) (#a #b:Type) (#s:Type0) (f:nds a s) (g:a -> nds b s)
  : nds b s
  = bind a b s f g

/// Reading the state
let get #s ()
  : nds s s
  = fun t n s -> s, s, n

/// Writing the state
let put #s (x:s)
  : nds unit s
  = fun t n _ -> (), x, n

/// Sampling a boolean
let sample #s ()
  : nds bool s
  = fun t n s -> t n, s, n + 1

/// A pure computation is a nondeterministic stateful one that uses
/// neither the tape nor the state
let lift_pure_nds (a:Type) (s:Type0) (f : unit -> a)
  : nds a s
  = fun t n s -> f (), s, n

/// For instance: flip two coins and remember how many came up heads
let flip_twice ()
  : nds unit nat
  = let! b1 = sample () in
    let! b2 = sample () in
    let! n = get () in
    put ((n <: nat) + (if b1 then 1 else 0) + (if b2 then 1 else 0))
