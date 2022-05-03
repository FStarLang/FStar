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

total
reflectable
layered_effect {
  NDS : a:Type -> st:Type0 -> Effect
  with
  repr = nds;
  return = return;
  bind = bind
}

/// Reading the state
let get #s ()
  : NDS s s
  = NDS?.reflect (fun t n s -> s, s, n)

/// Writing the state
let put #s (x:s)
  : NDS unit s
  = NDS?.reflect (fun t n _ -> (), x, n)

/// Sampling a boolean
let sample #s ()
  : NDS bool s
  = NDS?.reflect (fun t n s -> t n, s, n + 1)

let lift_pure_nds a s wp (f : eqtype_as_type unit -> PURE a wp)
  : Pure (nds a s)
         (requires wp (fun _ -> True))
         (ensures fun _ -> True)
  = fun t n s -> f (), s, n

sub_effect PURE ~> NDS = lift_pure_nds
