(*
   Copyright 2008-2026 Microsoft Research

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

(* Section 19.11.  A specification named as an explicit entry point.

   [rep] is a separation-logic predicate: it is a [val] whose result is
   [slprop], it has no runtime content, and its *ghost* index is a recursive
   datatype that the direct-to-C backend cannot lay out.  Naming it as a
   [--custard_entry] used to reach the layout pass and be rejected with error
   367; a specification should be reported as having nothing to extract, not
   as being unrepresentable.

   [tree] is only ever a ghost index -- nothing here holds one at runtime --
   so nothing in the output should mention it either. *)
module PulseSpecRoot
#lang-pulse
open Pulse
module US = FStar.SizeT

noeq
type tree =
  | Leaf
  | Node of tree & tree

(* Declared and defined: the two paths a specification can arrive on. *)
assume val rep_abs (t : tree) (n : US.t) : slprop

let rep (t : tree) (n : US.t) : slprop = pure (US.v n >= 0)

fn size (n : US.t)
  requires pure (US.fits (US.v n + 1))
  returns r : US.t
{
  US.(n +^ 1sz)
}
