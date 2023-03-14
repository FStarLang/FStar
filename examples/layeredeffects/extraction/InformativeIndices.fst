(*
   Copyright 2008-2023 Microsoft Research

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

module InformativeIndices

/// A negative testcase for indexed effects extraction
/// Since effect has a nat index, it cannot be extracted

type repr (a:Type) (n:nat) = a
let return a x : repr a 1 = x
let bind a b n1 n2 (f:repr a n1) (g:a -> repr b n2) : repr b (n1+n2) = g f
reifiable
reflectable
effect {
  M (a:Type) (n:nat) with {repr;return;bind}
}
let lift_PURE_M (a:Type) (wp:pure_wp a) (f:unit -> PURE a wp)
  : Pure (repr a 1) (requires wp (fun _ -> True)) (ensures fun _ -> True) =
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
  f ()
sub_effect PURE ~> M = lift_PURE_M

let ret (#a:Type) (x:a) : M a 1 = M?.reflect x

let test () : M int 2 =
  let x = ret 1 in
  ret x
