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

module ParametricST

/// This module defined a state effect parametric in the type of state.
/// It is used as a testcase for extraction of indexed effects

type repr (a:Type) (s:Type0) = s -> a & s
let return a x s : repr a s = fun s -> x, s
let bind a b s (f:repr a s) (g:a -> repr b s) : repr b s =
  fun s ->
  let x, s = f s in
  (g x) s
reifiable
reflectable
effect {
  ST (a:Type) ([@@@ effect_param] s:Type0) with {repr;return;bind}
}
let lift_PURE_ST a wp s (f:unit -> PURE a wp)
  : Pure (repr a s) (requires wp (fun _ -> True)) (ensures fun _ -> True) =

  fun s -> f (), s
sub_effect PURE ~> ST = lift_PURE_ST

let get #s () : ST s s = ST?.reflect (fun s -> s, s)
let put #s (v:s) : ST unit s = ST?.reflect (fun _ -> (), v)
let incr () : ST unit int =
  let n = get () in
  put (n+1)

let main =
  let _, n = reify (incr ()) 1 in
  let f = reify (let n = get () in put (n+2)) in
  let _, n = f n in
  FStar.IO.print_string (FStar.Printf.sprintf "Output: %d\n" n)
