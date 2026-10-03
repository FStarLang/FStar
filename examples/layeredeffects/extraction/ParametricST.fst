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

/// This used to test extraction of an effect indexed by the state type.
/// Effect indices no longer exist, so this is now the same state monad
/// specialized to int state and declared with the new reflectable syntax.

#set-options "--warn_error -272" // top-level effect

type repr (a:Type) = int -> a & int
let return (a:Type) (x:a) : repr a = fun s -> x, s
let bind (a b:Type) (f:repr a) (g:a -> repr b) : repr b =
  fun s ->
  let x, s = f s in
  g x s

reifiable
reflectable
effect { ST with {repr; return; bind} }

let lift_PURE_ST (a:Type) (f:unit -> PURE a) : repr a =
  fun s -> f (), s
sub_effect Tot ~> ST = lift_PURE_ST

let get () : ST int = ST?.reflect (fun s -> s, s)
let put (v:int) : ST unit = ST?.reflect (fun _ -> (), v)

let incr () : ST unit =
  let n = get () in
  put (n+1)

let main =
  let _, n = reify (incr ()) 1 in
  let f = reify (let n = get () in put (n+2)) in
  let _, n = f n in
  FStar.IO.print_string (FStar.Printf.sprintf "Output: %d\n" n)
