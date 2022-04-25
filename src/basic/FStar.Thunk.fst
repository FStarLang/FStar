(*
   Copyright 2008-2019 Microsoft Research

   Authors: Aseem Rastogi, Nikhil Swamy, Jonathan Protzenko

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
module FStar.Thunk
open FStar.Pervasives
open FStar.Compiler.Effect
module List = FStar.Compiler.List

let mk (f:unit -> 'a) : thunk 'a = alloc (Inl f)
let mkv (v:'a) : thunk 'a = alloc (Inr v)

let force (t:thunk 'a) =
    match !t with
    | Inr a -> a
    | Inl f ->
      let a = f () in
      t := Inr a;
      a

let map (f : 'a -> 'b) (t:thunk 'a) : thunk 'b =
  mk (fun () -> f (force t))
