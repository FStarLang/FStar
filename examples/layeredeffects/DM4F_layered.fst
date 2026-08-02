(*
   Copyright 2008-2018 Microsoft Research

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

module DM4F_layered

(* This used to be the same DM4F state example layered over a layered PURE.
   The layered encoding has been removed; the example is now the same plain
   state monad as DM4F. *)

open DM4F_Utils

type repr (a:Type u#ua) (st:Type0) : Type u#ua =
  s0:st -> Pure (a & st)

let return (#a:Type) (#st:Type0) (x:a) : repr a st =
  fun s0 -> (x, s0)

let bind (#a #b:Type) (#st:Type0)
  (c : repr a st)
  (f : a -> repr b st)
: repr b st
= fun s0 ->
    let (y, s1) = c s0 in
    f y s1

let (let!) (#a #b:Type) (#st:Type0) (c : repr a st) (f : a -> repr b st) : repr b st =
  bind c f

let run (#a:Type) (#st:Type0) (c:repr a st) (s0:st) : Pure (a & st) =
  c s0

let get #st () : repr st st =
  fun s0 -> (s0, s0)

let put #st (s:st) : repr unit st =
  fun _ -> ((), s)

let test () : repr int int =
  let! x = get () in
  let! _ = put (x + x) in
  let! y = get () in
  let! z = get () in
  return (y + z)
