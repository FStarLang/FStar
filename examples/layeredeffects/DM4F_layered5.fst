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

module DM4F_layered5

(* This used to be the same DM4F state example layered over ID5, without
   monotonicity.  The layered encoding has been removed; the example is now the
   same plain state monad, keeping the stateful sample programs. *)

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
    let r = c s0 in
    f (fst r) (snd r)

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

let addx (x:int) : repr unit int =
  let! y = get () in
  put (x + y)

let add_via_state (x y : int) : repr int int =
  let! o = get () in
  let! _ = put x in
  let! _ = addx y in
  let! r = get () in
  let! _ = put o in
  return r

#push-options "--warn_error -272" //Warning_TopLevelEffect
let main =
  let r, n = run (add_via_state 1 2) 3 in
  FStar.IO.print_string (FStar.Printf.sprintf "%d:%d\n" r n)
#pop-options
