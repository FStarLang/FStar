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
module LocalState

open FStar.Tactics.V2

type st1 = {
  x : int;
  y : int;
}

type st2 = int -> int

[@@ plugin]
let t2 () : Tac unit = fail "always fail"

[@@ plugin]
let t1 (_:unit) : Tac unit =
  let r1 = alloc {x = 1; y = 1} in
  let r2 = alloc #st2 (fun x -> x + 1) in
  let s1 = read r1 in
  let s2 = read r2 in
  let s = s1.x + s1.y + s2 1 in
  if s <> 4 then fail "Expected 4"
  else let _ = write r1 ({x = 2; y = 2}) in
       let _ = write r2 (fun x -> x + 2) in
       let s1 = read r1 in
       let s2 = read r2 in
       let s = s1.x + s1.y + s2 1 in
       if s <> 7 then fail "Expected 7"
       else try
              let _ = write r1 ({x=3; y=3}) in
              t2 ()
            with
              | _ ->
                let s1 = read r1 in
                let s = s1.x + s1.y in
                if s <> 6 then fail "Expected 6"
                else ()
