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
module Bug1362
assume val hoo : nat -> Tot nat

let f0 (b:bool) (n:nat) : Tot nat =
  let b, n = b, n in
  let zz = hoo n in
  let k0, k1 =
    let rec g (m:nat) : Tot (nat * nat) =
       if b then m, m
       else (admit(); g (m - 1))
    in
    g n
  in
  k0 + 1

let f1 (n:nat) =
   hoo (let rec g (m:nat) : nat =
         if m=0 then m
         else g (m - 1)
        in g n)

let f2 (b:bool) (n:nat) : Tot nat =
  let k =
    if b then
      let rec g (m:nat) : Tot nat =
        if b then m
        else (admit(); g (m - 1))
      in
      g n
    else 0
  in
  k + 1

let f3 (n:int) : Ghost int (requires True) (ensures (fun i -> i == 0)) =
  let k =
    let rec g (i:int) : Ghost int
      (requires True)
      (ensures (fun j -> j == 0)) = 0
    in
    g n
  in k


let f4 (n:int) : Ghost int (requires n >= 0) (ensures (fun i -> i == 0)) =
  let k =
    let rec g (i:int) : Ghost int
      (requires i >= 0)
      (ensures (fun j -> j == 0)) =
      if i = 0 then 0
      else g (i - 1)
    in
    g n
  in k
