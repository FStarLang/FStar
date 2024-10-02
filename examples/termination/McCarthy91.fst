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
module McCarthy91

let f91_ (x:nat) : nat = if x <= 100 then 91 else x - 10

open FStar.Mul
let rec f91 (x:nat) : Pure nat (requires True)
  (ensures (fun r -> r = f91_ x))
  (decreases (112 - x )) =
if x <= 100 then f91 (f91 (x + 11)) else x - 10
