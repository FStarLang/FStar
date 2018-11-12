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
module Map.OpaqueToSMT.Test
open Map.OpaqueToSMT
let imap = map int string
let upd (n:imap) (k:int) (v:string) = upd n k v
let sel (n:imap) (k:int) = sel n k

#reset-options "--hint_info --log_queries --initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0" 
//expect no Z3 query
let test1 (m:imap) =
  let n = upd (upd m 0 "hello") 1 "goodbye" in
  assert_norm (sel n 0 == "hello")

//expect a Z3 query for just `m 2 = "world"`
let test2 (m:imap) =
  assume (sel m 2 == "world");
  assert_norm (sel m 2 == m 2); //need this because after normalization the query below becomes `m 2 = "world"`
  let n = upd (upd m 0 "hello") 1 "goodbye" in
  assert_norm (sel n 2 == "world")
