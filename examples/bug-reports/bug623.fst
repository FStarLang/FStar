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
module Bug623

open FStar.All

val null: unit -> All unit
  (requires (fun h -> True))
  (ensures  (fun h r h' -> True))
let null () = ()

(* Fails *)
(* let test0 = assert(false); null () *)

(* Succeeds *)
let test1 () = assert(false); null ()

(* Succeeds *)
let test2 (u:unit) = assert(false); null ()

(* Fails *)
(* let test3 (u:unit) : All unit (requires (fun h -> True)) (ensures (fun h r h' -> True)) = assert(false); null() *)

(* Succeeds *)
let test3' () : All unit (requires (fun h -> True)) (ensures (fun h r h' -> True)) = assert(false); null()

(* Succeeds *)
let test4 (u:unit) : ML unit = assert(false); null()

(* Fails *)
(* let test5 (u:unit) : ML unit = assert(false) *)

val null2: unit -> Div unit
  (requires (True))
  (ensures  (fun r -> True))
let null2 () = ()

(* Succeeds *)
let test6 (u:unit) : ML unit = assert(false); null2()

val null3: unit -> Pure unit
  (requires (True))
  (ensures  (fun r -> True))
let null3 () = ()

(* Fails *)
let test7 (u:unit) : ML unit = assert(false); null3()
