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
module Bug807a

let test1 = 
  let find (#a:Type) (x:nat) (l:list (int * a)) : option (int * a) = admit() in
  find 0 []

let test2 = 
  let find (#a:Type) (l:list a) : option a = admit() in
  find []

assume val id: #a:Type0 -> a -> Tot a
assume val app_id: (#a:Type0 -> a -> Tot a) -> Tot unit
let test3 = app_id id

let test4 = app_id (fun (#a:Type0) -> id #a)
