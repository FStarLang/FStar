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
module Bug210c

(* Removing the aa argument to acc_inv makes this work. *)
assume val acc_inv : #aa:Type -> a:int -> Tot (e:int{e = a})

val fix_F : a:int -> Tot unit

[@@expect_failure [66]]
let fix_F a = assert (acc_inv a = a)
