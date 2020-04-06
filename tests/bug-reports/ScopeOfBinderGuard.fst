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
module ScopeOfBinderGuard
let t (z:bool) =
  match z with
  | true -> bool
  | false -> unit
let bool_t = t true

[@expect_failure [19]]
let test1 = fun (b:bool_t) (x:unit{eq2 #unit x b}) -> true
[@expect_failure [19]]
let test2 = fun (b:bool) (x:t false{eq2 #bool x b}) -> true
