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
module Bug293

val test : (a:int & b:int{a=b}) ->(unit*unit) -> Tot unit
let test (|a, b|) ((),()) =  assert(a = b)

(* This term in elaborated form is
let test x y =
  match x, t with
  | (|a, b|) ((),()) -> assert(a = b)


The equality in the body introduces two flex-flex subtyping constraints

   ?u_a   <: ?t
   ?u_b a <: ?t

If we solve these constraints in isolation, e.g., when closing the match,
then we set (?u_b a = ?u_a) rather than ?u_b a = fun a -> b:int{a=b}

And the program fails to verify
*)
