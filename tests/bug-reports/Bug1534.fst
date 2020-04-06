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
module Bug1534

type ok (a:int) = | Mkok : b:int -> ok a

type ok2 (a:int) : eqtype = | Mkok2 : b:int -> ok2 a

type ok3 (a:int) : bool -> Type = | Mkok3 : b:int -> ok3 a true

[@(expect_failure [313])]
type bad (a:int) = | Mkbad : a:int -> bad a

[@(expect_failure [313])]
type bad2 (a:int) : eqtype = | Mkbad2 : a:int -> ok2 a

[@(expect_failure [313])]
type bad3 (a:int) : bool -> Type = | Mkbad3 : a:int -> bad3 a true

(* Sanity check that this works with implicits *)
type eq' (#a:Type) : a -> a -> Type =
    | Refl' : x:a -> eq' x x

[@(expect_failure [313])]
type eq'bad (#a:Type) : a -> a -> Type =
    | Refl'bad : a:Type -> x:a -> eq'bad x x
