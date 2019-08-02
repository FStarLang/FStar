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
module Bug092

type t (a:Type{hasEq a}) = a -> a -> Tot a

type f_type (a:Type{hasEq a}) = r:t a{ forall x y. r x y = r y x }

assume val f : #a:Type{hasEq a} -> Tot (f_type a)

val f2 : a:Type{hasEq a} -> a -> Tot a
let f2 x = f x x
