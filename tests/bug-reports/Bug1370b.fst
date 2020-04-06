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
module Bug1370b

[@(expect_failure [316])]
effect Ouch1 (a:Type) = Tot False

[@(expect_failure [316])]
effect Ouch2 (x:int) (a:Type) = Tot a

effect Good3 (a:Type) (x:int) = Tot a

effect Good4 (a:Type) (x:int) = PURE a (fun p -> x > 0 /\ (forall y. p y))

effect Good5 (a:Type) (wp:((a -> Type0) -> Type0)) = PURE a wp
