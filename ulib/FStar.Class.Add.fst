(*
   Copyright 2008-2023 Microsoft Research

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
module FStar.Class.Add

(* A class for (additive, whatever that means) monoids *)
class additive a = {
  zero       : a;
  plus       : a -> a -> a;
}

val (++) : #a:_ -> {| additive a |} -> a -> a -> a
let (++) = plus

instance add_int : additive int = {
  zero = 0;
  plus = (+);
}

instance add_bool : additive bool = {
  zero = false;
  plus = ( || );
}

instance add_list #a : additive (list a) = {
  zero = [];
  plus = List.Tot.Base.append;
}
