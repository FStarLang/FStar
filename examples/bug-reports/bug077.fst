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
module Bug077

assume type a
assume type p : a -> Type

val ok : x:a{p x} -> r:a{p r}
let ok x = x

val ok2 : x:a{p x} -> r:(option a){Some? r ==> p (Some?.v r)}
let ok2 x = Some x

val ok3 : x:a{p x} -> option (r:a{p r})
let ok3 x = Some x


assume type b
assume type q : a -> b -> Type

val ok4 : x:a -> y:b{q x y} -> r:(a * b){q (fst r) (snd r)}
let ok4 x y = (x, y)

val ok5 : x:a -> y:b{q x y} -> r:(option (a * b)){Some? r ==> q (fst (Some?.v r)) (snd (Some?.v r))}
let ok5 x y = Some (x, y)

val bug : x:a -> y:b{q x y} -> option (r:(a * b){q (fst r) (snd r)})
let bug x y = Some (x, y)
