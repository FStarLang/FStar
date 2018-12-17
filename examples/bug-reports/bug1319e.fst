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
module Bug1319e

assume val err (a:Type0) : Type0
assume val return (#a:Type) (x:a) : err a
assume val bind (#a:Type) (#b:Type) (f:err a) (g: a -> Tot (err b)) : Tot (err b)

assume val conv (x:int) : y:nat{y === x} //without the refinement on the result type here everything is fine

[@(expect_failure [54])]
let test (x: err (int * unit)) : Tot (err (nat * unit))
= bind (x) (fun bu ->
  return (conv (fst bu), snd bu))
