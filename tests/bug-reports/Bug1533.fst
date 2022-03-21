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
module Bug1533

let elim a b (x:a) (y:b) : Lemma (requires (x === y)) (ensures (x == y)) = ()

let elim2 (a b:Type0) (x:a) (y:b) : Lemma (requires (x === y)) (ensures (a == b)) = ()

let coerce #a (#b:Type{b == a}) (x:a) : y:b{y === x} = x

[@@expect_failure]
let _ =
  elim2 nat int 1 1;
  assert (nat == int);
  let x : nat = coerce #int #nat (-1) in
  assert False
