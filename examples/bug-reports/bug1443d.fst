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
module Bug1443d

noeq type ins 'ins_typ = {
  eval_ins : 'ins_typ -> unit;
  ins_to_string : 'int_typ -> string
}

noeq type add64 't1 't2 = {
  dst: 't1;
  src: 't2
}

assume val eval_add64 : add64 't1 't2 ->  unit

assume val add64_to_string : add64 't1 't2 -> string

[@(expect_failure [66])]
let add64_ins (#t1:Type)(#t2:Type) : ins (add64 t1 t2) = {
  eval_ins = eval_add64;
  ins_to_string = add64_to_string
}
