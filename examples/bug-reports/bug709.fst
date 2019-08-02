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
module Bug709

let st (s:Type) (a:Type) = s -> M (a * s)

let return_st (s:Type) (a:Type) (x:a) : st s a = fun s0 -> x, s0

let bind_st (s:Type) (a:Type) (b:Type)
            (f:st s a) (g:a -> Tot (st s b)) : st s b =
  fun s0 -> let x, s1 = f s0 in g x s1

new_effect {
  STATE (s:Type) : a:Type -> Effect
  with repr     = st s
     ; bind     = bind_st s
     ; return   = return_st s
}
