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
module Bug713

let r = int
let cont (a:Type0) : Type = (a -> M r) -> M r

let return (a:Type0) (x:a) (p : a -> M r) : M r = p x

let bind (a:Type0) (b:Type0)
         (m : cont a) (f : a -> Tot (cont b)) (k : b -> M r) : M r =
         m (fun (x:a) -> let fx = f x in fx k)

reifiable new_effect {
  CONT: Type -> Effect
  with repr = cont
     ; return = return
     ; bind = bind
}
