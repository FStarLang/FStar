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
module Bug1187

let st (s:Type) (a:Type) = s -> M (a * s)

let return_st (s:Type) (a:Type) (x:a) : st s a = fun s0 -> x, s0
let bind_st (s:Type) (a:Type) (b:Type) (f:st s a) (g:a -> st s b) : st s b
  = fun (s0:s) -> let (x,s) = f s0 in g x s //<: M (b * s)

let get (s:Type) () : st s s = fun s0 -> s0, s0
let put (s:Type) (x:s) : st s unit = fun _ -> (), x

total reifiable reflectable new_effect {
  STATE_h (s:Type0) : a:Type -> Effect
  with repr     = st s
     ; bind     = bind_st s
     ; return   = return_st s
     ; get      = get s
     ; put      = put s
}

new_effect DM_ST = STATE_h int

let f : unit -> DM_ST int = 1
