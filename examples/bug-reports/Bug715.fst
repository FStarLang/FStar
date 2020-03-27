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
module Bug715

let cont (a:Type0) = (a -> M Type0) -> M Type0

let return (a:Type0) (x:a) : cont a = fun (p : a -> M Type0) -> p x

let bind (a:Type0) (b:Type0)
         (m : cont a) (f : a -> Tot (cont b)) (k : b -> M Type0) : M Type0 =
  (* m (fun (x:a) -> f x k) -- This variant causes:
    unknown(0,0-0,0) : Error
    Variable "uu___#2279" not found
  *)
  let mm : cont a = m in mm (fun (x:a) -> let fx : cont b = f x in fx k)

reifiable new_effect {
  CONT: Type -> Effect
  with repr = cont
     ; return = return
     ; bind = bind
}

(*
[hritcu@detained bug-reports]$ fstar.exe bug.fst
Error: Unexpected error; please file a bug report, ideally with a minimized version of the source program that triggered the error.
Invalid_argument("map2: Different_list_size")
*)
