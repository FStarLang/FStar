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
module Ex04e
//find

type option 'a =  
   | None : option 'a
   | Some : v:'a -> option 'a

let rec find f l = match l with
  | [] -> None
  | hd::tl -> if f hd then Some hd else find f tl

(*
Prove that if `find` returns `Some x` then `f x = true`. 
Is it better to do this intrinsically or extrinsically? Do it both ways.
*)



