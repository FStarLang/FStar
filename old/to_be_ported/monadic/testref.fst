(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
module TestRef
type nat = i:int{(GT i 0)}
type arr :: * => *
type sparse_set_shape = {dense : arr nat}
logic function ArrSel : int -> arr 'a -> 'a
type foo = r:sparse_set_shape{(0 = ((ArrSel<nat> 1 r.dense) : int))}

(* logic function SizeOf : int -> nat *)
(* val init: 'Post::(unit => heap => E) *)
(*        -> x:t  *)
(*        -> ST (fun (H:heap) => ((SizeOf x)=(SizeOf x))) *)
(*               unit *)
(*              'Post *)
