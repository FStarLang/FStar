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
#monadic(DST, returnDST, composeDST)
module Ex3

(*
type option :: * => * = 
  | None : 'a::* -> option 'a
  | Some : 'a::* -> 'a -> option 'a
*)

val foo : x:option 'a
       -> DST int (fun ('Post::int => heap => E) (h:heap) =>
           (forall (r:ref (option 'a)). (((Mem r (Domain h))=false) =>
                (forall (y:'a). (x=(Some y)) => 'Post 1 (Update r x h))
                && ((x=None) => 'Post 0 (Update r x h))
                && ('Post -1 (Update r x h)))))
let foo x =
  let r = ref x in
    match !r with
      | Some y -> 1
      | None -> 0
      | _ -> -1

