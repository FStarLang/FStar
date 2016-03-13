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
module Ex15

type nat = i:int{0 <= i}

(* TODO: build logical operators that work on nats, so we can use nats
 *       in the pre-condition.
 *)

val inc : n:nat
  -> DST int (fun ('Post::int => heap => E) (h:heap) =>
      (forall (y:nat). (y=(n + 1)) => 'Post y h))
let inc n = n + 1

