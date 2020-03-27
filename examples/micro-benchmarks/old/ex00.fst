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
module Ex00

(* Should infer the following type. 
 * Writing it down to confirm. *)
val zero:  x:unit
        -> DST bool (fun ('Post:bool -> heap -> E) (h:heap) -> 
            forall (b:bool). (b=true <==> 0=0) ==> 'Post b h)
let zero (x:unit) = (fun y -> y = 0) 0

