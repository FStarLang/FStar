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

module AddTwo
open Compose
open Twice

type IncrPre :: _ = 
    (fun (x:ref int) (z:unit) ('Post::unit => heap => E) (h:heap) => 
        'Post () (Update x (Add (Select x h) 1) h))

val incr: x:ref int 
        -> z:unit 
        -> DST unit (IncrPre x z)
let incr x (z:unit) = let y = !x in x := (y + 1)

val addTwo :  x:ref int
           -> DST unit (fun ('Post::unit => heap => E) h =>
               (forall u h'. (Select x h' = (Add (Select x h) 2))
                   ==> 'Post u h'))
let addTwo x = 
  compose (fun () -> incr x ()) (fun () -> incr x ()) ()
      
end 
