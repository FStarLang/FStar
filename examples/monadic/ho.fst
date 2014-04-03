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
module AddTwo
open Compose

type IncrPre :: _ = 
    (fun (x:ref int) ('Post::unit => heap => E) (z:unit) (h:heap) => 
        'Post () (Update x (Plus (Select x h) 1) h))

val incr:  'Post::unit => heap => E
        -> x:ref int
        -> unit
        -> ST (IncrPre x 'Post ())
              unit
             'Post

val addTwo : 'Post::unit => heap => E
           -> x:ref int
           -> ST (IncrPre x (IncrPre x 'Post) ()) 
                  unit
                 'Post
let addTwo x = 
  compose<unit, unit, unit, (IncrPre x (IncrPre x 'Post)), (IncrPre x 'Post), 'Post>  (incr x) (incr x) ()

end 

