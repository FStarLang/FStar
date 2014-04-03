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
module Compose

val compose: 'a::* -> 'b::* -> 'c::*
          -> 'Tx1::'a => ('b => heap => E) => heap => E
          -> 'Tx2::'b => ('c => heap => E) => heap => E
          -> f:(x:'a -> DST 'b ('Tx1 x))
          -> g:(y:'b -> DST 'c ('Tx2 y))
          -> x:'a
          -> DST 'c (fun ('Post::'c => heap => E) => ('Tx1 x (fun (y:'b) => 'Tx2 y 'Post)))
let compose ('a::*) ('b::*) ('c::*) ('Tx1::'a => ('b => heap => E) => heap => E) ('Tx2::'b => ('c => heap => E) => heap => E)
    (f:(x:'a -> DST 'b ('Tx1 x)))
    (g:(y:'b -> DST 'c ('Tx2 y)))
    (x:'a) = 
  let y = f x in 
    g y

end 
