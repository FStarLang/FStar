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
module Ex16

type rint = ref int
type rrec = {a:rint; b:rint}
type gtrec = r:rrec{(fun (h:heap) => ((fun (a:int) (b:int) => LT a b) (Select r.a h) (Select r.b h)))}

(* Cause of failure: Tc.kinding chokes on the type
 * 'Post::(Ex16.gtrec => (heap => E)) -> 
 * r1:Ex16.rint -> 
 * r2:this:Ex16.rint{(fun (h:heap) => LT (Select r1 h) (Select this h))} ->
 * ST ((fun (h:heap) => 'Post { Ex16.a=r1, Ex16.b=r2 } (Update r2 2 (Update r1 1 h)))) Ex16.gtrec 'Post
 *)

val foo : 'Post::(gtrec => heap => E)
      -> r1:rint
      -> r2:rint{(fun (h:heap) => ((fun (m:int) (n:int) => (LT m n)) (Select r1 h) (Select r2 h)))}
      -> ST (fun (h:heap) => ('Post ({a=r1;b=r2}) (Update r2 2 (Update r1 1 h))))
            gtrec
            'Post
let foo m n =
  if n > m then 
    m := 1;
    n := 2;
    {a=m; b=n}
  else
    m := 2;
    n := 1;
    {a=m; b=n}

