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

type myrec = {a:int; b:int}
type gtrec = r:myrec{LT r.a r.b}

val foo : m:int
      -> n:int{LT m n}
      -> DST myrec (fun ('Post::myrec => heap => E) => ('Post ({a=1;b=2})))
let foo m n =
  if n > m then 
    {a=1; b=2}
  else
    {a=2; b=1}

