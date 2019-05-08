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
module Bug543

type range = r:(int * int) { fst r <= snd r }
type wider (r1:range) (r2:range) = fst r1 <= fst r2 /\ snd r2 <= snd r1
type within (n:int) (r:range) = fst r <= n /\ n <= snd r
type rint (r:range) = n:int {fst r <= n /\ n <= snd r}

let u:range = (0,1)
assume val r : (r:range{wider r u})

val f: n:int {within n u} -> m:int {within m r}
let f n = n

val g: rint u -> rint r

//This fails: (NS: not any more)
let g n = n

//This also works
let g' n = let m:int = n in m
