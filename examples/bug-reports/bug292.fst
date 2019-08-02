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
module Bug292

type shared (s:int) = p:(int * int){(fst p) + (snd p) = s}
type shared2 (h:(int * int)) = p:((shared (fst h)) * (shared (snd h)))

val triple_a : unit -> Tot (r:(a:(int*int) & shared2 a) {snd(snd(dsnd r))=0} )
let triple_a () = let r  = (|(0,0),((0,0),(0,0))|) in
                  let r' = (|(0,0),((0,0),(0,0))|) in
(*                   cut(b2t(0=(snd(snd(dsnd r'))))); *)
(*                   cut(b2t(r = r')); *)
                  cut(b2t(0=(snd(snd(dsnd r)))));
                  r
