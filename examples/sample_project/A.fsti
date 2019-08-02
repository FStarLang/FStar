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
module A
open FStar.HyperStack.ST
open FStar.Buffer

val main: 
    argc:Int32.t{Int32.v argc > 0}
  -> argv:Buffer.buffer string{Buffer.length argv == Int32.v argc}
  -> Stack Int32.t 
    (requires (fun h -> True))
    (ensures (fun h _ h' -> True))
