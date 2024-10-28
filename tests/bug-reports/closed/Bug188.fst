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
module Bug188

val test0 : x:(option int){Some? x} -> Tot int
let test0 x = (fun (y:_{Some? y}) -> Some?.v y) x // Works

val test : x:(option int){Some? x} -> Tot int
// GM 2024-10-22: This seems to work now, though I don't think 
// one should rely on it. If this test regresses, maybe just delete it.
let test x = (fun y -> Some?.v y) x
