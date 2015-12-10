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
module FStar.String

let split (chars:list<char>) s = String.split chars s
let strcat s1 s2 = s1 ^ s2
let concat (s:string) (ts:list<string>) = String.concat s ts
let compare s1 s2 = String.compare s1 s2
let strlen s = String.length s
let length s = String.length s
let collect f s = String.collect f s
let lowercase s = String.lowercase s

(* may fail with index out of bounds *)
let substring s i j = String.sub s i j
let get s i = String.get s i



