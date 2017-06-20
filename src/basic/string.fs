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
open FSharp.Compatibility.OCaml
let split (chars:list<char>) s = String.split chars s
let strcat s1 s2 = s1 ^ s2
let concat (s:string) (ts:list<string>) = String.concat s ts
let compare s1 s2 = Prims.of_int (String.compare s1 s2)
let strlen s = Prims.of_int (String.length s)
let length s = Prims.of_int (String.length s)
let collect f s = String.collect f s
let lowercase s = String.lowercase s

(* may fail with index out of bounds *)
let substring s (i:Prims.int) (j:Prims.int) = String.sub s (Prims.parse_int32(Prims.to_string i)) (Prims.parse_int32(Prims.to_string j))
let get s (i:Prims.int) = String.get s (Prims.parse_int32(Prims.to_string i))

let rec list_of_string (s:string) = [for c in s -> c]
let string_of_list (l:list<char>) = List.fold_right (fun c a -> (string c) ^ a) l ""
