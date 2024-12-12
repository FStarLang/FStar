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
module TestSeq

open FStar
open FStar.IO
open FStar.All

val print_seq : s:Seq.seq int -> i:nat{i <= Seq.length s} -> ML unit
let rec print_seq s i = 
  if i = Seq.length s then ()
  else (print_string (string_of_int (Seq.index s i)); 
        print_string "\n";
        print_seq s (i + 1))

let main =
  let id i = i in
  let s = Seq.init 10 id in
  print_seq s 0
