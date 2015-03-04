(*
   Copyright 2008-2014 Chantal Keller, Microsoft Research and Inria

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
module Printf_Shallow


assume val string_of_int : int -> Tot string


type directive 'a 'b = (string -> Tot 'a) -> Tot 'b

val seq : directive 'b 'c -> directive 'a 'b -> Tot (directive 'a 'c)
let seq p1 p2 k = p1 (fun v -> p2 (fun w -> k (v^w)))

val s : directive 'a (string -> Tot 'a)
let s k = k

val d : directive 'a (int -> Tot 'a)
let d k x = k (string_of_int x)

val l : string -> Tot (directive 'a 'a)
let l s k = k s


(* Replace this with [string -> IO unit] if we were not reaching the
   error [Curried function, but not total] *)
val print_string : string -> Tot string
let print_string s = s

(* Idem, should be [directive unit 'a -> Tot 'a] *)
val printf : directive string 'a -> Tot 'a
let printf f = f print_string


(* Would be transparent with infix syntax for [seq] *)
val ex_dir : directive string (int -> string -> int -> string -> Tot string)
let ex_dir = seq d (seq (l " * ") (seq s (seq (l " = ") (seq d (seq (l " in ") s)))))

(* val test : string *)
(* let test = printf ex_dir 6 "9" 42 "base 13" *)

(* let test2 = assert ((printf ex_dir 6 "9" 42 "base 13") == "6 * 9 = 42 in base 13") *)
