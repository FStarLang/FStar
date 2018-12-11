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
module Bug1055b

open FStar.ST

(* this is accepted *)
let write (#a:Type) (r:ref a) = r := 42

(* this fails without --lax *)
// let append_to1 (#a:Type) (xs:list a) = 2 :: xs

(* this works again *)
let append_to2 (#a:Type) (xs:list a) = ignore(alloc 5); 2 :: xs

(* again only lax typable, causes segfault if called *)
val main : unit -> St unit
let main() = let r = alloc "some string" in write r; ignore(!r ^ !r)

(* again only lax typable, causes segfault if called *)
let foo (#a:Type) (x:a) : Tot (option a) = x
let bar = Some?.v (foo 1)
