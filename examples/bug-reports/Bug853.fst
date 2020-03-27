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
module Bug853

open FStar.Heap
open FStar.ST

type state =
  | Open
  | Closed

noeq type file = {name: string; state: ref state}

type isClosed file heap = (sel heap file.state) == Closed
type isOpen file heap = (sel heap file.state) == Open

val openHelper : file:file -> ST unit
    (requires (isClosed file))
    (ensures (fun heap s heap' -> isOpen file heap'))
let openHelper file =
    file.state := Open

let file1 () = {
    name = "file1";
    state = alloc Closed;
}

let computeBase () =
    12

let read file =
    13

val readFromFile : file:file -> ST unit
    (requires (isClosed file))
    (ensures (fun heap s heap' -> isClosed file heap'))
let readFromFile file =
    openHelper file;
    let x = computeBase () + read file in
    file.state := Closed

val nil : unit -> St unit
let nil () =
    readFromFile (file1 ())

(* let nil' = nil() *)
