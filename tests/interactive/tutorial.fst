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
module Tutorial
open FStar.String
open FStar.ST
open FStar.All
//safe-read-write

type filename = string

(* canWrite is a function specifying whether or not a file f can be written *)
let canWrite (f:filename) =
  match f with
    | "demo/tempfile" -> true
    | _ -> false

(* canRead is also a function ... *)
let canRead (f:filename) =
  canWrite f               (* writeable files are also readable *)
  || f="demo/README"       (* and so is this file *)


val read  : f:filename{canRead f}  -> ML string
let read f  = FStar.IO.print_string ("Dummy read of file " ^ f ^ "\n"); f

val write : f:filename{canWrite f} -> string -> ML unit
let write f s = FStar.IO.print_string ("Dummy write of string " ^ s ^ " to file " ^ f ^ "\n")


let passwd  = "demo/password"
let readme  = "demo/README"
let tmp     = "demo/tempfile"


val staticChecking : unit -> ML unit
let staticChecking () =
  let v1 = read tmp in
  let v2 = read readme in
  (* let v3 = read passwd in -- invalid read, fails type-checking *)
  write tmp "hello!"
  (* ; write passwd "junk" -- invalid write , fails type-checking *)


exception InvalidRead
val checkedRead : filename -> ML string
let checkedRead f =
  if canRead f then read f else raise InvalidRead


assume val checkedWrite : filename -> string -> ML unit

// solution here
//
//


let dynamicChecking () =
  let v1 = checkedRead tmp in
  let v2 = checkedRead readme in
  let v3 = checkedRead passwd in (* this raises exception *)
  checkedWrite tmp "hello!";
  checkedWrite passwd "junk" (* this raises exception *)

let main = staticChecking (); dynamicChecking ()
