(*
   Copyright 2024 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: Brian G. Milnes
*)

///  A file descriptor for a string file, useful for test.
module FStar.FDString

open FStar.List.Tot
open FStar.All 

type fd_string : eqtype = list string
type fd_string_read  = fd_string
type fd_string_write = fd_string 

let open_read_file  () = []
let open_write_file () = []
let close_read_file  fdsr = ()
let close_write_file fdsw = ()

let print_newline  fdsw  = "\n"::fdsw
let print_string   fdsw s = s::fdsw

let input_line     fdsr = 
 match fdsr with
 | []  -> raise FStar.IO.EOF
 | h::t -> (h,t)

let read_line      fdsr =
 match fdsr with
 | []  -> raise FStar.IO.EOF
 | h::t -> (h,t)

let write_string   fdsw s = s::fdsw

let fd_write_to_fd_read fdsw = rev fdsw

let fd_write_to_string fdsw =
 let fdsr = fd_write_to_fd_read fdsw in
  fold_right (^) (rev fdsw) ""

