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
module FStar.IO
exception EOF
open System
open System.IO
type fd_read  = TextReader
type fd_write = TextWriter

let print_newline _ = Printf.printf "\n"
let print_string x   = Printf.printf "%s" x
let print_uint8 x    = Printf.printf "%.02x" x
let print_uint32 x    = Printf.printf "%.04x" x
let print_uint64 x    = Printf.printf "%.08x" x
let print_any x      = Printf.printf "%A" x
let input_line ()    = System.Console.ReadLine()
let input_int  ()    = Int32.Parse(System.Console.ReadLine())
let input_float ()   = Single.Parse(System.Console.ReadLine(), System.Globalization.CultureInfo.InvariantCulture);
let open_read_file (x:string)  = new StreamReader(x)
let open_write_file (x:string) = File.CreateText(x)
let close_read_file (x:fd_read)   = x.Close()
let close_write_file (x:fd_write) = x.Close()
let read_line (fd:fd_read)     =
    let x = fd.ReadLine() in
    if x=null
    then raise EOF
    else x
let write_string (fd:fd_write) (x:string) =
    fd.Write(x)
