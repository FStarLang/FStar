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
module Microsoft.FStar.Getopt

assume val noshort : char
assume val nolong : string
type opt_variant =
  | ZeroArgs of (unit -> unit)
  | OneArg of (string -> unit) * string

type opt = char * string * opt_variant * string

type parse_cmdline_res =
  | Help
  | Die of string
  | GoOn

assume val parse_cmdline: list<opt> -> (string -> 'a) -> parse_cmdline_res
assume val parse_string: list<opt> -> (string -> 'a) -> string -> parse_cmdline_res
