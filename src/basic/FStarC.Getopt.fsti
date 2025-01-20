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
module FStarC.Getopt
open FStarC.Effect
open FStarC.BaseTypes

val noshort : char
val nolong : string
type opt_variant 'a =
  | ZeroArgs of (unit -> 'a)
  | OneArg of (string -> 'a) & string

type opt' 'a = char & string & opt_variant 'a
type opt = opt' unit

type parse_cmdline_res =
  | Empty
  | Help
  | Error of (string & string) // second arg is the long name of the failed option
  | Success

val parse_cmdline: list opt -> (string -> parse_cmdline_res) -> parse_cmdline_res
val parse_string: list opt -> (string -> parse_cmdline_res) -> string -> parse_cmdline_res
val parse_list: list opt -> (string -> parse_cmdline_res) -> list string -> parse_cmdline_res
val cmdline: unit -> list string
