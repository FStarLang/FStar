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
#light "off"
module FStar.Parser.ParseIt
open FStar.ST
open FStar.All
open FStar.Parser
open FStar.Util
open FStar
open FStar.Errors

type filename = string

type input_frag = {
    frag_fname:filename;
    frag_text:string;
    frag_line:int;
    frag_col:int
}

val read_vfs_entry : string -> option<(time * string)>
// This lets the ide tell us about edits not (yet) reflected on disk.
val add_vfs_entry: fname:string -> contents:string -> unit
// This reads mtimes from the VFS as well
val get_file_last_modification_time: fname:string -> time

type parse_frag =
    | Filename of filename
    | Toplevel of input_frag
    | Fragment of input_frag

type parse_result =
    | ASTFragment of (AST.inputFragment * list<(string * Range.range)>)
    | Term of AST.term
    | ParseError of (Errors.raw_error * string * Range.range)

val parse: parse_frag -> parse_result // either<(AST.inputFragment * list<(string * Range.range)>) , (string * Range.range)>
val find_file: string -> string

val parse_warn_error: string -> list<FStar.Options.error_flag>
