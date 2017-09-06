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

type filename = string

type input_frag = {
    frag_text:string;
    frag_line:int;
    frag_col:int
}

val parse: either<filename, input_frag> -> either<(AST.inputFragment * list<(string * Range.range)>) , (string * Range.range)>
val find_file: string -> string
