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
#light "off"
module FStar.Indent
open FStar.ST
open FStar.All

open FStar.Util
open FStar.Parser.ToDocument

module D = FStar.Parser.Driver
module P = FStar.Pprint

let generate filenames =
    let parse_and_indent filename =
        let modul, comments = D.parse_file filename in
        // P.pretty_out_channel (float_of_string "1.0") 100 (comments_to_document comments) stdout ;
        let leftover_comments =
            let comments = List.rev comments in
            let doc, comments = modul_with_comments_to_document modul comments in
                            (* TODO : some problem with the F# generated floats *)
            P.pretty_out_channel (float_of_string "1.0") 100 doc stdout ;
            comments
        in
        (* TODO : We could setup the leftover comments a little more nicely *)
        let left_over_doc =
           P.concat  [P.hardline ; P.hardline ; comments_to_document leftover_comments]
        in
        P.pretty_out_channel (float_of_string "1.0") 100 left_over_doc stdout
    in List.iter parse_and_indent filenames
