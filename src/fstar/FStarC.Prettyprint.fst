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

module FStarC.Prettyprint
open FStarC.Effect
open FStarC.List
open FStarC.Util
open FStarC.Parser.ToDocument
module List = FStarC.List
module D = FStarC.Parser.Driver
module P = FStarC.Pprint

let temp_file_name f = Format.fmt1 "%s.print_.fst" f

let generate (m: printing_mode) filenames =
    let parse_and_prettyprint (m: printing_mode) filename =
        let modul, comments = D.parse_file filename in
        let outf =
          match m with
          | FromTempToStdout -> None
          | FromTempToFile ->
            let outf = open_file_for_writing filename in
            Some outf
          | ToTempFile ->
            let outf = open_file_for_writing (temp_file_name filename) in
            Some outf
        in
        let leftover_comments =
            let comments = List.rev comments in
            let doc, comments = modul_with_comments_to_document modul comments in
                            (* TODO : some problem with the F# generated floats *)
            (match outf with
             | Some f -> append_to_file f <| P.pretty_string (float_of_string "1.0") 100 doc
             | None -> P.pretty_out_channel (float_of_string "1.0") 100 doc stdout);
           comments
        in
        let left_over_doc =
          if not (FStarC.List.isEmpty leftover_comments) then
            P.concat  [P.hardline ; P.hardline ; comments_to_document leftover_comments]
          else if m = FromTempToStdout then
            // This isn't needed for FromTempToFile, when using `append_to_file` a newline is added to EoF
            P.concat [P.hardline; P.hardline]
          else
            P.empty
        in
        match outf with
        | None ->
          P.pretty_out_channel (float_of_string "1.0") 100 left_over_doc stdout

        | Some outf ->
          append_to_file outf <| P.pretty_string (float_of_string "1.0") 100 left_over_doc;
          close_out_channel outf
    in
    List.iter (parse_and_prettyprint m) filenames
