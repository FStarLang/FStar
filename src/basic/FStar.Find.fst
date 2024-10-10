(*
   Copyright 2008-2024 Microsoft Research

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
module FStar.Find

open FStar
open FStar.Compiler.List
module BU = FStar.Compiler.Util

let find_file =
  let file_map = BU.smap_create 100 in
  fun filename ->
     match BU.smap_try_find file_map filename with
     | Some f -> f
     | None ->
       let result =
          (try
              if BU.is_path_absolute filename then
                if BU.file_exists filename then
                  Some filename
                else
                  None
              else
                (* In reverse, because the last directory has the highest precedence. *)
                BU.find_map (List.rev (Options.include_path ())) (fun p ->
                  let path =
                    if p = "." then filename
                    else BU.join_paths p filename in
                  if BU.file_exists path then
                    Some path
                  else
                    None)
           with | _ -> //to deal with issues like passing bogus strings as paths like " input"
                  None)
       in
       if Some? result
       then BU.smap_add file_map filename result;
       result
