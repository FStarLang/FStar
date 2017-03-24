(*
   Copyright 2008-2017 Microsoft Research

   Authors: Aseem Rastogi, Nikhil Swamy, Jonathan Protzenko

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

module FStar.Common
open FStar.All
module BU = FStar.Util

let has_cygpath =
    try
        let _, t_out, _ = BU.run_proc "which" "cygpath" "" in
        BU.trim_string t_out = "/usr/bin/cygpath"
    with
    | _ -> false

//try to convert filename passed from the editor to mixed path
//that works on both cygwin and native windows
//noop if not on cygwin
//on cygwin emacs this is required
let try_convert_file_name_to_mixed (s:string) : string =
    if has_cygpath
    then let _, t_out, _ = BU.run_proc "cygpath" ("-m " ^ s) "" in
         BU.trim_string t_out
    else s
