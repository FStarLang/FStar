(*
   Copyright 2025 Microsoft Research

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

(* Just dispatch to FStar.Pprint *)

let doc_of_char        = FStar_Pprint.doc_of_char
let concat_map         = FStar_Pprint.concat_map
let separate_map       = FStar_Pprint.separate_map
let optional           = FStar_Pprint.optional
let split              = FStar_Pprint.split
let flow_map           = FStar_Pprint.flow_map
let pretty_string      = FStar_Pprint.pretty_string
let pretty_out_channel = FStar_Pprint.pretty_out_channel
