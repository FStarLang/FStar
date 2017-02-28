(*
   Copyright 2016 Microsoft Research

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

(*  prettyprint's OCaml implementation is just a thin wrapper around
    Francois Pottier's pprint package. *)
include PPrint

let empty = PPrint.empty

let doc_of_char = PPrint.char
let doc_of_string = PPrint.string
let doc_of_bool b = PPrint.string (string_of_bool b)

let substring s ofs len =
    PPrint.substring s (Z.to_int ofs) (Z.to_int len)

let fancystring s apparent_length =
    PPrint.fancystring s (Z.to_int apparent_length)

let fancysubstring s ofs len apparent_length =
    PPrint.fancysubstring  s (Z.to_int ofs) (Z.to_int len) (Z.to_int apparent_length)

let blank n = PPrint.blank (Z.to_int n)

let break_ n = PPrint.break (Z.to_int n)

let op_Hat_Hat = PPrint.(^^)
let op_Hat_Slash_Hat = PPrint.(^/^)

let nest j doc = PPrint.nest (Z.to_int j) doc

let larrow = PPrint.string "<-"
let rarrow = PPrint.string "->"

let repeat n doc = PPrint.repeat (Z.to_int n) doc

let hang n doc = PPrint.hang (Z.to_int n) doc

let prefix n b left right =
    PPrint.prefix (Z.to_int n) (Z.to_int b) left right

let jump n b right =
    PPrint.jump (Z.to_int n) (Z.to_int b) right

let infix n b middle left right =
    PPrint.infix (Z.to_int n) (Z.to_int b) middle left right

let surround n b opening contents closing =
    PPrint.surround (Z.to_int n) (Z.to_int b) opening contents closing

let soft_surround n b opening contents closing =
    PPrint.soft_surround (Z.to_int n) (Z.to_int b) opening contents closing

let surround_separate n b void_ opening sep closing docs =
    PPrint.surround_separate (Z.to_int n) (Z.to_int b) void_ opening sep closing docs

let surround_separate_map n b void_ opening sep closing f xs =
    PPrint.surround_separate_map (Z.to_int n) (Z.to_int b) void_ opening sep closing f xs

(* Wrap up ToBuffer.pretty. *)
let pretty_string rfrac width doc =
    let buf = Buffer.create 0 in
    PPrint.ToBuffer.pretty rfrac (Z.to_int width) buf doc;
    Buffer.contents buf

(* Wrap up ToChannel.pretty *)
let pretty_out_channel rfrac width doc ch =
    PPrint.ToChannel.pretty rfrac (Z.to_int width) ch doc;
    flush ch
