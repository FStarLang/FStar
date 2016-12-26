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

(*  prettyprint.fsti's OCaml implementation is just a thin wrapper around
    Francois Pottier's pprint package. *)
type document = PPrint.document

let empty = PPrint.empty 

let document_of_char = PPrint.char 

let document_of_string = PPrint.string 

let substring s ofs len = 
    PPrint.substring s (Z.to_int ofs) (Z.to_int len)

let fancystring s apparent_length = 
    PPrint.fancystring s (Z.to_int apparent_length)

let fancysubstring s ofs len apparent_length = 
    PPrint.fancysubstring  s (Z.to_int ofs) (Z.to_int len) (Z.to_int apparent_length)

let utf8string = PPrint.utf8string 

let hardline = PPrint.hardline 

let blank n = PPrint.blank (Z.to_int n)

let break_ n = PPrint.break (Z.to_int n)

let op_Hat_Hat = PPrint.(^^) 

let nest j doc = PPrint.nest (Z.to_int j) doc 

let group = PPrint.group 

let ifflat = PPrint.ifflat 

let align = PPrint.align 

let lparen = PPrint.lparen
let rparen = PPrint.rparen
let langle = PPrint.langle
let rangle = PPrint.rangle
let lbrace = PPrint.lbrace
let rbrace = PPrint.rbrace
let lbracket = PPrint.lbracket
let rbracket = PPrint.rbracket
let squote = PPrint.squote
let dquote = PPrint.dquote
let bquote = PPrint.bquote
let semi = PPrint.semi
let colon = PPrint.colon
let comma = PPrint.comma
let space = PPrint.space
let dot = PPrint.dot
let sharp = PPrint.sharp
let slash = PPrint.slash
let backslash = PPrint.backslash
let equals = PPrint.equals
let qmark = PPrint.qmark
let tilde = PPrint.tilde
let at = PPrint.at
let percent = PPrint.percent
let dollar = PPrint.dollar
let caret  = PPrint.caret
let ampersand = PPrint.ampersand
let star = PPrint.star
let plus = PPrint.plus
let minus = PPrint.minus
let underscore = PPrint.underscore
let bang = PPrint.bang
let bar = PPrint.bar

let precede = PPrint.precede
let terminate = PPrint.terminate 

let enclose = PPrint.enclose 

let squotes = PPrint.squotes
let dquotes = PPrint.dquotes
let bquotes = PPrint.bquotes
let braces  = PPrint.braces
let parens  = PPrint.parens
let angles  = PPrint.angles
let brackets= PPrint.brackets

let twice = PPrint.twice 

let repeat n doc = PPrint.repeat (Z.to_int n) doc

let concat = PPrint.concat 

let separate = PPrint.separate 

let concat_map = PPrint.concat_map 

let separate_map = PPrint.separate_map 

let separate2 = PPrint.separate2 

let optional = PPrint.optional 

let lines = PPrint.lines

let arbitrary_string = PPrint.arbitrary_string 

let words = PPrint.words 

let split = PPrint.split 

let flow = PPrint.flow 

let flow_map = PPrint.flow_map 

let url = PPrint.url 

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
let pretty_string width doc = 
    let buf = Buffer.create 0 in 
    PPrint.ToBuffer.pretty 0.5 (Z.to_int width) buf doc;
    Buffer.contents buf 

(* Wrap up ToChannel.pretty *)
let pretty_out_channel width doc ch = 
    PPrint.ToChannel.pretty 0.5 (Z.to_int width) ch doc;
    flush ch
