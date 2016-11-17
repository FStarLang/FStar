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

(*  prettyprint.fst's OCaml implementation is just a thin wrapper around the
    opam pprint package. *)
type document = PPrint.document

let empty = PPrint.empty 

let not_impl_msg = "OCaml prettyprinter not yet implemented"

let document_of_char = PPrint.char 

let document_of_string = PPrint.string 

let substring = PPrint.substring

let fancystring = PPrint.fancystring 

let fancysubstring = PPrint.fancysubstring 

let utf8string = PPrint.utf8string 

let hardline = PPrint.hardline 

let blank = PPrint.blank 

let break_ = PPrint.break 

let op_Hat_Hat = PPrint.(^^) 

let nest = PPrint.nest 

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

let repeat = PPrint.repeat 

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

let hang = PPrint.hang 

let prefix = PPrint.prefix 

let jump = PPrint.jump 

let infix = PPrint.infix 

let surround = PPrint.surround 

let soft_surround = PPrint.soft_surround 

let surround_separate = PPrint.surround_separate 

let surround_separate_map = PPrint.surround_separate_map 
