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

let char (c:char) : document = failwith not_impl_msg

let string (s:string) : document = failwith not_impl_msg

let substring (s:string) (sofs:int) (len:int) : document = failwith not_impl_msg

let fancystring (s:string) (ofs:int) : document = failwith not_impl_msg

let fancysubstring (s:string) (ofs:int) (len:int) (app_len:int) : document = failwith not_impl_msg

let utf8string (s:string) : document = failwith not_impl_msg

let hardline : document = PPrint.hardline 

let blank (n:int) : document = failwith not_impl_msg

let break_ (n:int) : document = failwith not_impl_msg

let op_Hat_Hat (doc1:document) (doc2:document) : document = failwith not_impl_msg

let nest (j:int) (doc:document) : document = failwith not_impl_msg

let group (doc:document) : document = failwith not_impl_msg

let column (f:int -> document) : document = failwith not_impl_msg

let nesting (f:int -> document) : document = failwith not_impl_msg

let position (f: int -> int ->  int -> document) : document = failwith not_impl_msg

let ifflat (doc1:document) (doc2:document) : document = failwith not_impl_msg

let lparen: document = PPrint.lparen
let rparen: document = PPrint.rparen
let langle: document = PPrint.langle
let rangle: document = PPrint.rangle
let lbrace: document = PPrint.lbrace
let rbrace: document = PPrint.rbrace
let lbracket: document = PPrint.lbracket
let rbracket: document = PPrint.rbracket
let squote: document = PPrint.squote
let dquote: document = PPrint.dquote
let bquote: document = PPrint.bquote
let semi: document = PPrint.semi
let colon: document = PPrint.colon
let comma: document = PPrint.comma
let space: document = PPrint.space
let dot: document = PPrint.dot
let sharp: document = PPrint.sharp
let slash: document = PPrint.slash
let backslash: document = PPrint.backslash
let equals: document = PPrint.equals
let qmark: document = PPrint.qmark
let tilde: document = PPrint.tilde
let at: document = PPrint.at
let percent: document = PPrint.percent
let dollar: document = PPrint.dollar
let caret: document = PPrint.caret
let ampersand: document = PPrint.ampersand
let star: document = PPrint.star
let plus: document = PPrint.plus
let minus: document = PPrint.minus
let underscore: document = PPrint.underscore
let bang: document = PPrint.bang
let bar: document = PPrint.bar

let precede (l:document) (x:document) : document = failwith not_impl_msg

let terminate (r:document) (x:document) : document = failwith not_impl_msg

let enclose (l:document) (r:document) (x:document) : document = failwith not_impl_msg

let squotes (d:document) : document = failwith not_impl_msg
let dquotes (d:document) : document = failwith not_impl_msg
let bquotes (d:document) : document = failwith not_impl_msg
let braces  (d:document) : document = failwith not_impl_msg
let parens  (d:document) : document = failwith not_impl_msg
let angles  (d:document) : document = failwith not_impl_msg
let brackets(d:document) : document = failwith not_impl_msg

let twice (doc:document) : document = failwith not_impl_msg

let repeat (n:int) (doc:document) : document = failwith not_impl_msg

let concat (docs:document list) : document = failwith not_impl_msg

let separate (sep:document) (docs:document list) : document = failwith not_impl_msg

let concat_map (f:('a -> document)) (xs:'a list) : document = failwith not_impl_msg

let separate_map (sep:document) (f:('a -> document)) (xs:'a list) : document = failwith not_impl_msg

let separate2 (sep:document) (last_sep:document) (docs:document list) : document = failwith not_impl_msg

let optional (f:('a -> document)) (opt:'a option) : document = failwith not_impl_msg

let lines (s:string) : document list = failwith not_impl_msg

let arbitrary_string (s:string) : document = failwith not_impl_msg

let words (s:string) : document list = failwith not_impl_msg

let split (ok:(char -> bool)) (s:string) : document list = failwith not_impl_msg

let flow (sep:document) (docs:document list) : document = failwith not_impl_msg

let flow_map (sep:document) (f:('a -> document)) (docs:'a list) : document = failwith not_impl_msg

let url (s:string) : document = failwith not_impl_msg

let align (doc:document) : document = failwith not_impl_msg

let hang (n:int) (doc:document) : document = failwith not_impl_msg

let prefix (n:int) (b:int) (left: document) (right:document) : document = failwith not_impl_msg

let jump (n:int) (b:int) (right:document) : document = failwith not_impl_msg

let infix (n:int) (b:int) (middle:document) (left: document) (right:document) : document = failwith not_impl_msg

let surround (n:int) (b:int) (opening:document) (contents:document) (closing:document) : document = failwith not_impl_msg

let soft_surround (n:int) (b:int) (opening:document) (contents:document) (closing:document) : document = failwith not_impl_msg

let surround_separate (n:int) (b:int) (v:document) (opening:document) (sep:document) (closing:document) (docs:document list) : document = failwith not_impl_msg

let surround_separate_map (n:int) (b:int) (v:document) (opening:document) (sep:document) (closing:document) (f:('a -> document)) (docs:'a list) : document = failwith not_impl_msg

(*
let ( !^ ) (s:string) : document = failwith not_impl_msg

let ( ^/^ ) (x:document) (y:document) : document = failwith not_impl_msg

let ( ^//^ ) (x:document) (y:document) : document = failwith not_impl_msg
*)
