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
#light "off"

module FStar.Pprint
open Prims
open FSharp.Compatibility.OCaml
open FSharp.PPrint
open FStar.BaseTypes
module P = FSharp.PPrint.Engine
module C = FSharp.PPrint.Combinators

type document = P.document

let empty : document = P.empty

let doc_of_char (c:char) : document = P.char c
let doc_of_string (s:string) : document = P.string s
let doc_of_bool (b:bool) : document = P.string (string_of_bool b)

let substring (s:string) (sofs:int) (len:int) : document = P.substring s sofs len

let fancystring (s:string) (ofs:int) : document = P.fancystring s ofs

let fancysubstring (s:string) (ofs:int) (len:int) (app_len:int) : document = P.fancysubstring s ofs len app_len

let utf8string (s:string) : document = P.utf8string s

let hardline : document = P.hardline

let blank (n:int) : document = P.blank n

let break_ (n:int) : document = P.break_ n

let (^^) (doc1:document) (doc2:document) : document = C.concat [doc1; doc2]
let (^/^) (doc1:document) (doc2:document) : document = C.concat [doc1; P.break_ 1; doc2]

let nest (j:int) (doc:document) : document = P.nest j doc

let group (doc:document) : document = P.group doc

let ifflat (doc1:document) (doc2:document) : document = P.ifflat doc1 doc2

let align (doc:document) : document = P.align doc

let lparen: document = C.lparen
let rparen : document = C.rparen
let langle : document = C.langle
let rangle : document = C.rangle
let lbrace : document = C.lbrace
let rbrace : document = C.rbrace
let lbracket : document = C.lbracket
let rbracket : document = C.rbracket
let squote : document = C.squote
let dquote : document = C.dquote
let bquote : document = C.bquote
let semi : document = C.semi
let colon : document = C.colon
let comma : document = C.comma
let space : document = C.space
let dot : document = C.dot
let sharp : document = C.sharp
let slash : document = C.slash
let backslash : document = C.backslash
let equals : document = C.equals
let qmark : document = C.qmark
let tilde : document = C.tilde
let at : document = C.at
let percent : document = C.percent
let dollar : document = C.dollar
let caret : document = C.caret
let ampersand : document = C.ampersand
let star : document = C.star
let plus : document = C.plus
let minus : document = C.minus
let underscore : document = C.underscore
let bang : document = C.bang
let bar : document = C.bar
let long_left_arrow : document = P.string "<--"
let larrow : document = P.string "<-"
let rarrow : document = P.string "->"

let precede (l:document) (x:document) : document = C.precede l x

let terminate (r:document) (x:document) : document = C.terminate r x

let enclose (l:document) (r:document) (x:document) : document = C.enclose l r x

let squotes (d)  = C.squotes d
let dquotes (d)  = C.dquotes (d)
let bquotes (d)  = C.bquotes (d)
let braces  (d)  = C.braces  (d)
let parens  (d)  = C.parens  (d)
let angles  (d)  = C.angles  (d)
let brackets(d)  = C.brackets(d)

let twice (doc)  = C.twice (doc)

let repeat (n:int) (doc)  = C.repeat (n:int) (doc)

let concat docs  = C.concat docs

let separate (sep) (docs)  = C.separate (sep) (docs)

let concat_map (f:('a -> document)) (xs:'a list)  = C.concat_map (f:('a -> document)) (xs:'a list)

let separate_map (sep) (f:('a -> document)) (xs:'a list)  = C.separate_map (sep) (f:('a -> document)) (xs:'a list)

let separate2 (sep) (last_sep) (docs)  = C.separate2 (sep) (last_sep) (docs)

let optional (f:('a -> document)) (opt:'a option)  = C.optional (f:('a -> document)) (opt:'a option)

let lines (s:string) = C.lines s

let arbitrary_string (s:string)  = C.arbitrary_string (s:string)

let words (s:string) = C.words s

let split (ok:(char -> bool)) (s:string) = C.split ok s

let flow (sep) (docs)  = C.flow (sep) (docs)

let flow_map (sep) (f:('a -> document)) (docs:'a list)  = C.flow_map (sep) (f:('a -> document)) (docs:'a list)

let url (s:string)  = C.url (s:string)

let hang (n:int) (doc)  = C.hang (n:int) (doc)

let prefix (n:int) (b:int) (left) (right)  = C.prefix (n:int) (b:int) (left) (right)

let jump (n:int) (b:int) (right)  = C.jump (n:int) (b:int) (right)

let infix (n:int) (b:int) (middle) (left) (right)  = C.infix (n:int) (b:int) (middle) (left) (right)

let surround (n:int) (b:int) (opening) (contents) (closing)  = C.surround (n:int) (b:int) (opening) (contents) (closing)

let soft_surround (n:int) (b:int) (opening) (contents) (closing)  = C.soft_surround (n:int) (b:int) (opening) (contents) (closing)

let surround_separate (n:int) (b:int) (v) (opening) (sep) (closing) (docs) =
    C.surround_separate (n:int) (b:int) (v) (opening) (sep) (closing) (docs)

let surround_separate_map (n:int) (b:int) (v) (opening) (sep) (closing) (f:('a -> document)) (docs:'a list)  = C.surround_separate_map (n:int) (b:int) (v) (opening) (sep) (closing) (f:('a -> document)) (docs:'a list)

(* Wrap up ToChannel.pretty *)
let pretty_out_channel rfrac width doc ch =
    P.ToChannel.pretty rfrac width ch doc;
    flush ch

(* Wrap up ToBuffer.pretty *)
let pretty_string rfrac width doc =
    let ch = new System.IO.StringWriter() in
    pretty_out_channel rfrac width doc ch;
    ch.ToString()
