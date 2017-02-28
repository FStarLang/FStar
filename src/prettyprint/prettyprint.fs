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

open FSharp.PPrint
open FStar.BaseTypes

// Work-around to get an ADT: 
// Have to rewrap the abstract type, otherwise .NET forces us to expose it in the fsi.
// http://stackoverflow.com/questions/2855735/f-cant-hide-a-type-abbreviation-in-a-signature-why-not
type document = Doc of FSharp.PPrint.Engine.document

let not_impl_msg = "F# prettyprinter function not yet implemented."

let empty : document = Doc FSharp.PPrint.Engine.empty

let doc_of_char (c:char) : document = Doc (FSharp.PPrint.Engine.char c)
let doc_of_string (s:string) : document = Doc (FSharp.PPrint.Engine.string s)
// SI: check there's no bool in F#.PPrint? 
let doc_of_bool (b:bool) : document = 
    Doc (FSharp.PPrint.Engine.string (match b with true -> "true" | _ -> "false"))

let substring (s:string) (sofs:int) (len:int) : document = 
    Doc (FSharp.PPrint.Engine.substring s sofs len)

let fancystring (s:string) (ofs:int) : document = 
    Doc (FSharp.PPrint.Engine.fancystring s ofs)

let fancysubstring (s:string) (ofs:int) (len:int) (app_len:int) : document = 
    Doc (FSharp.PPrint.Engine.fancysubstring s ofs len app_len)

let utf8string (s:string) : document = Doc (FSharp.PPrint.Engine.utf8string s)

let hardline : document = Doc (FSharp.PPrint.Engine.hardline)

let blank (n:int) : document = Doc (FSharp.PPrint.Engine.blank n)

let break_ (n:int) : document = Doc (FSharp.PPrint.Engine.break_ n)

let op_Hat_Hat (Doc doc1:document) (Doc doc2:document) : document = 
    Doc (FSharp.PPrint.Engine.(^^) doc1 doc2)

let op_Hat_Slash_Hat (Doc doc1:document) (Doc doc2:document) : document = 
    Doc (FSharp.PPrint.Combinators.(^/^) doc1 doc2)

let nest (j:int) (Doc doc:document) : document = 
    Doc (FSharp.PPrint.Engine.nest j doc)

let group (Doc doc:document) : document = 
    Doc (FSharp.PPrint.Engine.group doc)

let column (_: int -> document): document = failwith not_impl_msg
let nesting (_: int -> document): document = failwith not_impl_msg
let position (_: int -> int -> int -> document): document = failwith not_impl_msg

let ifflat (Doc doc1:document) (Doc doc2:document) : document = 
    Doc (FSharp.PPrint.Engine.ifflat doc1 doc2) 

let align (Doc doc:document) : document = 
    Doc (FSharp.PPrint.Engine.align doc)

let lparen: document = Doc FSharp.PPrint.Combinators.lparen
let rparen: document = Doc FSharp.PPrint.Combinators.rparen 
let langle: document = Doc FSharp.PPrint.Combinators.langle
let rangle: document = Doc FSharp.PPrint.Combinators.rangle
let lbrace: document = Doc FSharp.PPrint.Combinators.lbrace
let rbrace: document = Doc FSharp.PPrint.Combinators.rbrace
let lbracket: document = Doc FSharp.PPrint.Combinators.lbracket
let rbracket: document = Doc FSharp.PPrint.Combinators.rbracket
let squote: document = Doc FSharp.PPrint.Combinators.squote
let dquote: document = Doc FSharp.PPrint.Combinators.dquote
let bquote: document = Doc FSharp.PPrint.Combinators.bquote
let semi: document = Doc FSharp.PPrint.Combinators.semi
let colon: document = Doc FSharp.PPrint.Combinators.colon
let comma: document = Doc FSharp.PPrint.Combinators.comma
let space: document = Doc FSharp.PPrint.Combinators.space
let dot: document = Doc FSharp.PPrint.Combinators.dot
let sharp: document = Doc FSharp.PPrint.Combinators.sharp
let slash: document = Doc FSharp.PPrint.Combinators.slash
let backslash: document = Doc FSharp.PPrint.Combinators.backslash
let equals: document = Doc FSharp.PPrint.Combinators.equals
let qmark: document = Doc FSharp.PPrint.Combinators.qmark
let tilde: document = Doc FSharp.PPrint.Combinators.tilde
let at: document = Doc FSharp.PPrint.Combinators.at
let percent: document = Doc FSharp.PPrint.Combinators.percent
let dollar: document = Doc FSharp.PPrint.Combinators.dollar
let caret: document = Doc FSharp.PPrint.Combinators.caret
let ampersand: document = Doc FSharp.PPrint.Combinators.ampersand
let star: document = Doc FSharp.PPrint.Combinators.star
let plus: document = Doc FSharp.PPrint.Combinators.plus
let minus: document = Doc FSharp.PPrint.Combinators.minus
let underscore: document = Doc FSharp.PPrint.Combinators.underscore
let bang: document = Doc FSharp.PPrint.Combinators.bang
let bar: document = Doc FSharp.PPrint.Combinators.bar
let larrow: document = Doc (FSharp.PPrint.Engine.string "<-")
let rarrow: document = Doc (FSharp.PPrint.Engine.string "->")

let precede (Doc l:document) (Doc x:document) : document = 
    Doc (FSharp.PPrint.Combinators.precede l x)

let terminate (Doc r:document) (Doc x:document) : document = 
    Doc (FSharp.PPrint.Combinators.terminate r x)

let enclose (Doc l:document) (Doc r:document) (Doc x:document) : document = 
    Doc (FSharp.PPrint.Combinators.enclose l r x)

let squotes (Doc d:document) : document = Doc (FSharp.PPrint.Combinators.squotes d)
let dquotes (Doc d:document) : document = Doc (FSharp.PPrint.Combinators.dquotes d)
let bquotes (Doc d:document) : document = Doc (FSharp.PPrint.Combinators.bquotes d)
let braces  (Doc d:document) : document = Doc (FSharp.PPrint.Combinators.braces d)
let parens  (Doc d:document) : document = Doc (FSharp.PPrint.Combinators.parens d)
let angles  (Doc d:document) : document = Doc (FSharp.PPrint.Combinators.angles d)
let brackets(Doc d:document) : document = Doc (FSharp.PPrint.Combinators.brackets d)

let twice (Doc doc:document) : document = Doc (FSharp.PPrint.Combinators.twice doc)

let repeat (n:int) (Doc doc:document) : document = 
    Doc (FSharp.PPrint.Combinators.repeat n doc)

let concat (docs:document list) : document = 
    let dd = List.map (fun (Doc d) -> d) docs in
    let d = FSharp.PPrint.Combinators.concat dd in
    Doc d

let separate (Doc sep:document) (docs:document list) : document = 
    let dd = List.map (fun (Doc d) -> d) docs in
    let d = FSharp.PPrint.Combinators.separate sep dd in
    Doc d

// SI: check
//     Used composition to work out f' implementation. 
let concat_map (f:('a -> document)) (xs:'a list) : document = 
    let f' (a:'a) : FSharp.PPrint.Engine.document = 
        // apply f
        let d = f a in 
        // unpack d
        match d with 
        | Doc d' -> d' in
    let d' = FSharp.PPrint.Combinators.concat_map f' xs in
    Doc d'

// SI: check
let separate_map (Doc sep:document) (f:('a -> document)) (xs:'a list) : document = 
    let f' (a:'a) : FSharp.PPrint.Engine.document = 
        let d = f a in 
        match d with 
        | Doc d' -> d' in 
    let d' = FSharp.PPrint.Combinators.separate_map sep f' xs in 
    Doc d'

let separate2 (Doc sep:document) (Doc last_sep:document) (docs:document list) : document = 
    let dd = List.map (fun (Doc d) -> d) docs in
    let d = FSharp.PPrint.Combinators.separate2 sep last_sep dd in
    Doc d

let optional (f:('a -> document)) (opt:'a option) : document = failwith not_impl_msg

let lines (s:string) : document list = 
    let dd = FSharp.PPrint.Combinators.lines s in
    List.map (fun d -> (Doc d)) dd

let arbitrary_string (s:string) : document = 
    Doc (FSharp.PPrint.Combinators.arbitrary_string s)
   
let words (s:string) : document list = 
    let dd = FSharp.PPrint.Combinators.words s in 
    List.map (fun d -> (Doc d)) dd

let split (ok:(char -> bool)) (s:string) : document list = 
    let dd = FSharp.PPrint.Combinators.split ok s in 
    List.map (fun d -> (Doc d)) dd

let flow (Doc sep:document) (docs:document list) : document = 
    let dd = List.map (fun (Doc d) -> d) docs in 
    Doc (FSharp.PPrint.Combinators.flow sep dd)

// SI: check
let flow_map (Doc sep:document) (f:('a -> document)) (docs:'a list) : document =
    let f' (a:'a) : FSharp.PPrint.Engine.document = 
        let d = f a in 
        match d with 
        | Doc d' -> d' in 
    let d' = FSharp.PPrint.Combinators.separate_map sep f' docs in 
    Doc d'

let url (s:string) : document = Doc (FSharp.PPrint.Combinators.url s)

let hang (n:int) (Doc doc:document) : document = 
    Doc (FSharp.PPrint.Combinators.hang n doc)

let prefix (n:int) (b:int) (Doc left: document) (Doc right:document) : document =
    Doc (FSharp.PPrint.Combinators.prefix n b left right)

let jump (n:int) (b:int) (Doc right:document) : document = 
    Doc (FSharp.PPrint.Combinators.jump n b right)

let infix (n:int) (b:int) (Doc middle:document) (Doc left: document) (Doc right:document) : document = 
    Doc (FSharp.PPrint.Combinators.infix n b middle left right)

let surround (n:int) (b:int) (Doc opening:document) (Doc contents:document) (Doc closing:document) : document =
    Doc (FSharp.PPrint.Combinators.surround n b opening contents closing)

let soft_surround (n:int) (b:int) (Doc opening:document) (Doc contents:document) (Doc closing:document) : document = 
    Doc (FSharp.PPrint.Combinators.soft_surround n b opening contents closing)

let surround_separate (n:int) (b:int) (Doc v:document) (Doc opening:document) (Doc sep:document) (Doc closing:document) (docs:document list) : document = 
    Doc (FSharp.PPrint.Combinators.surround n b v opening closing)

// SI: check
let surround_separate_map (n:int) (b:int) (Doc v:document) (Doc opening:document) (Doc sep:document) (Doc closing:document) (f:('a -> document)) (docs:'a list) : document = 
    let f' (a:'a) : FSharp.PPrint.Engine.document = 
        let d = f a in 
        match d with 
        | Doc d' -> d' in 
    let d' = FSharp.PPrint.Combinators.surround_separate_map n b v opening sep closing f' docs in 
    Doc d'
    
let ( ^^ ) (Doc x:document) (Doc y:document) : document = 
    Doc (FSharp.PPrint.Engine.(^^) x y)

// let ( !^ ) (s:string) : document = failwith not_impl_msg

let ( ^/^ ) (Doc x:document) (Doc y:document) : document = 
    Doc (FSharp.PPrint.Combinators.(^/^) x y)

// let ( ^//^ ) (x:document) (y:document) : document = failwith not_impl_msg

open FSharp.Compatibility.OCaml

let pretty_string (rfrac:float) (width:int) (Doc doc:document) : string = 
    let buf = Buffer.create 0 in 
    FSharp.PPrint.Engine.ToBuffer.pretty rfrac width buf doc;
    buf.ToString () 

let pretty_out_channel (rfrac:float) (width:int) (Doc doc:document) (channel:FStar.Util.out_channel) : unit = 
    FSharp.PPrint.Engine.ToChannel.pretty rfrac width channel doc 
