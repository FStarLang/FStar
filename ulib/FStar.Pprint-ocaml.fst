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
module FStar.Pprint

(* The OCaml implementation: a thin binding to Francois Pottier's pprint
   package.  The definitions marked [custard_extern] are not compiled, their
   uses refer to the OCaml symbol directly. *)

open FStar.Char
open FStar.Float64

[@@custard_extern "int"]
private assume new type ocaml_int : Type0

[@@custard_extern "Z.to_int"]
private assume val oi (n:int) : ocaml_int

[@@custard_extern "char"]
private assume new type ocaml_char : Type0

[@@custard_extern "Char.chr"]
private assume val char_chr (c:char) : ocaml_char

[@@custard_extern "Char.code"]
private assume val char_code (c:ocaml_char) : char

[@@custard_extern "PPrint.document"]
private assume new type ocaml_document : Type0

type document = ocaml_document

[@@custard_extern "PPrint.empty"]
let empty = admit ()

[@@custard_extern "PPrint.OCaml.char"]
private assume val ocaml_char_doc (c:ocaml_char) : document

let doc_of_char c = ocaml_char_doc (char_chr c)

[@@custard_extern "PPrint.string"]
let doc_of_string _ = admit ()

let doc_of_bool b = doc_of_string (if b then "true" else "false")

[@@custard_extern "PPrint.substring"]
private assume val ocaml_substring : string -> ocaml_int -> ocaml_int -> document

let substring s ofs len = ocaml_substring s (oi ofs) (oi len)

[@@custard_extern "PPrint.fancystring"]
private assume val ocaml_fancystring : string -> ocaml_int -> document

let fancystring s apparent_length = ocaml_fancystring s (oi apparent_length)

[@@custard_extern "PPrint.fancysubstring"]
private assume val ocaml_fancysubstring : string -> ocaml_int -> ocaml_int -> ocaml_int -> document

let fancysubstring s ofs len apparent_length =
  ocaml_fancysubstring s (oi ofs) (oi len) (oi apparent_length)

[@@custard_extern "PPrint.utf8string"]
let utf8string _ = admit ()

[@@custard_extern "PPrint.hardline"]
let hardline = admit ()

[@@custard_extern "PPrint.blank"]
private assume val ocaml_blank : ocaml_int -> document

let blank n = ocaml_blank (oi n)

[@@custard_extern "PPrint.break"]
private assume val ocaml_break : ocaml_int -> document

let break_ n = ocaml_break (oi n)

[@@custard_extern "PPrint.(^^)"]
let ( ^^ ) _ _ = admit ()

[@@custard_extern "PPrint.(^/^)"]
let ( ^/^ ) _ _ = admit ()

[@@custard_extern "PPrint.nest"]
private assume val ocaml_nest : ocaml_int -> document -> document

let nest j doc = ocaml_nest (oi j) doc

[@@custard_extern "PPrint.group"]
let group _ = admit ()

[@@custard_extern "PPrint.ifflat"]
let ifflat _ _ = admit ()

[@@custard_extern "PPrint.lparen"]
let lparen = admit ()
[@@custard_extern "PPrint.rparen"]
let rparen = admit ()
[@@custard_extern "PPrint.langle"]
let langle = admit ()
[@@custard_extern "PPrint.rangle"]
let rangle = admit ()
[@@custard_extern "PPrint.lbrace"]
let lbrace = admit ()
[@@custard_extern "PPrint.rbrace"]
let rbrace = admit ()
[@@custard_extern "PPrint.lbracket"]
let lbracket = admit ()
[@@custard_extern "PPrint.rbracket"]
let rbracket = admit ()
[@@custard_extern "PPrint.squote"]
let squote = admit ()
[@@custard_extern "PPrint.dquote"]
let dquote = admit ()
[@@custard_extern "PPrint.bquote"]
let bquote = admit ()
[@@custard_extern "PPrint.semi"]
let semi = admit ()
[@@custard_extern "PPrint.colon"]
let colon = admit ()
[@@custard_extern "PPrint.comma"]
let comma = admit ()
[@@custard_extern "PPrint.space"]
let space = admit ()
[@@custard_extern "PPrint.dot"]
let dot = admit ()
[@@custard_extern "PPrint.sharp"]
let sharp = admit ()
[@@custard_extern "PPrint.slash"]
let slash = admit ()
[@@custard_extern "PPrint.backslash"]
let backslash = admit ()
[@@custard_extern "PPrint.equals"]
let equals = admit ()
[@@custard_extern "PPrint.qmark"]
let qmark = admit ()
[@@custard_extern "PPrint.tilde"]
let tilde = admit ()
[@@custard_extern "PPrint.at"]
let at = admit ()
[@@custard_extern "PPrint.percent"]
let percent = admit ()
[@@custard_extern "PPrint.dollar"]
let dollar = admit ()
[@@custard_extern "PPrint.caret"]
let caret = admit ()
[@@custard_extern "PPrint.ampersand"]
let ampersand = admit ()
[@@custard_extern "PPrint.star"]
let star = admit ()
[@@custard_extern "PPrint.plus"]
let plus = admit ()
[@@custard_extern "PPrint.minus"]
let minus = admit ()
[@@custard_extern "PPrint.underscore"]
let underscore = admit ()
[@@custard_extern "PPrint.bang"]
let bang = admit ()
[@@custard_extern "PPrint.bar"]
let bar = admit ()

let rarrow = doc_of_string "->"
let long_left_arrow = doc_of_string "<--"
let larrow = doc_of_string "<-"

[@@custard_extern "PPrint.precede"]
let precede _ _ = admit ()
[@@custard_extern "PPrint.terminate"]
let terminate _ _ = admit ()
[@@custard_extern "PPrint.enclose"]
let enclose _ _ _ = admit ()
[@@custard_extern "PPrint.squotes"]
let squotes _ = admit ()
[@@custard_extern "PPrint.dquotes"]
let dquotes _ = admit ()
[@@custard_extern "PPrint.bquotes"]
let bquotes _ = admit ()
[@@custard_extern "PPrint.braces"]
let braces _ = admit ()
[@@custard_extern "PPrint.parens"]
let parens _ = admit ()
[@@custard_extern "PPrint.angles"]
let angles _ = admit ()
[@@custard_extern "PPrint.brackets"]
let brackets _ = admit ()
[@@custard_extern "PPrint.twice"]
let twice _ = admit ()

[@@custard_extern "PPrint.repeat"]
private assume val ocaml_repeat : ocaml_int -> document -> document

let repeat n doc = ocaml_repeat (oi n) doc

[@@custard_extern "PPrint.concat"]
let concat _ = admit ()
[@@custard_extern "PPrint.separate"]
let separate _ _ = admit ()
[@@custard_extern "PPrint.concat_map"]
let concat_map _ _ = admit ()
[@@custard_extern "PPrint.separate_map"]
let separate_map _ _ _ = admit ()
[@@custard_extern "PPrint.separate2"]
let separate2 _ _ _ = admit ()
[@@custard_extern "PPrint.optional"]
let optional _ _ = admit ()
[@@custard_extern "PPrint.lines"]
let lines _ = admit ()
[@@custard_extern "PPrint.arbitrary_string"]
let arbitrary_string _ = admit ()
[@@custard_extern "PPrint.words"]
let words _ = admit ()

[@@custard_extern "PPrint.split"]
private assume val ocaml_split : (ocaml_char -> bool) -> string -> list document

let split ok s = ocaml_split (fun c -> ok (char_code c)) s

[@@custard_extern "PPrint.flow"]
let flow _ _ = admit ()
[@@custard_extern "PPrint.flow_map"]
let flow_map _ _ _ = admit ()
[@@custard_extern "PPrint.url"]
let url _ = admit ()
[@@custard_extern "PPrint.align"]
let align _ = admit ()

[@@custard_extern "PPrint.hang"]
private assume val ocaml_hang : ocaml_int -> document -> document

let hang n doc = ocaml_hang (oi n) doc

[@@custard_extern "PPrint.prefix"]
private assume val ocaml_prefix : ocaml_int -> ocaml_int -> document -> document -> document

let prefix n b left right = ocaml_prefix (oi n) (oi b) left right

[@@custard_extern "PPrint.jump"]
private assume val ocaml_jump : ocaml_int -> ocaml_int -> document -> document

let jump n b right = ocaml_jump (oi n) (oi b) right

[@@custard_extern "PPrint.infix"]
private assume val ocaml_infix : ocaml_int -> ocaml_int -> document -> document -> document -> document

let infix n b middle left right = ocaml_infix (oi n) (oi b) middle left right

[@@custard_extern "PPrint.surround"]
private assume val ocaml_surround : ocaml_int -> ocaml_int -> document -> document -> document -> document

let surround n b opening contents closing =
  ocaml_surround (oi n) (oi b) opening contents closing

[@@custard_extern "PPrint.soft_surround"]
private assume val ocaml_soft_surround : ocaml_int -> ocaml_int -> document -> document -> document -> document

let soft_surround n b opening contents closing =
  ocaml_soft_surround (oi n) (oi b) opening contents closing

[@@custard_extern "PPrint.surround_separate"]
private assume val ocaml_surround_separate :
  ocaml_int -> ocaml_int -> document -> document -> document -> document -> list document -> document

let surround_separate n b void_ opening sep closing docs =
  ocaml_surround_separate (oi n) (oi b) void_ opening sep closing docs

[@@custard_extern "PPrint.surround_separate_map"]
private assume val ocaml_surround_separate_map (#a:Type) :
  ocaml_int -> ocaml_int -> document -> document -> document -> document -> (a -> document) -> list a -> document

let surround_separate_map n b void_ opening sep closing f xs =
  ocaml_surround_separate_map (oi n) (oi b) void_ opening sep closing f xs

(* [PPrint.ToBuffer.pretty] writes into a buffer; the buffer is local, so the
   whole is a pure function, which F* cannot see through. *)
[@@custard_extern "(fun rfrac width doc -> let buf = Buffer.create 0 in PPrint.ToBuffer.pretty rfrac width buf doc; Buffer.contents buf)"]
private assume val ocaml_pretty_string : float64 -> ocaml_int -> document -> string

let pretty_string rfrac width doc = ocaml_pretty_string rfrac (oi width) doc

let render doc = pretty_string one 80 doc
