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
open FStar.ST
open FStar.All
open FStar.BaseTypes

(** A pretty-printing engine and a set of basic document combinators. *)

(** {1 Building documents} *)

(** Documents must be built in memory before they are rendered. This may seem
    costly, but it is a simple approach, and works well. *)

(** The following operations form a set of basic (low-level) combinators for
    building documents. On top of these combinators, higher-level combinators
    can be defined: see {!PPrintCombinators}. *)

(** This is the abstract type of documents. *)
type document
  = FSharp.PPrint.Engine.document // JUST FSHARP

(** The following basic (low-level) combinators allow constructing documents. *)

(** [empty] is the empty document. *)
val empty: document

(** [doc_of_char c] is a document that consists of the single character [c]. This
    character must not be a newline. *)
val doc_of_char: FStar.Char.char -> document

(** [doc_of_string s] is a document that consists of the string [s]. This string must
    not contain a newline. *)
val doc_of_string: string -> document

(** [doc_of_bool b] is a document that consists of the boolean [b]. This boolean must
    not contain a newline. *)
val doc_of_bool: bool -> document

(** [substring s ofs len] is a document that consists of the portion of the
    string [s] delimited by the offset [ofs] and the length [len]. This
    portion must contain a newline. *)
val substring: string -> int -> int -> document

(** [fancystring s apparent_length] is a document that consists of the string
    [s]. This string must not contain a newline. The string may contain fancy
    characters: color escape characters, UTF-8 or multi-byte characters,
    etc. Thus, its apparent length (which measures how many columns the text
    will take up on screen) differs from its length in bytes. *)
val fancystring: string -> int -> document

(** [fancysubstring s ofs len apparent_length] is a document that consists of
    the portion of the string [s] delimited by the offset [ofs] and the length
    [len]. This portion must contain a newline. The string may contain fancy
    characters. *)
val fancysubstring : string -> int -> int -> int -> document

(** [utf8string s] is a document that consists of the UTF-8-encoded string [s].
    This string must not contain a newline. *)
val utf8string: string -> document

(** [hardline] is a forced newline document. This document forces all enclosing
    groups to be printed in non-flattening mode. In other words, any enclosing
    groups are dissolved. *)
val hardline: document

(** [blank n] is a document that consists of [n] blank characters. *)
val blank: int -> document

(** [break_ n] is a document which consists of either [n] blank characters,
    when forced to display on a single line, or a single newline character,
    otherwise. Note that there is no choice at this point: choices are encoded
    by the [group] combinator. *)
val break_: int -> document

(** [doc1 ^^ doc2] is the concatenation of the documents [doc1] and [doc2]. *)
val ( ^^ ) : document -> document -> document
(** [x ^/^ y] separates x and y with a breakable space. It is a short-hand for
    [x ^^ break 1 ^^ y] *)
val ( ^/^ ) : document -> document -> document

(** [nest j doc] is the document [doc], in which the indentation level has
    been increased by [j], that is, in which [j] blanks have been inserted
    after every newline character. Read this again: indentation is inserted
    after every newline character. No indentation is inserted at the beginning
    of the document. *)
val nest: int -> document -> document

(** [group doc] encodes a choice. If possible, then the entire document [group
    doc] is rendered on a single line. Otherwise, the group is dissolved, and
    [doc] is rendered. There might be further groups within [doc], whose
    presence will lead to further choices being explored. *)
val group: document -> document

// (** [column f] is the document obtained by applying the function [f] to the
//     current column number. This combinator allows making the construction of
//     a document dependent on the current column number. *)
// val column: (int -> document) -> document

// (** [nesting f] is the document obtained by applying the function [f] to the
//     current indentation level, that is, the number of indentation (blank)
//     characters that were inserted at the beginning of the current line. *)
// val nesting: (int -> document) -> document

// (** [position f] is the document obtained by applying the function [f]
//     to the current position in the rendered output. The position
//     consists of [bol], which is the character-offset of the beginnig
//     of the current line (starting at 0), [line], which is the current
//     line (starting at 1), and [column], which is the current column
//     (starting at 0). The current character-offset is always given by
//     [bol + column]. *)
// val position : (int -> int -> int -> document) -> document

(** [ifflat doc1 doc2] is rendered as [doc1] if part of a group that can be
    successfully flattened, and is rendered as [doc2] otherwise. Use this
    operation with caution. Because the pretty-printer is free to choose
    between [doc1] and [doc2], these documents should be semantically
    equivalent. *)
val ifflat: document -> document -> document

// SI: purposely commented-out for now.
// (** {1 Rendering documents} *)
//
// (** This renderer sends its output into an output channel. *)
// module ToChannel : PPrintRenderer.RENDERER
//   with type channel = out_channel
//    and type document = document
//
// (** This renderer sends its output into a memory buffer. *)
// module ToBuffer : PPrintRenderer.RENDERER
//   with type channel = Buffer.t
//    and type document = document
//
// (** This renderer sends its output into a formatter channel. *)
// module ToFormatter : PPrintRenderer.RENDERER
//   with type channel = Format.formatter
//    and type document = document


(** A set of high-level combinators for building documents. *)

(** {1 Single characters} *)

(** The following constant documents consist of a single character. *)

val lparen: document
val rparen: document
val langle: document
val rangle: document
val lbrace: document
val rbrace: document
val lbracket: document
val rbracket: document
val squote: document
val dquote: document
val bquote: document
val semi: document
val colon: document
val comma: document
val space: document
val dot: document
val sharp: document
val slash: document
val backslash: document
val equals: document
val qmark: document
val tilde: document
val at: document
val percent: document
val dollar: document
val caret: document
val ampersand: document
val star: document
val plus: document
val minus: document
val underscore: document
val bang: document
val bar: document
val rarrow: document
val long_left_arrow: document
val larrow: document

(** {1 Delimiters} *)

(** [precede l x] is [l ^^ x]. *)
val precede: document -> document -> document

(** [terminate r x] is [x ^^ r]. *)
val terminate: document -> document -> document

(** [enclose l r x] is [l ^^ x ^^ r]. *)
val enclose: document -> document -> document -> document

(** The following combinators enclose a document within a pair of delimiters.
    They are partial applications of [enclose]. No whitespace or line break is
    introduced. *)

val squotes: document -> document
val dquotes: document -> document
val bquotes: document -> document
val braces: document -> document
val parens: document -> document
val angles: document -> document
val brackets: document -> document

(** {1 Repetition} *)

(** [twice doc] is the document obtained by concatenating two copies of
    the document [doc]. *)
val twice: document -> document

(** [repeat n doc] is the document obtained by concatenating [n] copies of
    the document [doc]. *)
val repeat: int -> document -> document

(** {1 Lists and options} *)

(** [concat docs] is the concatenation of the documents in the list [docs]. *)
val concat: list<document> -> document

(** [separate sep docs] is the concatenation of the documents in the list
    [docs]. The separator [sep] is inserted between every two adjacent
    documents. *)
val separate: document -> list<document> -> document

(** [concat_map f xs] is equivalent to [concat (List.map f xs)]. *)
val concat_map: ('a -> document) -> list<'a> -> document

(** [separate_map sep f xs] is equivalent to [separate sep (List.map f xs)]. *)
val separate_map: document -> ('a -> document) -> list<'a> -> document

(** [separate2 sep last_sep docs] is the concatenation of the documents in the
    list [docs]. The separator [sep] is inserted between every two adjacent
    documents, except between the last two documents, where the separator
    [last_sep] is used instead. *)
val separate2: document -> document -> list<document> -> document

(** [optional f None] is the empty document. [optional f (Some x)] is
    the document [f x]. *)
val optional: ('a -> document) -> option<'a> -> document

(** {1 Text} *)

(** [lines s] is the list of documents obtained by splitting [s] at newline
    characters, and turning each line into a document via [substring]. This
    code is not UTF-8 aware. *)
val lines: string -> list<document>

(** [arbitrary_string s] is equivalent to [separate (break 1) (lines s)].
    It is analogous to [string s], but is valid even if the string [s]
    contains newline characters. *)
val arbitrary_string: string -> document

(** [words s] is the list of documents obtained by splitting [s] at whitespace
    characters, and turning each word into a document via [substring]. All
    whitespace is discarded. This code is not UTF-8 aware. *)
val words: string -> list<document>

(** [split ok s] splits the string [s] before and after every occurrence of a
    character that satisfies the predicate [ok]. The substrings thus obtained
    are turned into documents, and a list of documents is returned. No
    information is lost: the concatenation of the documents yields the
    original string.  This code is not UTF-8 aware. *)
val split: (FStar.Char.char -> bool) -> string -> list<document>

(** [flow sep docs] separates the documents in the list [docs] with the
    separator [sep] and arranges for a new line to begin whenever a document
    does not fit on the current line. This is useful for typesetting
    free-flowing, ragged-right text. A typical choice of [sep] is [break b],
    where [b] is the number of spaces that must be inserted between two
    consecutive words (when displayed on the same line). *)
val flow: document -> list<document> -> document

(** [flow_map sep f docs] is equivalent to [flow sep (List.map f docs)]. *)
val flow_map: document -> ('a -> document) -> list<'a> -> document

(** [url s] is a possible way of displaying the URL [s]. A potential line
    break is inserted immediately before and immediately after every slash
    and dot character. *)
val url: string -> document

(** {1 Alignment and indentation} *)

(** [align doc] increases the indentation level to reach the current
    column. Thus, this document will be rendered within a box whose
    upper left corner is the current position. *)
val align: document -> document

(* [hang n doc] is analogous to [align], but additionally indents
   all lines, except the first one, by [n]. Thus, the text in the
   box forms a hanging indent. *)
val hang: int -> document -> document

(** [prefix n b left right] has the following flat layout: {[
left right
]}
and the following non-flat layout:
{[
left
  right
]}
The parameter [n] controls the nesting of [right] (when not flat).
The parameter [b] controls the number of spaces between [left] and [right]
(when flat).
 *)
val prefix: int -> int -> document -> document -> document

(** [jump n b right] is equivalent to [prefix n b empty right]. *)
val jump: int -> int -> document -> document

(** [infix n b middle left right] has the following flat layout: {[
left middle right
]}
and the following non-flat layout: {[
left middle
  right
]}
The parameter [n] controls the nesting of [right] (when not flat).
The parameter [b] controls the number of spaces between [left] and [middle]
(always) and between [middle] and [right] (when flat).
*)
val infix: int -> int -> document -> document -> document -> document

(** [surround n b opening contents closing] has the following flat layout: {[
opening contents closing
]}
and the following non-flat layout: {[
opening
  contents
closing
]}
The parameter [n] controls the nesting of [contents] (when not flat).
The parameter [b] controls the number of spaces between [opening] and [contents]
and between [contents] and [closing] (when flat).
*)
val surround: int -> int -> document -> document -> document -> document

(** [soft_surround] is analogous to [surround], but involves more than one
    group, so it offers possibilities other than the completely flat layout
    (where [opening], [contents], and [closing] appear on a single line) and
    the completely developed layout (where [opening], [contents], and
    [closing] appear on separate lines). It tries to place the beginning of
    [contents] on the same line as [opening], and to place [closing] on the
    same line as the end of [contents], if possible.
*)
val soft_surround: int -> int -> document -> document -> document -> document

(** [surround_separate n b void opening sep closing docs] is equivalent to
    [surround n b opening (separate sep docs) closing], except when the
    list [docs] is empty, in which case it reduces to [void]. *)
val surround_separate: int -> int -> document -> document -> document -> document -> list<document> -> document

(** [surround_separate_map n b void opening sep closing f xs] is equivalent to
    [surround_separate n b void opening sep closing (List.map f xs)]. *)
val surround_separate_map: int -> int -> document -> document -> document -> document -> ('a -> document) -> list<'a> -> document

(** {1 Short-hands} *)


//(** [!^s] is a short-hand for [string s]. *)
// val ( !^ ) : string -> document

(** [x ^/^ y] separates [x] and [y] with a breakable space.
    It is a short-hand for [x ^^ break 1 ^^ y]. *)

(** [x ^//^ y] is a short-hand for [prefix 2 1 x y]. *)
// val ( ^//^ ) : document -> document -> document

// Expose underlying Renderer.pretty implementations (avoid inner modules).
// [pretty_string] uses ToBuffer:RENDERER implementation;
// [print_out_channel] uses the ToChannel:RENDERER one.
val pretty_string : float -> int -> document -> string
val pretty_out_channel : float -> int -> document -> FStar.Util.out_channel -> unit
