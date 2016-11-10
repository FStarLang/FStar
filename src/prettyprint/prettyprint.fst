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

(** A pretty-printing engine and a set of basic document combinators. *)

(** {1 Building documents} *)

(** Documents must be built in memory before they are rendered. This may seem
    costly, but it is a simple approach, and works well. *)

(** The following operations form a set of basic (low-level) combinators for
    building documents. On top of these combinators, higher-level combinators
    can be defined: see {!PPrintCombinators}. *)

(** This is the abstract type of documents. *)
type document

(** The following basic (low-level) combinators allow constructing documents. *)

(** [empty] is the empty document. *)
assume val empty: document

(** [char c] is a document that consists of the single character [c]. This
    character must not be a newline. *)
assume val char: char -> document

(** [string s] is a document that consists of the string [s]. This string must
    not contain a newline. *)
assume val string: string -> document

(** [substring s ofs len] is a document that consists of the portion of the
    string [s] delimited by the offset [ofs] and the length [len]. This
    portion must contain a newline. *)
assume val substring: string -> int -> int -> document

(** [fancystring s apparent_length] is a document that consists of the string
    [s]. This string must not contain a newline. The string may contain fancy
    characters: color escape characters, UTF-8 or multi-byte characters,
    etc. Thus, its apparent length (which measures how many columns the text
    will take up on screen) differs from its length in bytes. *)
assume val fancystring: string -> int -> document

(** [fancysubstring s ofs len apparent_length] is a document that consists of
    the portion of the string [s] delimited by the offset [ofs] and the length
    [len]. This portion must contain a newline. The string may contain fancy
    characters. *)
assume val fancysubstring : string -> int -> int -> int -> document

(** [utf8string s] is a document that consists of the UTF-8-encoded string [s].
    This string must not contain a newline. *)
assume val utf8string: string -> document

(** [hardline] is a forced newline document. This document forces all enclosing
    groups to be printed in non-flattening mode. In other words, any enclosing
    groups are dissolved. *)
assume val hardline: document

(** [blank n] is a document that consists of [n] blank characters. *)
assume val blank: int -> document

(** [break_ n] is a document which consists of either [n] blank characters,
    when forced to display on a single line, or a single newline character,
    otherwise. Note that there is no choice at this point: choices are encoded
    by the [group] combinator. *)
assume val break_: int -> document

(** [doc1 ^^ doc2] is the concatenation of the documents [doc1] and [doc2]. *)
//assume val (^^): document -> document -> document
//assume val concat : document -> document -> document

(** [nest j doc] is the document [doc], in which the indentation level has
    been increased by [j], that is, in which [j] blanks have been inserted
    after every newline character. Read this again: indentation is inserted
    after every newline character. No indentation is inserted at the beginning
    of the document. *)
assume val nest: int -> document -> document

(** [group doc] encodes a choice. If possible, then the entire document [group
    doc] is rendered on a single line. Otherwise, the group is dissolved, and
    [doc] is rendered. There might be further groups within [doc], whose
    presence will lead to further choices being explored. *)
assume val group: document -> document

(** [column f] is the document obtained by applying the function [f] to the
    current column number. This combinator allows making the construction of
    a document dependent on the current column number. *)
assume val column: (int -> document) -> document

(** [nesting f] is the document obtained by applying the function [f] to the
    current indentation level, that is, the number of indentation (blank)
    characters that were inserted at the beginning of the current line. *)
assume val nesting: (int -> document) -> document

(** [position f] is the document obtained by applying the function [f]
    to the current position in the rendered output. The position
    consists of [bol], which is the character-offset of the beginnig
    of the current line (starting at 0), [line], which is the current
    line (starting at 1), and [column], which is the current column
    (starting at 0). The current character-offset is always given by
    [bol + column]. *)
assume val position : (bol:int -> line:int -> column:int -> document) -> document

(** [ifflat doc1 doc2] is rendered as [doc1] if part of a group that can be
    successfully flattened, and is rendered as [doc2] otherwise. Use this
    operation with caution. Because the pretty-printer is free to choose
    between [doc1] and [doc2], these documents should be semantically
    equivalent. *)
assume val ifflat: document -> document -> document

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

assume val lparen: document
assume val rparen: document
assume val langle: document
assume val rangle: document
assume val lbrace: document
assume val rbrace: document
assume val lbracket: document
assume val rbracket: document
assume val squote: document
assume val dquote: document
assume val bquote: document
assume val semi: document
assume val colon: document
assume val comma: document
assume val space: document
assume val dot: document
assume val sharp: document
assume val slash: document
assume val backslash: document
assume val equals: document
assume val qmark: document
assume val tilde: document
assume val at: document
assume val percent: document
assume val dollar: document
assume val caret: document
assume val ampersand: document
assume val star: document
assume val plus: document
assume val minus: document
assume val underscore: document
assume val bang: document
assume val bar: document

(** {1 Delimiters} *)

(** [precede l x] is [l ^^ x]. *)
assume val precede: document -> document -> document

(** [terminate r x] is [x ^^ r]. *)
assume val terminate: document -> document -> document

(** [enclose l r x] is [l ^^ x ^^ r]. *)
assume val enclose: document -> document -> document -> document

(** The following combinators enclose a document within a pair of delimiters.
    They are partial applications of [enclose]. No whitespace or line break is
    introduced. *)

assume val squotes: document -> document
assume val dquotes: document -> document
assume val bquotes: document -> document
assume val braces: document -> document
assume val parens: document -> document
assume val angles: document -> document
assume val brackets: document -> document

(** {1 Repetition} *)

(** [twice doc] is the document obtained by concatenating two copies of
    the document [doc]. *)
assume val twice: document -> document

(** [repeat n doc] is the document obtained by concatenating [n] copies of
    the document [doc]. *)
assume val repeat: int -> document -> document

(** {1 Lists and options} *)

(** [concat docs] is the concatenation of the documents in the list [docs]. *)
assume val concat: document list -> document

(** [separate sep docs] is the concatenation of the documents in the list
    [docs]. The separator [sep] is inserted between every two adjacent
    documents. *)
assume val separate: document -> document list -> document

(** [concat_map f xs] is equivalent to [concat (List.map f xs)]. *)
assume val concat_map: ('a -> document) -> 'a list -> document

(** [separate_map sep f xs] is equivalent to [separate sep (List.map f xs)]. *)
assume val separate_map: document -> ('a -> document) -> 'a list -> document

(** [separate2 sep last_sep docs] is the concatenation of the documents in the
    list [docs]. The separator [sep] is inserted between every two adjacent
    documents, except between the last two documents, where the separator
    [last_sep] is used instead. *)
assume val separate2: document -> document -> document list -> document

(** [optional f None] is the empty document. [optional f (Some x)] is
    the document [f x]. *)
assume val optional: ('a -> document) -> 'a option -> document

(** {1 Text} *)

(** [lines s] is the list of documents obtained by splitting [s] at newline
    characters, and turning each line into a document via [substring]. This
    code is not UTF-8 aware. *)
assume val lines: string -> document list

(** [arbitrary_string s] is equivalent to [separate (break 1) (lines s)].
    It is analogous to [string s], but is valid even if the string [s]
    contains newline characters. *)
assume val arbitrary_string: string -> document

(** [words s] is the list of documents obtained by splitting [s] at whitespace
    characters, and turning each word into a document via [substring]. All
    whitespace is discarded. This code is not UTF-8 aware. *)
assume val words: string -> document list

(** [split ok s] splits the string [s] before and after every occurrence of a
    character that satisfies the predicate [ok]. The substrings thus obtained
    are turned into documents, and a list of documents is returned. No
    information is lost: the concatenation of the documents yields the
    original string.  This code is not UTF-8 aware. *)
assume val split: (char -> bool) -> string -> document list

(** [flow sep docs] separates the documents in the list [docs] with the
    separator [sep] and arranges for a new line to begin whenever a document
    does not fit on the current line. This is useful for typesetting
    free-flowing, ragged-right text. A typical choice of [sep] is [break b],
    where [b] is the number of spaces that must be inserted between two
    consecutive words (when displayed on the same line). *)
assume val flow: document -> document list -> document

(** [flow_map sep f docs] is equivalent to [flow sep (List.map f docs)]. *)
assume val flow_map: document -> ('a -> document) -> 'a list -> document

(** [url s] is a possible way of displaying the URL [s]. A potential line
    break is inserted immediately before and immediately after every slash
    and dot character. *)
assume val url: string -> document

(** {1 Alignment and indentation} *)

(** [align doc] increases the indentation level to reach the current
    column. Thus, this document will be rendered within a box whose
    upper left corner is the current position. *)
assume val align: document -> document

(* [hang n doc] is analogous to [align], but additionally indents
   all lines, except the first one, by [n]. Thus, the text in the
   box forms a hanging indent. *)
assume val hang: int -> document -> document

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
assume val prefix: int -> int -> document -> document -> document

(** [jump n b right] is equivalent to [prefix n b empty right]. *)
assume val jump: int -> int -> document -> document

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
assume val infix: int -> int -> document -> document -> document -> document

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
assume val surround: int -> int -> document -> document -> document -> document

(** [soft_surround] is analogous to [surround], but involves more than one
    group, so it offers possibilities other than the completely flat layout
    (where [opening], [contents], and [closing] appear on a single line) and
    the completely developed layout (where [opening], [contents], and
    [closing] appear on separate lines). It tries to place the beginning of
    [contents] on the same line as [opening], and to place [closing] on the
    same line as the end of [contents], if possible.
*)
assume val soft_surround: int -> int -> document -> document -> document -> document

(** [surround_separate n b void opening sep closing docs] is equivalent to
    [surround n b opening (separate sep docs) closing], except when the
    list [docs] is empty, in which case it reduces to [void]. *)
assume val surround_separate: int -> int -> document -> document -> document -> document -> document list -> document

(** [surround_separate_map n b void opening sep closing f xs] is equivalent to
    [surround_separate n b void opening sep closing (List.map f xs)]. *)
assume val surround_separate_map: int -> int -> document -> document -> document -> document -> ('a -> document) -> 'a list -> document

// (** {1 Short-hands} *)
// 
// (** [!^s] is a short-hand for [string s]. *)
// assume val ( !^ ) : string -> document
// 
// (** [x ^/^ y] separates [x] and [y] with a breakable space.
//     It is a short-hand for [x ^^ break 1 ^^ y]. *)
// assume val ( ^/^ ) : document -> document -> document
// 
// (** [x ^//^ y] is a short-hand for [prefix 2 1 x y]. *)
// assume val ( ^//^ ) : document -> document -> document

