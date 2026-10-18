(*
   Copyright 2026 Microsoft Research

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

(* The implementation of [FStar.Pprint] used by the Cherry backend, which has
   no OCaml library to link against.  It is written from scratch, after the
   classic presentations of the Wadler-style document algebra (Wadler, "A
   prettier printer"; Leijen's wl-pprint, for the ribbon) and Oppen's
   observation that a group can be decided by its precomputed flat width.

   Documents.  Every node that can contain a line break carries its
   *requirement*: the number of columns it occupies when rendered flat, or
   [-1] when it cannot be flat at all (it contains a [hardline] that no
   [ifflat] hides).  Requirements are computed bottom-up when the document is
   built, so each node is visited once.

   Rendering.  A single left-to-right pass over a stack of
   (indentation, flat?, document) frames, written as a self tail call so that
   it is a loop: no recursion on the depth of the document.  A [group] is
   printed flat exactly when it is already inside a flat group, or its
   requirement fits both
   - the page: [column + requirement <= width], and
   - the ribbon: [column + requirement <= line_indent + ribbon], where
     [line_indent] is the indentation the current line started with and
     [ribbon = floor (rfrac * width)].
   Only the group itself is measured, not what follows it on the line.
   Blanks (indentation, [blank], flat [break_]) are kept pending and only
   written out before the next nonempty text, so lines never end in blanks
   that the document did not spell out as text.  Text is written as is, and
   advances the column by its apparent length, newline characters included.

   Lengths and offsets are in bytes, as in the OCaml library, except for
   [utf8string], whose length is its number of code points, and the fancy
   strings, whose length is given.  The string splitting functions
   ([lines], [words], [split], [url]) work on bytes too.

   Known differences with the OCaml build:
   - [doc_of_char c] for a code point above 255 renders [c] between quotes
     (the OCaml build fails on such characters).
   - Negative [nest] amounts and out-of-bounds [substring] arguments are not
     checked; the bounds of a substring are clamped to the string. *)

open FStar.Char

module F = FStar.Float64
module I64 = FStar.Int64
module U32 = FStar.UInt32
module L = FStar.List.Tot.Base

(* Byte-level string primitives, realized by the Cherry runtime
   (ulib/c/cherry.c). *)
private assume val byte_size : string -> nat
private assume val byte_at : string -> nat -> char
private assume val byte_sub : string -> nat -> nat -> string

(* A requirement of [-1] is infinite. *)
private let req_add (a b : int) : int =
  if a < 0 || b < 0 then -1 else a + b

type document =
  | Empty : document
  | Text : s:string -> len:int -> document
  | Blank : n:int -> document
  | Hard : document
  | IfFlat : req:int -> flat:document -> brk:document -> document
  | Cat : req:int -> a:document -> b:document -> document
  | Nest : req:int -> j:int -> d:document -> document
  | Group : req:int -> d:document -> document
  | Align : req:int -> d:document -> document

private let req (d:document) : int =
  match d with
  | Empty -> 0
  | Text _ n -> n
  | Blank n -> n
  | Hard -> -1
  | IfFlat r _ _ -> r
  | Cat r _ _ -> r
  | Nest r _ _ -> r
  | Group r _ -> r
  | Align r _ -> r

private let text (s:string) : document =
  if s = "" then Empty else Text s (byte_size s)

let empty = Empty

(* As an OCaml character literal. *)
private let pad3 (n:int) : string =
  if n < 10 then "00" ^ string_of_int n
  else if n < 100 then "0" ^ string_of_int n
  else string_of_int n

private let char_literal (c:char) : string =
  let n = U32.v (u32_of_char c) in
  if c = '\\' then "'\\\\'"
  else if c = '\'' then "'\\''"
  else if c = '\n' then "'\\n'"
  else if c = '\t' then "'\\t'"
  else if c = '\r' then "'\\r'"
  else if n = 8 then "'\\b'"
  else if (n >= 32 && n <= 126) || n > 255 then "'" ^ String.make 1 c ^ "'"
  else "'\\" ^ pad3 n ^ "'"

let doc_of_char c = text (char_literal c)

let doc_of_string s = text s

let doc_of_bool b = if b then Text "true" 4 else Text "false" 5

let substring s ofs len =
  if ofs < 0 || len <= 0 then Empty else text (byte_sub s ofs len)

let fancystring s apparent_length = Text s apparent_length

let fancysubstring s ofs len apparent_length =
  if ofs < 0 || len < 0 then Text "" apparent_length
  else Text (byte_sub s ofs len) apparent_length

let utf8string s = if s = "" then Empty else Text s (String.length s)

let hardline = Hard

let blank n = if n <= 0 then Empty else Blank n

let break_ n = IfFlat (if n < 0 then 0 else n) (blank n) Hard

let ( ^^ ) x y =
  match x with
  | Empty -> y
  | _ ->
    match y with
    | Empty -> x
    | _ -> Cat (req_add (req x) (req y)) x y

let ( ^/^ ) x y = x ^^ break_ 1 ^^ y

let nest j doc =
  match doc with
  | Empty -> Empty
  | _ -> Nest (req doc) j doc

let group doc =
  match doc with
  | Empty -> Empty
  | Group _ _ -> doc
  | _ -> Group (req doc) doc

let ifflat doc1 doc2 = IfFlat (req doc1) doc1 doc2

private let ch (s:string) : document = Text s 1

let lparen = ch "("
let rparen = ch ")"
let langle = ch "<"
let rangle = ch ">"
let lbrace = ch "{"
let rbrace = ch "}"
let lbracket = ch "["
let rbracket = ch "]"
let squote = ch "'"
let dquote = ch "\""
let bquote = ch "`"
let semi = ch ";"
let colon = ch ":"
let comma = ch ","
let space = ch " "
let dot = ch "."
let sharp = ch "#"
let slash = ch "/"
let backslash = ch "\\"
let equals = ch "="
let qmark = ch "?"
let tilde = ch "~"
let at = ch "@"
let percent = ch "%"
let dollar = ch "$"
let caret = ch "^"
let ampersand = ch "&"
let star = ch "*"
let plus = ch "+"
let minus = ch "-"
let underscore = ch "_"
let bang = ch "!"
let bar = ch "|"
let rarrow = Text "->" 2
let long_left_arrow = Text "<--" 3
let larrow = Text "<-" 2

let precede l x = l ^^ x

let terminate r x = x ^^ r

let enclose l r x = l ^^ x ^^ r

let squotes d = enclose squote squote d
let dquotes d = enclose dquote dquote d
let bquotes d = enclose bquote bquote d
let braces d = enclose lbrace rbrace d
let parens d = enclose lparen rparen d
let angles d = enclose langle rangle d
let brackets d = enclose lbracket rbracket d

let twice doc = doc ^^ doc

private let rec repeat_acc (n:int) (doc acc:document)
  : Tot document (decreases (if n > 0 then n else 0)) =
  if n <= 0 then acc else repeat_acc (n - 1) doc (acc ^^ doc)

let repeat n doc = repeat_acc n doc Empty

(* The list combinators fold from the left, as loops, and so build
   left-nested concatenations; the renderer does not mind. *)
private let rec concat_acc (acc:document) (docs:list document) : Tot document (decreases docs) =
  match docs with
  | [] -> acc
  | d :: rest -> concat_acc (acc ^^ d) rest

let concat docs = concat_acc Empty docs

private let rec separate_acc (sep acc:document) (docs:list document)
  : Tot document (decreases docs) =
  match docs with
  | [] -> acc
  | d :: rest -> separate_acc sep (acc ^^ sep ^^ d) rest

let separate sep docs =
  match docs with
  | [] -> Empty
  | d :: rest -> separate_acc sep d rest

private let rec concat_map_acc (#a:Type) (f:a -> document) (acc:document) (xs:list a)
  : Tot document (decreases xs) =
  match xs with
  | [] -> acc
  | x :: rest -> concat_map_acc f (acc ^^ f x) rest

let concat_map f xs = concat_map_acc f Empty xs

private let rec separate_map_acc (#a:Type) (sep:document) (f:a -> document) (acc:document) (xs:list a)
  : Tot document (decreases xs) =
  match xs with
  | [] -> acc
  | x :: rest -> separate_map_acc sep f (acc ^^ sep ^^ f x) rest

let separate_map sep f xs =
  match xs with
  | [] -> Empty
  | x :: rest -> separate_map_acc sep f (f x) rest

private let rec separate2_acc (sep last_sep acc:document) (docs:list document)
  : Tot document (decreases docs) =
  match docs with
  | [] -> acc
  | [d] -> acc ^^ last_sep ^^ d
  | d :: rest -> separate2_acc sep last_sep (acc ^^ sep ^^ d) rest

let separate2 sep last_sep docs =
  match docs with
  | [] -> Empty
  | d :: rest -> separate2_acc sep last_sep d rest

let optional f o =
  match o with
  | None -> Empty
  | Some x -> f x

(* Splitting, on bytes.  [cut ok keep s n start i acc] scans [s] from byte
   [i], the current piece starting at [start]; at a byte satisfying [ok] it
   ends the piece, adding the separator itself when [keep], and empty pieces
   only when [keep_empty]. *)
private let piece (s:string) (start i:nat) : document =
  if i <= start then Empty else text (byte_sub s start (i - start))

private let rec cut (ok:char -> bool) (keep keep_empty:bool) (s:string) (n start i:nat)
  (acc:list document) : Tot (list document) (decreases (if i < n then n - i else 0)) =
  if i >= n then begin
    if keep_empty || i > start then L.rev (piece s start i :: acc) else L.rev acc
  end else begin
    let c = byte_at s i in
    if ok c then begin
      let acc = if keep_empty || i > start then piece s start i :: acc else acc in
      let acc = if keep then text (byte_sub s i 1) :: acc else acc in
      cut ok keep keep_empty s n (i + 1) (i + 1) acc
    end else cut ok keep keep_empty s n start (i + 1) acc
  end

private let is_newline (c:char) : bool = c = '\n'

let lines s = cut is_newline false true s (byte_size s) 0 0 []

let arbitrary_string s = separate (break_ 1) (lines s)

private let is_space (c:char) : bool =
  c = ' ' || c = '\t' || c = '\n' || c = '\r'

let words s = cut is_space false false s (byte_size s) 0 0 []

let split ok s = cut ok true true s (byte_size s) 0 0 []

private let rec flow_acc (sep acc:document) (docs:list document) : Tot document (decreases docs) =
  match docs with
  | [] -> acc
  | d :: rest -> flow_acc sep (acc ^^ group (sep ^^ d)) rest

let flow sep docs =
  match docs with
  | [] -> Empty
  | d :: rest -> flow_acc sep d rest

private let rec flow_map_acc (#a:Type) (sep:document) (f:a -> document) (acc:document) (xs:list a)
  : Tot document (decreases xs) =
  match xs with
  | [] -> acc
  | x :: rest -> flow_map_acc sep f (acc ^^ group (sep ^^ f x)) rest

let flow_map sep f docs =
  match docs with
  | [] -> Empty
  | x :: rest -> flow_map_acc sep f (f x) rest

private let is_url_sep (c:char) : bool = c = '/' || c = '.'

let url s = flow (break_ 0) (split is_url_sep s)

let align doc =
  match doc with
  | Empty -> Empty
  | _ -> Align (req doc) doc

let hang n doc = align (nest n doc)

let prefix n b left right = group (left ^^ nest n (break_ b ^^ right))

let jump n b right = prefix n b empty right

let infix n b middle left right = prefix n b (left ^^ blank b ^^ middle) right

let surround n b opening contents closing =
  group (opening ^^ nest n (break_ b ^^ contents) ^^ break_ b ^^ closing)

let soft_surround n b opening contents closing =
  group (opening ^^ nest n (group (break_ b) ^^ contents) ^^ group (break_ b ^^ closing))

let surround_separate n b void_ opening sep closing docs =
  match docs with
  | [] -> void_
  | _ -> surround n b opening (separate sep docs) closing

let surround_separate_map n b void_ opening sep closing f xs =
  match xs with
  | [] -> void_
  | _ -> surround n b opening (separate_map sep f xs) closing

(* Rendering *)

private noeq type stack =
  | Done : stack
  | Push : indent:int -> flat:bool -> d:document -> rest:stack -> stack

private let rec dsize (d:document) : GTot pos =
  match d with
  | IfFlat _ a b -> 1 + dsize a + dsize b
  | Cat _ a b -> 1 + dsize a + dsize b
  | Nest _ _ a -> 1 + dsize a
  | Group _ a -> 1 + dsize a
  | Align _ a -> 1 + dsize a
  | _ -> 1

private let rec ssize (k:stack) : GTot nat =
  match k with
  | Done -> 0
  | Push _ _ d rest -> dsize d + ssize rest

private let add_spaces (out:string) (n:int) : string =
  if n <= 0 then out else out ^ String.make n ' '

(* [col] is the current column, [pend] the blanks not written yet (they are
   included in [col]), and [base] the indentation of the current line. *)
#push-options "--fuel 2 --ifuel 1"
private let rec render_loop (width rib:int) (out:string) (col pend base:int) (k:stack)
  : Tot string (decreases (ssize k)) =
  match k with
  | Done -> out
  | Push i f d rest ->
    match d with
    | Empty -> render_loop width rib out col pend base rest
    | Text s n ->
      if s = "" then render_loop width rib out (col + n) pend base rest
      else render_loop width rib (add_spaces out pend ^ s) (col + n) 0 base rest
    | Blank n -> render_loop width rib out (col + n) (pend + n) base rest
    | Hard -> render_loop width rib (out ^ "\n") i i i rest
    | IfFlat _ a b ->
      if f then render_loop width rib out col pend base (Push i f a rest)
      else render_loop width rib out col pend base (Push i f b rest)
    | Cat _ a b -> render_loop width rib out col pend base (Push i f a (Push i f b rest))
    | Nest _ j a -> render_loop width rib out col pend base (Push (i + j) f a rest)
    | Align _ a -> render_loop width rib out col pend base (Push col f a rest)
    | Group r a ->
      let f' = f || (r >= 0 && col + r <= width && col + r <= base + rib) in
      render_loop width rib out col pend base (Push i f' a rest)
#pop-options

(* [floor (rfrac * width)], clamped to [0, width]: the largest [k] in that
   range whose float is at most the product, by bisection. *)

private let rec bisect (x:F.float64) (lo hi:int)
  : Tot int (decreases (if hi > lo then hi - lo else 0)) =
  if hi <= lo || hi > 1000000000 || lo < 0 then lo
  else
    let mid = (lo + hi + 1) / 2 in
    if F.lte (F.of_int (I64.int_to_t mid)) x then bisect x mid hi
    else bisect x lo (mid - 1)

private let ribbon (rfrac:F.float64) (width:int) : int =
  if width <= 0 then 0
  else
    let w = if width > 1000000000 then 1000000000 else width in
    let x = F.mul rfrac (F.of_int (I64.int_to_t w)) in
    if F.lte (F.of_int 0L) x then bisect x 0 w else 0

let pretty_string rfrac width doc =
  render_loop width (ribbon rfrac width) "" 0 0 0 (Push 0 false doc Done)

let render doc = pretty_string F.one 80 doc
