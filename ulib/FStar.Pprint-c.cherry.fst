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

(* The Cherry implementation: a port of Francois Pottier's PPrint (version
   20230830), which the OCaml implementation binds, so that both render a
   document identically.  Differences:
   - Lengths and offsets count code points, as FStar.String does, where PPrint
     counts bytes.  The two agree on ASCII.
   - [blank n] for a negative [n] is empty.
   - [lines], [words], [split] and [url] are quadratic, since the runtime has
     no linear way of walking a string. *)

open FStar.Char
module S = FStar.String
module F = FStar.Float64
module I64 = FStar.Int64
module U32 = FStar.UInt32

(* Requirements are the width of the flat rendering, or [-1] for infinity. *)
noeq type document =
  | Empty : document
  | Text : s:string -> len:int -> document
  | Blank : n:int -> document
  | IfFlat : d1:document -> d2:document -> document
  | HardLine : document
  | Cat : req:int -> d1:document -> d2:document -> document
  | Nest : req:int -> j:int -> d:document -> document
  | Group : req:int -> d:document -> document
  | Align : req:int -> d:document -> document

let rec requirement (d:document) : int =
  match d with
  | Empty -> 0
  | Text _ n -> n
  | Blank n -> n
  | IfFlat d1 _ -> requirement d1
  | HardLine -> -1
  | Cat r _ _ -> r
  | Nest r _ _ -> r
  | Group r _ -> r
  | Align r _ -> r

let req_add (x y:int) : int = if x < 0 || y < 0 then -1 else x + y

let empty = Empty

let text (s:string) (len:int) : document =
  if S.length s = 0 then Empty else Text s (if len < 0 then 0 else len)

(* [sub_doc s i len] is the code points [i, i+len) of [s]. *)
let sub_doc (s:string) (i:nat) (len:nat{i + len <= S.length s}) : document =
  if len = 0 then Empty else Text (S.sub s i len) len

let clamped_sub (s:string) (ofs len:int) : string =
  let n = S.length s in
  let ofs : nat = if ofs < 0 then 0 else if ofs > n then n else ofs in
  let len : nat = if len < 0 then 0 else if ofs + len > n then n - ofs else len in
  S.sub s ofs len

let pad3 (n:int) : string =
  if n < 10 then "00" ^ string_of_int n
  else if n < 100 then "0" ^ string_of_int n
  else string_of_int n

(* PPrint's [OCaml.char], which is OCaml's ["%C"]. *)
let char_literal (c:char) : string =
  let n = U32.v (u32_of_char c) in
  let body =
    if c = '\'' then "\\'"
    else if c = '\\' then "\\\\"
    else if c = '\n' then "\\n"
    else if c = '\t' then "\\t"
    else if c = '\r' then "\\r"
    else if n = 8 then "\\b"
    else if n >= 32 && n <= 126 then S.make 1 c
    else if n < 256 then "\\" ^ pad3 n
    else S.make 1 c in
  "'" ^ body ^ "'"

let string_doc (s:string) : document = text s (S.length s)

let doc_of_char c = string_doc (char_literal c)
let doc_of_string s = string_doc s
let doc_of_bool b = string_doc (if b then "true" else "false")
let substring s ofs len = string_doc (clamped_sub s ofs len)
let fancystring s apparent_length = text s apparent_length
let fancysubstring s ofs len apparent_length = text (clamped_sub s ofs len) apparent_length
let utf8string s = string_doc s
let hardline = HardLine
let blank n = if n <= 0 then Empty else Blank n
let break_ n = IfFlat (blank n) HardLine

let ( ^^ ) x y =
  match x with
  | Empty -> y
  | _ -> (match y with
          | Empty -> x
          | _ -> Cat (req_add (requirement x) (requirement y)) x y)

let ( ^/^ ) x y = x ^^ (break_ 1 ^^ y)

let nest j d =
  match d with
  | Empty -> Empty
  | _ -> Nest (requirement d) j d

let group d =
  match d with
  | Empty -> Empty
  | _ -> let r = requirement d in if r < 0 then d else Group r d

let ifflat d1 d2 =
  match d1 with
  | IfFlat d1' _ -> IfFlat d1' d2
  | Empty -> (match d2 with Empty -> Empty | _ -> IfFlat d1 d2)
  | _ -> IfFlat d1 d2

let lparen = Text "(" 1
let rparen = Text ")" 1
let langle = Text "<" 1
let rangle = Text ">" 1
let lbrace = Text "{" 1
let rbrace = Text "}" 1
let lbracket = Text "[" 1
let rbracket = Text "]" 1
let squote = Text "'" 1
let dquote = Text "\"" 1
let bquote = Text "`" 1
let semi = Text ";" 1
let colon = Text ":" 1
let comma = Text "," 1
let space = Blank 1
let dot = Text "." 1
let sharp = Text "#" 1
let slash = Text "/" 1
let backslash = Text "\\" 1
let equals = Text "=" 1
let qmark = Text "?" 1
let tilde = Text "~" 1
let at = Text "@" 1
let percent = Text "%" 1
let dollar = Text "$" 1
let caret = Text "^" 1
let ampersand = Text "&" 1
let star = Text "*" 1
let plus = Text "+" 1
let minus = Text "-" 1
let underscore = Text "_" 1
let bang = Text "!" 1
let bar = Text "|" 1
let rarrow = Text "->" 2
let long_left_arrow = Text "<--" 3
let larrow = Text "<-" 2

let precede l x = l ^^ x
let terminate r x = x ^^ r
let enclose l r x = l ^^ (x ^^ r)
let squotes x = enclose squote squote x
let dquotes x = enclose dquote dquote x
let bquotes x = enclose bquote bquote x
let braces x = enclose lbrace rbrace x
let parens x = enclose lparen rparen x
let angles x = enclose langle rangle x
let brackets x = enclose lbracket rbracket x
let twice d = d ^^ d

let rec repeat_aux (n:int) (d acc:document) : Tot document (decreases (if n > 0 then n else 0)) =
  if n <= 0 then acc else repeat_aux (n - 1) d (d ^^ acc)

let repeat n d = repeat_aux n d empty

(* The folds build left-leaning trees, as PPrint's do. *)
let rec concat_aux (acc:document) (docs:list document) : Tot document (decreases docs) =
  match docs with
  | [] -> acc
  | d :: ds -> concat_aux (acc ^^ d) ds

let concat docs = concat_aux empty docs

let rec separate_aux (sep acc:document) (docs:list document) : Tot document (decreases docs) =
  match docs with
  | [] -> acc
  | d :: ds -> separate_aux sep (acc ^^ (sep ^^ d)) ds

let separate sep docs =
  match docs with
  | [] -> empty
  | d :: ds -> separate_aux sep d ds

let rec concat_map_aux (#a:Type) (f:a -> document) (acc:document) (xs:list a)
  : Tot document (decreases xs) =
  match xs with
  | [] -> acc
  | x :: xs -> concat_map_aux f (acc ^^ f x) xs

let concat_map #a f xs = concat_map_aux #a f empty xs

let rec separate_map_aux (#a:Type) (sep:document) (f:a -> document) (acc:document) (xs:list a)
  : Tot document (decreases xs) =
  match xs with
  | [] -> acc
  | x :: xs -> separate_map_aux sep f (acc ^^ (sep ^^ f x)) xs

let separate_map #a sep f xs =
  match xs with
  | [] -> empty
  | x :: xs -> separate_map_aux #a sep f (f x) xs

let rec separate2_aux (sep last_sep acc:document) (i n:int) (docs:list document)
  : Tot document (decreases docs) =
  match docs with
  | [] -> acc
  | d :: ds ->
    separate2_aux sep last_sep (acc ^^ ((if i < n - 1 then sep else last_sep) ^^ d)) (i + 1) n ds

let separate2 sep last_sep docs =
  match docs with
  | [] -> empty
  | d :: ds -> separate2_aux sep last_sep d 1 (FStar.List.Tot.length docs) ds

let optional #a f o =
  match o with
  | None -> empty
  | Some x -> f x

(* The first [j >= i] whose character satisfies [ok], or [n]. *)
let rec find_from (ok:char -> bool) (s:string) (n:nat{n == S.length s}) (i:nat{i <= n})
  : Tot (j:nat{i <= j /\ j <= n}) (decreases (n - i)) =
  if i = n then n
  else if ok (S.index s i) then i
  else find_from ok s n (i + 1)

let is_newline (c:char) : bool = c = '\n'
let is_space (c:char) : bool = c = ' ' || c = '\t' || c = '\n' || c = '\r'
let is_not_space (c:char) : bool = not (is_space c)

let rec lines_aux (s:string) (n:nat{n == S.length s}) (i:nat{i <= n}) (acc:list document)
  : Tot (list document) (decreases (n - i)) =
  let j = find_from is_newline s n i in
  if j < n then lines_aux s n (j + 1) (sub_doc s i (j - i) :: acc)
  else FStar.List.Tot.rev (sub_doc s i (n - i) :: acc)

let lines s = lines_aux s (S.length s) 0 []

let arbitrary_string s = separate (break_ 1) (lines s)

let rec words_aux (s:string) (n:nat{n == S.length s}) (i:nat{i <= n}) (acc:list document)
  : Tot (list document) (decreases (n - i)) =
  let i = find_from is_not_space s n i in
  if i = n then FStar.List.Tot.rev acc
  else
    let j = find_from is_space s n (i + 1) in
    words_aux s n j (sub_doc s i (j - i) :: acc)

let words s = words_aux s (S.length s) 0 []

let rec split_aux (ok:char -> bool) (s:string) (n:nat{n == S.length s}) (i:nat{i <= n})
                  (acc:list document)
  : Tot (list document) (decreases (n - i)) =
  let j = find_from ok s n i in
  if j < n then split_aux ok s n (j + 1) (Text (S.sub s j 1) 1 :: sub_doc s i (j - i) :: acc)
  else FStar.List.Tot.rev (sub_doc s i (n - i) :: acc)

let split ok s = split_aux ok s (S.length s) 0 []

let rec flow_aux (sep acc:document) (docs:list document) : Tot document (decreases docs) =
  match docs with
  | [] -> acc
  | d :: ds -> flow_aux sep (acc ^^ group (sep ^^ d)) ds

let flow sep docs =
  match docs with
  | [] -> empty
  | d :: ds -> flow_aux sep d ds

let rec flow_map_aux (#a:Type) (sep:document) (f:a -> document) (acc:document) (xs:list a)
  : Tot document (decreases xs) =
  match xs with
  | [] -> acc
  | x :: xs -> flow_map_aux sep f (acc ^^ group (sep ^^ f x)) xs

let flow_map #a sep f xs =
  match xs with
  | [] -> empty
  | x :: xs -> flow_map_aux #a sep f (f x) xs

let is_url_sep (c:char) : bool = c = '/' || c = '.'

let url s = flow (break_ 0) (split is_url_sep s)

let align d =
  match d with
  | Empty -> Empty
  | _ -> Align (requirement d) d

let hang n d = align (nest n d)
let prefix n b left right = group (left ^^ nest n (break_ b ^^ right))
let jump n b right = group (nest n (break_ b ^^ right))
let infix n b middle left right = prefix n b (left ^^ (blank b ^^ middle)) right

let surround n b opening contents closing =
  group (opening ^^ (nest n (break_ b ^^ contents) ^^ (break_ b ^^ closing)))

let soft_surround n b opening contents closing =
  group (opening ^^ (nest n (group (break_ b) ^^ contents) ^^ group (break_ b ^^ closing)))

let surround_separate n b void opening sep closing docs =
  match docs with
  | [] -> void
  | _ -> surround n b opening (separate sep docs) closing

let surround_separate_map #a n b void opening sep closing f xs =
  match xs with
  | [] -> void
  | _ -> surround n b opening (separate_map #a sep f xs) closing

(* Rendering.  [Cat] counts two so that every step of [pretty] decreases
   [size d + csize k], with [Empty] as "pop the continuation". *)
let rec size (d:document) : nat =
  match d with
  | Empty -> 0
  | IfFlat d1 d2 -> 1 + size d1 + size d2
  | Cat _ d1 d2 -> 2 + size d1 + size d2
  | Nest _ _ d -> 1 + size d
  | Group _ d -> 1 + size d
  | Align _ d -> 1 + size d
  | _ -> 1

noeq type cont =
  | KNil : cont
  | KCons : indent:int -> flatten:bool -> d:document -> k:cont -> cont

let rec csize (k:cont) : nat =
  match k with
  | KNil -> 0
  | KCons _ _ d k -> 1 + size d + csize k

(* Blanks are held back in [pending] until something follows them on the
   same line, so that no line has trailing whitespace (PPrint's [buffering]). *)
let emit (pending:int) (acc s:string) : string =
  if pending > 0 then (acc ^ S.make pending ' ') ^ s else acc ^ s

let rec pretty (width ribbon last_indent column pending:int) (acc:string)
               (indent:int) (flatten:bool) (d:document) (k:cont)
  : Tot string (decreases (size d + csize k)) =
  match d with
  | Empty ->
    (match k with
     | KNil -> acc
     | KCons i f d' k' -> pretty width ribbon last_indent column pending acc i f d' k')
  | Text s n ->
    pretty width ribbon last_indent (column + n) 0 (emit pending acc s) indent flatten Empty k
  | Blank n ->
    pretty width ribbon last_indent (column + n) (pending + n) acc indent flatten Empty k
  | HardLine ->
    pretty width ribbon indent indent indent (acc ^ "\n") indent flatten Empty k
  | IfFlat d1 d2 ->
    pretty width ribbon last_indent column pending acc indent flatten
      (if flatten then d1 else d2) k
  | Cat _ d1 d2 ->
    pretty width ribbon last_indent column pending acc indent flatten d1
      (KCons indent flatten d2 k)
  | Nest _ j d1 ->
    pretty width ribbon last_indent column pending acc (indent + j) flatten d1 k
  | Group r d1 ->
    let c = column + r in
    let flatten = flatten || (r >= 0 && c <= width && c <= last_indent + ribbon) in
    pretty width ribbon last_indent column pending acc indent flatten d1 k
  | Align _ d1 ->
    pretty width ribbon last_indent column pending acc column flatten d1 k

let pretty_doc (width ribbon:int) (d:document) : string =
  pretty width ribbon 0 0 0 "" 0 false d KNil

(* [ribbon] is [max 0 (min width (truncate (float_of_int width *. rfrac)))]:
   the largest [k] in [0, width] with [k <= width * rfrac], found by bisection
   since FStar.Float64 has no truncation. *)
let max_exact : int = 9007199254740992

let to_float (k:int{0 <= k /\ k <= max_exact}) : F.float64 =
  assert_norm (max_exact < pow2 63);
  F.of_int (I64.int_to_t k)

let rec bisect (target:F.float64) (lo:nat) (hi:int{lo < hi /\ hi <= max_exact})
  : Tot nat (decreases (hi - lo)) =
  if hi - lo <= 1 then lo
  else
    let mid = lo + (hi - lo) / 2 in
    if F.lte (to_float mid) target then bisect target mid hi else bisect target lo mid

let ribbon_of (rfrac:F.float64) (width:int) : int =
  if width <= 0 then 0
  else if width > max_exact then width
  else
    let target = F.mul (to_float width) rfrac in
    if F.lte (to_float width) target then width
    else if not (F.lte (to_float 0) target) then 0
    else bisect target 0 width

let pretty_string rfrac width d = pretty_doc width (ribbon_of rfrac width) d

let render d = pretty_doc 80 80 d
