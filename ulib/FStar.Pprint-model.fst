(* Model implementation of FStar.Pprint: verified, but never extracted (the real implementation is native).
   A document is modeled as the string it renders to on a single line. *)
module FStar.Pprint

type document = | D : s:string -> document

let empty = D ""
let doc_of_char c = D (FStar.String.string_of_char c)
let doc_of_string s = D s
let doc_of_bool b = D (if b then "true" else "false")
let substring s _ _ = D s
let fancystring s _ = D s
let fancysubstring s _ _ _ = D s
let utf8string s = D s
let hardline = D "\n"

let rec spaces (n:int) : Tot string (decreases (if n > 0 then n else 0)) =
  if n <= 0 then "" else " " ^ spaces (n - 1)

let blank n = D (spaces n)
let break_ n = D (spaces n)
let ( ^^ ) x y = D (D?.s x ^ D?.s y)
let ( ^/^ ) x y = x ^^ break_ 1 ^^ y
let nest _ d = d
let group d = d
let ifflat d _ = d

let lparen = D "("
let rparen = D ")"
let langle = D "<"
let rangle = D ">"
let lbrace = D "{"
let rbrace = D "}"
let lbracket = D "["
let rbracket = D "]"
let squote = D "'"
let dquote = D "\""
let bquote = D "`"
let semi = D ";"
let colon = D ":"
let comma = D ","
let space = D " "
let dot = D "."
let sharp = D "#"
let slash = D "/"
let backslash = D "\\"
let equals = D "="
let qmark = D "?"
let tilde = D "~"
let at = D "@"
let percent = D "%"
let dollar = D "$"
let caret = D "^"
let ampersand = D "&"
let star = D "*"
let plus = D "+"
let minus = D "-"
let underscore = D "_"
let bang = D "!"
let bar = D "|"
let rarrow = D "->"
let long_left_arrow = D "<--"
let larrow = D "<-"

let precede l x = l ^^ x
let terminate r x = x ^^ r
let enclose l r x = l ^^ x ^^ r
let squotes = enclose squote squote
let dquotes = enclose dquote dquote
let bquotes = enclose bquote bquote
let braces = enclose lbrace rbrace
let parens = enclose lparen rparen
let angles = enclose langle rangle
let brackets = enclose lbracket rbracket
let twice d = d ^^ d

let rec repeat n d : Tot document (decreases (if n > 0 then n else 0)) =
  if n <= 0 then empty else d ^^ repeat (n - 1) d

let rec concat docs =
  match docs with
  | [] -> empty
  | d :: ds -> d ^^ concat ds

let rec separate sep docs =
  match docs with
  | [] -> empty
  | [d] -> d
  | d :: ds -> d ^^ sep ^^ separate sep ds

let concat_map f xs = concat (FStar.List.Tot.map f xs)
let separate_map sep f xs = separate sep (FStar.List.Tot.map f xs)

let rec separate2 sep last_sep docs =
  match docs with
  | [] -> empty
  | [d] -> d
  | [d1; d2] -> d1 ^^ last_sep ^^ d2
  | d :: ds -> d ^^ sep ^^ separate2 sep last_sep ds

let optional f o =
  match o with
  | None -> empty
  | Some x -> f x

let lines s = [D s]
let arbitrary_string s = D s
let words s = [D s]
let split _ s = [D s]
let flow sep docs = separate sep docs
let flow_map sep f xs = separate_map sep f xs
let url s = D s
let align d = d
let hang _ d = d
let prefix _ b left right = left ^^ blank b ^^ right
let jump _ b right = blank b ^^ right
let infix _ b middle left right = left ^^ blank b ^^ middle ^^ blank b ^^ right
let surround _ b opening contents closing =
  opening ^^ blank b ^^ contents ^^ blank b ^^ closing
let soft_surround n b opening contents closing = surround n b opening contents closing
let surround_separate n b void opening sep closing docs =
  match docs with
  | [] -> void
  | _ -> surround n b opening (separate sep docs) closing
let surround_separate_map n b void opening sep closing f xs =
  surround_separate n b void opening sep closing (FStar.List.Tot.map f xs)

let pretty_string _ _ d = D?.s d
let render d = D?.s d
