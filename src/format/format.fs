(* -------------------------------------------------------------------- *)
#light "off"

module FStar.Format
open Prims
module PP = FStar.Pprint
(* -------------------------------------------------------------------- *)
type doc = Doc of PP.document

(* -------------------------------------------------------------------- *)
let empty    = Doc PP.empty
let hardline = Doc PP.hardline

(* -------------------------------------------------------------------- *)
let text (s : string) = Doc (PP.arbitrary_string s)
let num (i : int) = Doc (PP.arbitrary_string (string_of_int i))

(* -------------------------------------------------------------------- *)
let break_ (i : int   ) = Doc (PP.break_ i)

let break0 = break_ 0
let break1 = text " "

(* -------------------------------------------------------------------- *)
let enclose (Doc l) (Doc r) (Doc x) =
    Doc (PP.enclose l r x)

let brackets (Doc d : doc) = Doc (PP.brackets d)
let cbrackets (d : doc) = enclose (text "{") (text "}") d
let parens   (Doc d : doc) = Doc (PP.parens d)

(* -------------------------------------------------------------------- *)
let cat (Doc d1) (Doc d2) = Doc (PP.(^^) d1 d2)

(* -------------------------------------------------------------------- *)
let reduce (docs : list<doc>) =
  List.fold cat empty docs

(* -------------------------------------------------------------------- *)
let group (Doc d : doc) = Doc (PP.group d)

(* -------------------------------------------------------------------- *)
let groups (docs : list<doc>) =
  group (reduce docs)

(* -------------------------------------------------------------------- *)
let combine (Doc sep : doc) (docs : list<doc>) =
  let select (Doc d) = if d = PP.empty then None else Some d in
  let docs = List.choose select docs in
  Doc (PP.separate sep docs)

(* -------------------------------------------------------------------- *)
let cat1 (d1 : doc) (d2 : doc) =
    reduce [d1; break1; d2]

(* -------------------------------------------------------------------- *)
let reduce1 (docs : list<doc>) =
    combine break1 docs

(* -------------------------------------------------------------------- *)
let nest (i : int) (Doc d : doc) =
    Doc (PP.nest i d)

(* -------------------------------------------------------------------- *)
let align (docs : list<doc>) =
    let (Doc doc) = combine hardline docs in
    Doc (PP.align doc)

(* -------------------------------------------------------------------- *)
let hbox (d : doc) = d (* FIXME *)

(* -------------------------------------------------------------------- *)
let pretty (sz : int) (Doc doc : doc) : string =
    PP.pretty_string 0.8 sz doc