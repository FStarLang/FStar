(* -------------------------------------------------------------------- *)
#light "off"

module FStar.Format
open FSharp
open FSharp.PPrint
open FSharp.Compatibility.OCaml

(* -------------------------------------------------------------------- *)
type doc = Doc of PPrint.Engine.document

(* -------------------------------------------------------------------- *)
let empty    = Doc Engine.empty
let hardline = Doc Engine.hardline

(* -------------------------------------------------------------------- *)
let text (s : string) = Doc (Engine.string s)
let num (i : int) = Doc (Engine.string (string_of_int i))

(* -------------------------------------------------------------------- *)
let break_ (i : int   ) = Doc (Engine.break_ i)

let break0 = break_ 0
let break1 = text " "

(* -------------------------------------------------------------------- *)
let enclose (Doc l) (Doc r) (Doc x) =
    Doc (Combinators.enclose l r x)

let brackets (Doc d : doc) = Doc (Combinators.brackets d)
let cbrackets (d : doc) = enclose (text "{") (text "}") d
let parens   (Doc d : doc) = Doc (Combinators.parens d)

(* -------------------------------------------------------------------- *)
let cat (Doc d1) (Doc d2) = Doc (Engine.(^^) d1 d2)

(* -------------------------------------------------------------------- *)
let reduce (docs : list<doc>) =
  List.fold cat empty docs

(* -------------------------------------------------------------------- *)
let group (Doc d : doc) = Doc (Engine.group d)

(* -------------------------------------------------------------------- *)
let groups (docs : list<doc>) =
  group (reduce docs)

(* -------------------------------------------------------------------- *)
let combine (Doc sep : doc) (docs : list<doc>) =
  let select (Doc d) = if d = Engine.empty then None else Some d in
  let docs = List.choose select docs in
  Doc (Combinators.separate sep docs)

(* -------------------------------------------------------------------- *)
let cat1 (d1 : doc) (d2 : doc) =
    reduce [d1; break1; d2]

(* -------------------------------------------------------------------- *)
let reduce1 (docs : list<doc>) =
    combine break1 docs

(* -------------------------------------------------------------------- *)
let nest (i : int) (Doc d : doc) =
    Doc (Engine.nest i d)

(* -------------------------------------------------------------------- *)
let align (docs : list<doc>) =
    let (Doc doc) = combine hardline docs in
    Doc (Engine.align doc)

(* -------------------------------------------------------------------- *)
let hbox (d : doc) = d (* FIXME *)

(* -------------------------------------------------------------------- *)
let pretty (sz : int) (Doc doc : doc) : string =
    FStar.Pprint.pretty_string 0.8 sz doc
//    let buffer = Buffer.create 0 in
//    PPrint.Engine.ToBuffer.pretty 0.8 sz buffer doc;
//    Buffer.contents buffer
