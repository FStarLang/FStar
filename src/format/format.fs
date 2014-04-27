(* -------------------------------------------------------------------- *)
module FSharp.OCaml.Format

(* -------------------------------------------------------------------- *)
type doc = { node: node; width: int; }

and node =
| Text   of string
| Concat of doc * doc
| Group  of doc
| Line

type width = int

let (&.) (s : string) : doc =
    { node = Text s; width = String.length s; }

let (+.) (d1 : doc) (d2 : doc) : doc =
    { node  = Concat (d1, d2);
      width = d1.width + d2.width; }

let endl : doc =
    { node = Line; width = 1; }

let group (d : doc) =
    { node = Group d; width = d.width; }

(* -------------------------------------------------------------------- *)
let tostring (w : width) (doc : doc) =
    let rec format (fit, wleft) doc =
        match doc.node with
        | Text s ->
            (s, wleft - String.length s)
        | Line ->
            if fit then (" " , wleft-1) else ("\r\n", w)
        | Group d ->
            format (fit || d.width <= wleft, wleft) d
        | Concat (d1, d2) ->
            let (s1, wleft1) = format (fit, wleft ) d1
            let (s2, wleft2) = format (fit, wleft1) d2
            (s1 + s2, wleft2)

    fst (format (false, w) doc)
