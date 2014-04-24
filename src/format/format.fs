(* -------------------------------------------------------------------- *)
module FSharp.OCaml.Format

(* -------------------------------------------------------------------- *)
type doc =
| Text   of string
| Concat of doc * doc
| Group  of doc
| Line

type width = int

let (&.) (s : string) : doc =
    Text s

let (+.) (d1 : doc) (d2 : doc) : doc =
    Concat (d1, d2)

let endl : doc =
    Line

let group (d : doc) =
    Group d

(* -------------------------------------------------------------------- *)
let rec width = function
    | Text   x        -> String.length x
    | Line            -> 1
    | Concat (d1, d2) -> width d1 + width d2
    | Group  d        -> width d

(* -------------------------------------------------------------------- *)
let tostring (w : width) (doc : doc) =
    let rec format (fit, wleft) = function
    | Text s ->
        (s, wleft - String.length s)
    | Line ->
        if fit then (" " , wleft-1) else ("\r\n", w)
    | Group d ->
        format (fit || width d <= wleft, wleft) d
    | Concat (d1, d2) ->
        let (s1, wleft1) = format (fit, wleft ) d1
        let (s2, wleft2) = format (fit, wleft1) d2
        (s1 + s2, wleft2)

    fst (format (false, w) doc)

