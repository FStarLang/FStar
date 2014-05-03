(* -------------------------------------------------------------------- *)
module FSharp.Format

open System.IO

(* -------------------------------------------------------------------- *)
type width = Inf | Finite of int

let inline (+&) (x : width) (y : width) =
    match x, y with
    | Inf, _ | _, Inf -> Inf
    | Finite x, Finite y -> Finite (x + y)

let inline (<=&) (x : width) (y : width) =
    match x, y with
    | Finite _, Inf      -> true
    | Inf     , Finite _ -> false
    | Inf     , Inf      -> true 
    | Finite x, Finite y -> (x <= y)

(* -------------------------------------------------------------------- *)
type node =
| Empty
| HardLF

| Blank     of int
| Text      of string
| MaybeFlat of doc * doc
| Group     of doc
| Concat    of doc * doc
| Nest      of int * doc

and doc = { node: node; width: width; }

(* -------------------------------------------------------------------- *)
let rec unflat (d : doc) =
    match d.node with
    | MaybeFlat (d, _) -> unflat d
    | _ -> d

(* -------------------------------------------------------------------- *)
let empty =
    { node = Empty; width = Finite 0; }

let hardline =
    { node = HardLF; width = Inf; }

let text (s : string) =
    let node = if String.length s = 0 then Empty else Text s
    { node = node; width = Finite (String.length s); }

let blank (n : int) =
    text (String.replicate (max n 0) " ")

let maybeflat (d1 : doc) (d2 : doc) =
    let d1 = unflat d1 in
    { node = MaybeFlat (d1, d2); width = d1.width; }

let break_ (n : int) =
    maybeflat (blank n) hardline

let break0 = break_ 0
let break1 = break_ 1

let group (d : doc) =
    match d.width with
    | Finite _ -> { node = Group d; width = d.width; }
    | Inf -> d

let nest (i : int) (d : doc) =
    { node = Nest (i, d); width = d.width; }

let cat (d1 : doc) (d2 : doc) =
    match d1.node, d2.node with
    | Empty, _     -> d2
    | _    , Empty -> d1
    | _    , _     ->
        { node = Concat (d1, d2); width = d1.width +& d2.width; }

(* -------------------------------------------------------------------- *)
let (~%) = fun s -> text s
let (@.) = fun d1 d2 -> cat d1 d2
let (+.) = fun d1 d2 -> d1 @. break1 @. d2

(* -------------------------------------------------------------------- *)
let enclose (left : string) (right : string) (doc : doc) =
    %left @. doc @. %right

let parens (doc : doc) =
    enclose "(" ")" doc

(* -------------------------------------------------------------------- *)
let join (sep : string) (docs : list<doc>) =
    let fold1 (d1 : doc) (d2 : doc) =
        match d1.node, d2.node with
        | Empty, _     -> d2
        | _    , Empty -> d2
        | _    , _     -> d1 +. %sep +. d2

    List.fold fold1 empty docs

(* -------------------------------------------------------------------- *)
let joins (docs : list<doc>) =
    let fold1 (d1 : doc) (d2 : doc) =
        match d1.node, d2.node with
        | Empty, _     -> d2
        | _    , Empty -> d2
        | _    , _     -> d1 +. d2

    List.fold fold1 empty docs

(* -------------------------------------------------------------------- *)
let groups (docs : list<doc>) =
    group (List.fold cat empty docs)

(* -------------------------------------------------------------------- *)
let align (docs : list<doc>) =
    let for1 d1 d2 = d1 +. d2
    List.fold for1 empty docs

(* -------------------------------------------------------------------- *)
type state = {
    (*---*) width  : int;
    (*---*) ribbon : int;
    mutable column : int;
    mutable indent : int;
    mutable prefix : int;
    (*---*) output : TextWriter;
}

type stack1 = {
    indent  : int;
    flatten : bool;
    doc     : doc;
}

type stack = list<stack1>

(* -------------------------------------------------------------------- *)
let emit_crlf (state : state) (indent : int) =
    state.output.WriteLine ()
    state.prefix <- indent
    state.indent <- indent
    state.column <- indent

(* -------------------------------------------------------------------- *)
let emit_blanks (state : state) (n : int) =
    if state.prefix > 0 || state.column = 0 then
        state.prefix <- state.prefix + n
    else
        state.output.Write (String.replicate n " ")
    state.column <- state.column + n

(* -------------------------------------------------------------------- *)
let emit_string (state : state) (s : string) =
    state.output.Write (s)
    if state.prefix > 0 then
        state.output.Write (String.replicate state.prefix " ")
        state.prefix <- 0
    state.column <- state.column + s.Length

(* -------------------------------------------------------------------- *)
let indent (cp : stack1) (n : int) =
    { cp with indent = cp.indent + n }

(* -------------------------------------------------------------------- *)
let rec format (state : state) (cps : stack) (cp : stack1) =
    match cp.doc.node with
    | Empty ->
        continue_ state cps

    | Text s ->
        emit_string state s
        continue_ state cps

    | HardLF ->
        emit_crlf state cp.indent
        continue_ state cps

    | Blank n ->
        emit_blanks state n
        continue_ state cps

    | Nest (n, d) ->
        format state cps { indent cp n with doc = d; }

    | Concat (d1, d2) ->
        let cp1 = { cp with doc = d1 }
        let cp2 = { cp with doc = d2 }
        format state (cp2 :: cps) cp1

    | Group d ->
        let fit () =
            let column = (Finite state.column) +& cp.doc.width in
               column <=& Finite state.width
            && column <=& Finite (state.indent + state.ribbon)
        let flatten = cp.flatten || fit ()

        format state cps { cp with flatten = flatten; doc = d; }

    | MaybeFlat (d1, d2) ->
        let d = if cp.flatten then d1 else d2
        format state cps { cp with doc = d }

and continue_ (state : state) = function
    | []        -> ()
    | cp :: cps -> format state cps cp

(* -------------------------------------------------------------------- *)
let pretty (width : int) (d : doc) =
    let width  = max 10 width
    let writer = new StringWriter ()

    let state = {
        width  = width;
        ribbon = (int) (0.72 * (float) width);
        indent = 0;
        prefix = 0;
        column = 0;
        output = writer :> TextWriter;
    }

    let cp = { indent = 0; flatten = false; doc = group d; }

    format state [] cp
    state.output.Flush ()
    writer.ToString ()
