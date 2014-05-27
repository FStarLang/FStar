(* -------------------------------------------------------------------- *)
#light "off"

module FSharp.Format

open System.IO

(* -------------------------------------------------------------------- *)
type width = Inf | Finite of int

let add_w (x : width) (y : width) =
    match x, y with
    | Inf, _ | _, Inf -> Inf
    | Finite x, Finite y -> Finite (x + y)

let le_w (x : width) (y : width) =
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
    let node = if String.length s = 0 then Empty else Text s in
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
        { node = Concat (d1, d2); width = add_w d1.width d2.width; }

(* -------------------------------------------------------------------- *)
let reduce (docs : list<doc>) =
    let fold1 (d1 : doc) (d2 : doc) =
        match d1.node, d2.node with
        | Empty, _     -> d2
        | _    , Empty -> d2
        | _    , _     -> cat d1 d2

    in List.fold fold1 empty docs

(* -------------------------------------------------------------------- *)
let combine (sep : doc) (docs : list<doc>) =
    let fold1 (d1 : doc) (d2 : doc) =
        match d1.node, d2.node with
        | Empty, _     -> d2
        | _    , Empty -> d2
        | _    , _     -> reduce [d1; sep; d2]

    in List.fold fold1 empty docs

(* -------------------------------------------------------------------- *)
let groups (docs : list<doc>) =
    group (List.fold cat empty docs)

(* -------------------------------------------------------------------- *)
let cat1 (d1 : doc) (d2 : doc) =
    reduce [d1; break1; d2]

(* -------------------------------------------------------------------- *)
let reduce1 (docs : list<doc>) =
    combine break1 docs

(* -------------------------------------------------------------------- *)
let enclose (left : doc) (right : doc) (doc : doc) =
    reduce [left; doc; right]

(* -------------------------------------------------------------------- *)
let lparen = text "("
let rparen = text ")"

let parens (doc : doc) =
    enclose lparen rparen doc

(* -------------------------------------------------------------------- *)
let align (docs : list<doc>) =
    let for1 d1 d2 = cat d1 d2 in
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
    state.output.WriteLine ();
    state.prefix <- indent;
    state.indent <- indent;
    state.column <- indent

(* -------------------------------------------------------------------- *)
let emit_blanks (state : state) (n : int) =
    if state.prefix > 0 || state.column = 0 then
        state.prefix <- state.prefix + n
    else
        state.output.Write (String.replicate n " ");
    state.column <- state.column + n

(* -------------------------------------------------------------------- *)
let emit_string (state : state) (s : string) =
    state.output.Write (s);
    if state.prefix > 0 then begin
        state.output.Write (String.replicate state.prefix " ");
        state.prefix <- 0
    end;
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
        emit_string state s;
        continue_ state cps

    | HardLF ->
        emit_crlf state cp.indent;
        continue_ state cps

    | Blank n ->
        emit_blanks state n;
        continue_ state cps

    | Nest (n, d) ->
        format state cps { indent cp n with doc = d; }

    | Concat (d1, d2) ->
        let cp1 = { cp with doc = d1 } in
        let cp2 = { cp with doc = d2 } in
        format state (cp2 :: cps) cp1

    | Group d ->
        let fit () =
            let column = add_w (Finite state.column) cp.doc.width in
               le_w column (Finite state.width)
            && le_w column (Finite (state.indent + state.ribbon)) in
        let flatten = cp.flatten || fit () in

        format state cps { cp with flatten = flatten; doc = d; }

    | MaybeFlat (d1, d2) ->
        let d = if cp.flatten then d1 else d2 in
        format state cps { cp with doc = d }

and continue_ (state : state) = function
    | []        -> ()
    | cp :: cps -> format state cps cp

(* -------------------------------------------------------------------- *)
let pretty (width : int) (d : doc) =
    let width  = max 10 width in
    let writer = new StringWriter () in

    let state = {
        width  = width;
        ribbon = (int) (0.72 * (float) width);
        indent = 0;
        prefix = 0;
        column = 0;
        output = writer :> TextWriter;
    } in

    let cp = { indent = 0; flatten = false; doc = group d; } in

    format state [] cp;
    state.output.Flush ();
    writer.ToString ()
