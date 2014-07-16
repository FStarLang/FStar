(* -------------------------------------------------------------------- *)
#light "off"

module Microsoft.FStar.Backends.OCaml.Code

open System
open System.Text

open Microsoft.FStar.Backends.OCaml.Syntax
open FSharp.Format

(* -------------------------------------------------------------------- *)
type assoc  = ILeft | IRight | Left | Right | NonAssoc
type fixity = Prefix | Postfix | Infix of assoc
type opprec = int * fixity
type level  = opprec * assoc

let t_prio_fun  = (10, Infix Right)
let t_prio_tpl  = (20, Infix NonAssoc)
let t_prio_name = (30, Postfix)

let e_bin_prio_lambda = ( 5, Prefix)
let e_bin_prio_if     = (15, Prefix)
let e_bin_prio_letin  = (19, Prefix)
let e_bin_prio_or     = (20, Infix Left)
let e_bin_prio_and    = (25, Infix Left)
let e_bin_prio_eq     = (27, Infix NonAssoc)
let e_bin_prio_order  = (29, Infix NonAssoc)
let e_bin_prio_op1    = (30, Infix Left)
let e_bin_prio_op2    = (40, Infix Left)
let e_bin_prio_op3    = (50, Infix Left)
let e_bin_prio_op4    = (60, Infix Left)
let e_bin_prio_seq    = (100, Infix Left)
let e_app_prio        = (10000, Infix Left)

let min_op_prec = (-1, Infix NonAssoc)
let max_op_prec = (System.Int32.MaxValue, Infix NonAssoc)

(* -------------------------------------------------------------------- *)
let maybe_paren (outer, side) inner doc =
  let noparens ((pi, fi) as _inner) ((po, fo) as _outer) side =
    (pi > po) ||
      match fi, side with
      | Postfix    , Left     -> true
      | Prefix     , Right    -> true
      | Infix Left , Left     -> (pi = po) && (fo = Infix Left )
      | Infix Right, Right    -> (pi = po) && (fo = Infix Right)
      | Infix Left , ILeft    -> (pi = po) && (fo = Infix Left )
      | Infix Right, IRight   -> (pi = po) && (fo = Infix Right)
      | _          , NonAssoc -> (pi = po) && (fi = fo)
      | _          , _        -> false
  in

  if noparens inner outer side then doc else parens doc

(* -------------------------------------------------------------------- *)
let ocaml_u8_codepoint (i : byte) =
  if (int)i = 0 then "" else sprintf "\\x%x" i

(* -------------------------------------------------------------------- *)
let encode_char c =
  if (int)c > 127 then // Use UTF-8 encoding
    let bytes = System.String (c, 1) in
    let bytes = (new UTF8Encoding (false, true)).GetBytes(bytes) in
    String.concat "" (Array.map ocaml_u8_codepoint bytes)
  else
    match c with
    | c when Char.IsLetterOrDigit(c) -> System.String (c, 1)
    | c when Char.IsPunctuation(c)   -> System.String (c, 1)
    | c when c = ' '                 -> " "
    | c when c = '\t'                -> "\\t"
    | c when c = '\r'                -> "\\r"
    | c when c = '\n'                -> "\\n"
    | _                              -> ocaml_u8_codepoint ((byte)c)

(* -------------------------------------------------------------------- *)
let string_of_mlconstant (sctt : mlconstant) =
  match sctt with
  | MLC_Unit           -> "()"
  | MLC_Bool     true  -> "true"
  | MLC_Bool     false -> "false"
  | MLC_Char     c     -> sprintf "'%s'" (encode_char c)
  | MLC_Byte     c     -> sprintf "'%s'" (ocaml_u8_codepoint c)
  | MLC_Int      i     -> sprintf "%d" i // FIXME
  | MLC_Float    d     -> sprintf "%f" d

  | MLC_Bytes bytes ->
      let bytes = Array.map ocaml_u8_codepoint bytes in
      sprintf "\"%s\"" (String.concat "" bytes)

  | MLC_String chars ->
      let chars = String.collect encode_char chars in
      sprintf "\"%s\"" chars

(* -------------------------------------------------------------------- *)
let rec doc_of_expr (outer : level) (e : mlexpr) : doc =
    match e with
    | MLE_Seq es ->
        let docs = List.map (doc_of_expr (min_op_prec, NonAssoc)) es in
        let docs = List.map (fun d -> reduce [d; text ";"; hardline]) docs in
        reduce docs

    | MLE_Const c ->
        text (string_of_mlconstant c)

    | MLE_Var (x, _) ->
        text x

    | MLE_Name path ->
        text (ptsym path)

    | MLE_Record (_, fields) ->
        let for1 (name, e) =
            let doc = doc_of_expr (min_op_prec, NonAssoc) e in
            reduce1 [text name; text "="; doc] in

        let doc = List.map for1 fields in
        let doc = List.map (fun d -> cat d (text ";")) doc in
        let doc = reduce [text "{"; reduce1 doc; text "}"] in

        doc

    | MLE_CTor (ctor, []) ->
        text (ptsym ctor)

    | MLE_CTor (ctor, args) ->
        let args = List.map (doc_of_expr (min_op_prec, NonAssoc)) args in
        reduce1 [text (ptsym ctor); parens (combine (text ", ") args)]

    | MLE_Tuple es ->
        let docs = List.map (doc_of_expr (min_op_prec, NonAssoc)) es in
        let docs = parens (combine (text ", ") docs) in
        docs

    | MLE_Let (rec_, lets, body) ->
        let doc  = doc_of_lets (rec_, lets) in
        let body = doc_of_expr (min_op_prec, NonAssoc) body in
        combine hardline [doc; reduce1 [text "in"; body]]

    | MLE_App (e, args) ->
        let e    = doc_of_expr (e_app_prio, ILeft) e in
        let args = List.map (doc_of_expr (e_app_prio, IRight)) args in
        maybe_paren outer e_app_prio (reduce1 (e :: args))

    | MLE_Fun (ids, body) ->
        let ids  = List.map (fun (x, _) -> text x) ids in
        let body = doc_of_expr (min_op_prec, NonAssoc) body in
        let doc  = reduce1 [text "fun"; reduce1 ids; text "->"; body] in
        maybe_paren outer e_bin_prio_lambda doc

    | MLE_If (cond, e1, None) ->
        let cond = doc_of_expr (min_op_prec, NonAssoc) cond in
        let doc  =
            combine hardline [
                reduce1 [text "if"; cond; text "then"; text "begin"];
                doc_of_expr (min_op_prec, NonAssoc) e1;
                text "end"
            ]

        in maybe_paren outer e_bin_prio_if doc

    | MLE_If (cond, e1, Some e2) ->
        let cond = doc_of_expr (min_op_prec, NonAssoc) cond in
        let doc  =
            combine hardline [
                reduce1 [text "if"; cond; text "then"; text "begin"];
                doc_of_expr (min_op_prec, NonAssoc) e1;
                reduce1 [text "end"; text "else"; text "begin"];
                doc_of_expr (min_op_prec, NonAssoc) e2;
                text "end"
            ]

        in maybe_paren outer e_bin_prio_if doc

    | MLE_Match (cond, pats) ->
        let cond = doc_of_expr (min_op_prec, NonAssoc) cond in
        let pats = List.map doc_of_branch pats in
        let doc  = reduce1 [text "match"; parens cond; text "with"] :: pats in
        let doc  = combine hardline doc in

        maybe_paren outer e_bin_prio_if doc

    | MLE_Raise (exn, []) ->
        reduce1 [text "raise"; text (ptsym exn)]

    | MLE_Raise (exn, args) ->
        let args = List.map (doc_of_expr (min_op_prec, NonAssoc)) args in
        reduce1 [text "raise"; parens (combine (text ", ") args)]

    | MLE_Try (e, pats) ->
        combine hardline [
            reduce1 [text "try"; text "begin"];
            doc_of_expr (min_op_prec, NonAssoc) e;
            reduce1 [text "end"; text "with"];
            (combine hardline (List.map doc_of_branch pats))
        ]

(* -------------------------------------------------------------------- *)
and doc_of_pattern (pattern : mlpattern) : doc =
    match pattern with
    | MLP_Wild     -> text "_"
    | MLP_Const  c -> text (string_of_mlconstant c)
    | MLP_Var    x -> text (fst x)

    | MLP_Record (_, fields) ->
        let for1 (name, p) = reduce1 [text name; text "="; doc_of_pattern p] in
        brackets (combine (text "; ") (List.map for1 fields))

    | MLP_CTor (p, []) ->
        text (ptsym p)

    | MLP_CTor (p, ps) ->
        let ps = List.map doc_of_pattern ps in
        reduce1 [text (ptsym p); parens (combine (text ", ") ps)]

    | MLP_Tuple ps ->
        let ps = List.map doc_of_pattern ps in
        parens (combine (text ", ") ps)

    | MLP_Branch ps ->
        let ps = List.map doc_of_pattern ps in
        let ps = List.map parens ps in
        combine (text " | ") ps

(* -------------------------------------------------------------------- *)
and doc_of_branch ((p, cond, e) : mlbranch) : doc =
    let case =
        match cond with
        | None   -> reduce1 [text "|"; doc_of_pattern p]
        | Some c ->
            let c = doc_of_expr (min_op_prec, NonAssoc) c in
            reduce1 [text "|"; doc_of_pattern p; text "when"; c] in

    combine hardline [
        reduce1 [case; text "->"; text "begin"];
        doc_of_expr (min_op_prec, NonAssoc) e;
        text "end";
    ]

(* -------------------------------------------------------------------- *)
and doc_of_lets (rec_, lets) =
    let for1 (name, ids, e) =
        let e   = doc_of_expr (min_op_prec, NonAssoc) e in
        let ids = List.map (fun (x, _) -> text x) ids in
        reduce1 [text (fst name); reduce1 ids; text "="; e] in

    let letdoc = if rec_ then reduce1 [text "let"; text "rec"] else text "let" in

    let lets = List.map for1 lets in
    let lets = List.mapi (fun i doc ->
        reduce1 [(if i = 0 then letdoc else text "and"); doc])
        lets in

    combine hardline lets

(* -------------------------------------------------------------------- *)
let rec doc_of_mltype (outer : level) (ty : mlty) =
    match ty with
    | MLTY_Var x ->
        text (idsym x)

    | MLTY_Tuple tys ->
        let doc = List.map (doc_of_mltype (min_op_prec, NonAssoc)) tys in
        let doc = parens (hbox (combine (text " * ") doc)) in
        doc

    | MLTY_Named (args, name) -> begin
        let args =
            match args with
            | []    -> empty
            | [arg] -> doc_of_mltype (t_prio_name, Left) arg
            | _     ->
                let args = List.map (doc_of_mltype (min_op_prec, NonAssoc)) args in
                parens (hbox (combine (text ", ") args))

        in hbox (reduce1 [args; text (ptsym name)])
    end

    | MLTY_Fun (t1, t2) ->
        let d1 = doc_of_mltype (t_prio_fun, Left ) t1 in
        let d2 = doc_of_mltype (t_prio_fun, Right) t2 in

        maybe_paren outer t_prio_fun (hbox (reduce1 [d1; text " -> "; d2]))

(* -------------------------------------------------------------------- *)
let doc_of_mltydecl (decls : mltydecl) =
    let for1 (x, tparams, _) =
        let tparams =
            match tparams with
            | []  -> empty
            | [x] -> text (idsym x)
            | _   ->
                let doc = List.map (fun x -> (text (idsym x))) tparams in
                parens (combine (text ", ") doc) in

        reduce1 [tparams; text x] in

    let doc = List.map for1 decls in
    let doc = reduce1 [text "type"; combine (text " and ") doc] in
    doc

(* -------------------------------------------------------------------- *)
let doc_of_sig1 (s : mlsig1) =
    match s with
    | MLS_Exn (x, []) ->
        reduce1 [text "exception"; text x]

    | MLS_Exn (x, args) ->
        let args = List.map (doc_of_mltype (min_op_prec, NonAssoc)) args in
        let args = parens (combine (text " * ") args) in
        reduce1 [text "exception"; text x; text "of"; args]

    | MLS_Val (x, (_, ty)) ->
        let ty = doc_of_mltype (min_op_prec, NonAssoc) ty in
        reduce1 [text "val"; text x; text ": "; ty]

    | MLS_Ty decls ->
        doc_of_mltydecl decls

(* -------------------------------------------------------------------- *)
let doc_of_mod1 (m : mlmodule1) =
    match m with
    | MLM_Exn (x, []) ->
        reduce1 [text "exception"; text x]

    | MLM_Exn (x, args) ->
        let args = List.map (doc_of_mltype (min_op_prec, NonAssoc)) args in
        let args = parens (combine (text " * ") args) in
        reduce1 [text "exception"; text x; text "of"; args]

    | MLM_Ty decls ->
        doc_of_mltydecl decls

    | MLM_Let (rec_, lets) ->
        let lets = List.map (fun (x, y, z) -> ((x, -1), y, z)) lets in
        doc_of_lets (rec_, lets)

    | MLM_Top e ->
        reduce1 [
            text "let"; text "_"; text "=";
            doc_of_expr (min_op_prec, NonAssoc) e
        ]

(* -------------------------------------------------------------------- *)
let doc_of_sig (s : mlsig) =
    let docs = List.map doc_of_sig1 s in
    let docs = List.map (fun x -> reduce [x; hardline; hardline]) docs in
    reduce docs

(* -------------------------------------------------------------------- *)
let doc_of_mod (m : mlmodule) =
    let docs = List.map doc_of_mod1 m in
    let docs = List.map (fun x -> reduce [x; hardline; hardline]) docs in
    reduce docs

(* -------------------------------------------------------------------- *)
let rec doc_of_mllib (MLLib mllib : mllib) =
    let for1 (x, sigmod, sub) =
        let head = reduce1 [text "module"; text x; text ":"; text "sig"] in
        let mid  = reduce1 [text "end"; text "="; text "struct"] in
        let tail = reduce1 [text "end"] in
        let doc  = Option.map (fun (s, m) -> (doc_of_sig s, doc_of_mod m)) sigmod in
        let sub  = doc_of_mllib sub in

        reduce [
            cat head hardline;
            (match doc with
             | None        -> empty
             | Some (s, m) -> reduce [
                    cat s   hardline;
                    cat mid hardline;
                    cat m   hardline;
                ]);
            sub;
            cat tail hardline;
        ]
    in

    let docs = List.map for1 mllib in
    let docs = List.map (fun x -> reduce[x; hardline; hardline]) docs in

    reduce docs

