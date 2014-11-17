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
let e_bin_prio_comb   = (70, Infix Left)
let e_bin_prio_seq    = (100, Infix Left)
let e_app_prio        = (10000, Infix Left)

let min_op_prec = (-1, Infix NonAssoc)
let max_op_prec = (System.Int32.MaxValue, Infix NonAssoc)

(* -------------------------------------------------------------------- *)
let infix_prim_ops = [
    ("op_Addition"       , e_bin_prio_op1   , "+" );
    ("op_Subtraction"    , e_bin_prio_op1   , "-" );
    ("op_Equality"       , e_bin_prio_eq    , "=" );
    ("op_ColonEquals"    , e_bin_prio_eq    , ":=");
    ("op_disEquality"    , e_bin_prio_eq    , "<>");
    ("op_AmpAmp"         , e_bin_prio_and   , "&&");
    ("op_BarBar"         , e_bin_prio_or    , "||");
    (* ("pipe_left"      , e_bin_prio_comb  , "<|"); *)
    (* ("pipe_right"     , e_bin_prio_comb  , "|>"); *)

    ("op_LessThanOrEqual"   , e_bin_prio_order , "<=");
    ("op_GreaterThanOrEqual", e_bin_prio_order , ">=");
    ("op_LessThan"          , e_bin_prio_order , "<" );
    ("op_GreaterThan"       , e_bin_prio_order , ">" );
]

(* -------------------------------------------------------------------- *)
let prim_uni_ops = [
    ("op_Negation", "not");
    ("op_Minus", "-");
    ("exit", "exit");
    ("failwith", "failwith");
    ("raise", "raise");
]

(* -------------------------------------------------------------------- *)
let prim_types = [
    ("char", "char");
    ("bool", "bool");
    ("string", "string");
    ("unit", "unit");
    ("ref", "ref");
    ("array", "array");
    ("option", "option");
    ("list", "list");
    (* ("int32", "Int32.t"); *)
    ("int64", "Int64.t");
]

(* -------------------------------------------------------------------- *)
let prim_constructors = [
    ("Some", "Some");
    ("None", "None");
    ("Nil", "[]");
    ("Cons", "::");
]

(* -------------------------------------------------------------------- *)
let is_prims_ns (ns : list<mlsymbol>) =
    ns = ["Fstar"; "Support"; "Prims"]

(* -------------------------------------------------------------------- *)
let as_bin_op ((ns, x) : mlpath) =
    if is_prims_ns ns then
        List.tryFind (fun (y, _, _) -> x = y) infix_prim_ops
    else
        None

(* -------------------------------------------------------------------- *)
let is_bin_op (p : mlpath) =
    as_bin_op p <> None

(* -------------------------------------------------------------------- *)
let as_uni_op ((ns, x) : mlpath) =
    if is_prims_ns ns then
        List.tryFind (fun (y, _) -> x = y) prim_uni_ops
    else
        None

(* -------------------------------------------------------------------- *)
let is_uni_op (p : mlpath) =
    as_uni_op p <> None

(* -------------------------------------------------------------------- *)
let as_standard_type ((ns, x) : mlpath) =
    if is_prims_ns ns then
        List.tryFind (fun (y, _) -> x = y) prim_types
    else
        None

(* -------------------------------------------------------------------- *)
let is_standard_type (p : mlpath) =
  as_standard_type p <> None

(* -------------------------------------------------------------------- *)
let as_standard_constructor ((ns, x) : mlpath) =
    if is_prims_ns ns then
        List.tryFind (fun (y, _) -> x = y) prim_constructors
    else
        None

(* -------------------------------------------------------------------- *)
let is_standard_constructor (p : mlpath) =
  as_standard_constructor p <> None

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
    | c when c = '\\'                -> "\\\\"
    | c when c = ' '                 -> " "
    | c when c = '\b'                -> "\\b"
    | c when c = '\t'                -> "\\t"
    | c when c = '\r'                -> "\\r"
    | c when c = '\n'                -> "\\n"
    | c when c = '\''                -> "\\'"
    | c when c = '\"'                -> "\\\""
    | c when Char.IsLetterOrDigit(c) -> System.String (c, 1)
    | c when Char.IsPunctuation(c)   -> System.String (c, 1)
    | c when Char.IsSymbol(c)        -> System.String (c, 1)
    | _                              -> ocaml_u8_codepoint ((byte)c)

(* -------------------------------------------------------------------- *)
let string_of_mlconstant (sctt : mlconstant) =
  match sctt with
  | MLC_Unit           -> "()"
  | MLC_Bool     true  -> "true"
  | MLC_Bool     false -> "false"
  | MLC_Char     c     -> sprintf "'%s'" (encode_char c)
  | MLC_Byte     c     -> sprintf "'%s'" (ocaml_u8_codepoint c)
  | MLC_Int32    i     -> sprintf "%d" i
  | MLC_Int64    i     -> sprintf "%dL" i
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

    | MLE_Record (path, fields) ->
        let for1 (name, e) =
            let doc = doc_of_expr (min_op_prec, NonAssoc) e in
            reduce1 [text (ptsym (path, name)); text "="; doc] in

        cbrackets (combine (text "; ") (List.map for1 fields))

    | MLE_CTor (ctor, []) ->
       let name =
         if is_standard_constructor ctor then
           snd (Option.get (as_standard_constructor ctor))
         else
           ptctor ctor in
        text name

    | MLE_CTor (ctor, args) ->
       let name =
         if is_standard_constructor ctor then
           snd (Option.get (as_standard_constructor ctor))
         else
           ptctor ctor in
        let args = List.map (doc_of_expr (min_op_prec, NonAssoc)) args in
        let doc =
          match name, args with
            (* Special case for Cons *)
            | "::", [x;xs] -> reduce [x; text "::"; xs]
            | _, _ -> reduce1 [text name; parens (combine (text ", ") args)] in
        maybe_paren outer e_app_prio doc

    | MLE_Tuple es ->
        let docs = List.map (doc_of_expr (min_op_prec, NonAssoc)) es in
        let docs = parens (combine (text ", ") docs) in
        docs

    | MLE_Let (rec_, lets, body) ->
        let doc  = doc_of_lets (rec_, lets) in
        let body = doc_of_expr (min_op_prec, NonAssoc) body in
        maybe_paren outer e_bin_prio_letin (combine hardline [doc; reduce1 [text "in"; body]])

    | MLE_App (e, args) -> begin
        match e, args with
        | (MLE_Name p, [e1; e2]) when is_bin_op p ->
            let (_, prio, txt) = Option.get (as_bin_op p) in
            let e1  = doc_of_expr (prio, Left ) e1 in
            let e2  = doc_of_expr (prio, Right) e2 in
            let doc = reduce1 [e1; text txt; e2] in
            parens doc

        | (MLE_Name p, [e1]) when is_uni_op p ->
            let (_, txt) = Option.get (as_uni_op p) in
            let e1  = doc_of_expr (min_op_prec, NonAssoc ) e1 in
            let doc = reduce1 [text txt; parens e1] in
            parens doc

        | _ ->
            let e    = doc_of_expr (e_app_prio, ILeft) e in
            let args = List.map (doc_of_expr (e_app_prio, IRight)) args in
            parens (reduce1 (e :: args))
    end

    | MLE_Proj (e, f) ->
       let e = doc_of_expr (min_op_prec, NonAssoc) e in
       let doc = reduce [e; text "."; text (ptsym f)] in
       doc

    | MLE_Fun (ids, body) ->
        let ids  = List.map (fun (x, _) -> text x) ids in
        let body = doc_of_expr (min_op_prec, NonAssoc) body in
        let doc  = reduce1 [text "fun"; reduce1 ids; text "->"; body] in
        parens doc

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

        parens doc

    | MLE_Raise (exn, []) ->
        reduce1 [text "raise"; text (ptctor exn)]

    | MLE_Raise (exn, args) ->
        let args = List.map (doc_of_expr (min_op_prec, NonAssoc)) args in
        reduce1 [text "raise"; text (ptctor exn); parens (combine (text ", ") args)]

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

    | MLP_Record (path, fields) ->
        let for1 (name, p) = reduce1 [text (ptsym (path, name)); text "="; doc_of_pattern p] in
        cbrackets (combine (text "; ") (List.map for1 fields))

    | MLP_CTor (ctor, []) ->
       let name =
         if is_standard_constructor ctor then
           snd (Option.get (as_standard_constructor ctor))
         else
           ptctor ctor in
        text name

    | MLP_CTor (ctor, ps) ->
        let ps = List.map doc_of_pattern ps in
       let name =
         if is_standard_constructor ctor then
           snd (Option.get (as_standard_constructor ctor))
         else
           ptctor ctor in
       let doc =
         match name, ps with
           (* Special case for Cons *)
           | "::", [x;xs] -> reduce [x; text "::"; xs]
           | _, _ -> reduce1 [text name; parens (combine (text ", ") ps)] in
       maybe_paren (min_op_prec, NonAssoc) e_app_prio doc

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
        reduce1 [text (idsym name); reduce1 ids; text "="; e] in

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
        let doc = List.map (doc_of_mltype (t_prio_tpl, Left)) tys in
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

        in

        let name =
          if is_standard_type name then
            snd (Option.get (as_standard_type name))
          else
            ptsym name

        in hbox (reduce1 [args; text name])
    end

    | MLTY_Fun (t1, t2) ->
        let d1 = doc_of_mltype (t_prio_fun, Left ) t1 in
        let d2 = doc_of_mltype (t_prio_fun, Right) t2 in

        maybe_paren outer t_prio_fun (hbox (reduce1 [d1; text " -> "; d2]))

(* -------------------------------------------------------------------- *)
let doc_of_mltydecl (decls : mltydecl) =
    let for1 (x, tparams, body) =
        let tparams =
            match tparams with
            | []  -> empty
            | [x] -> text (idsym x)
            | _   ->
                let doc = List.map (fun x -> (text (idsym x))) tparams in
                parens (combine (text ", ") doc) in

        let forbody (body : mltybody) =
            match body with
            | MLTD_Abbrev ty ->
                doc_of_mltype (min_op_prec, NonAssoc) ty

            | MLTD_Record fields -> begin
                let forfield (name, ty) =
                    let name = text name in
                    let ty   = doc_of_mltype (min_op_prec, NonAssoc) ty in
                    reduce1 [name; text ":"; ty]

                in cbrackets (combine (text "; ") (List.map forfield fields))
            end

            | MLTD_DType ctors ->
                let forctor (name, tys) =
                    match tys with
                    | [] -> text name
                    | _  ->
                        let tys = List.map (doc_of_mltype (t_prio_tpl, Left)) tys in
                        let tys = combine (text " * ") tys in
                        reduce1 [text name; text "of"; tys]
                in

                let ctors = List.map forctor ctors in
                let ctors = List.map (fun d -> reduce1 [text "|"; d]) ctors in
                combine hardline ctors

        in

        let doc = reduce1 [tparams; text (ptsym ([], x))] in

        match body with
        | None      -> doc
        | Some body ->
            let body = forbody body in
            combine hardline [reduce1 [doc; text "="]; body]

    in

    let doc = List.map for1 decls in
    let doc = reduce1 [text "type"; combine (text " and ") doc] in
    doc

(* -------------------------------------------------------------------- *)
let rec doc_of_sig1 (s : mlsig1) =
    match s with
    | MLS_Mod (x, subsig) ->
        combine hardline
            [reduce1 [text "module"; text x; text "="];
             doc_of_sig subsig;
             reduce1 [text "end"]]

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
and doc_of_sig (s : mlsig) =
    let docs = List.map doc_of_sig1 s in
    let docs = List.map (fun x -> reduce [x; hardline; hardline]) docs in
    reduce docs

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
let doc_of_mod (m : mlmodule) =
    let docs = List.map doc_of_mod1 m in
    let docs = List.map (fun x -> reduce [x; hardline; hardline]) docs in
    reduce docs

(* -------------------------------------------------------------------- *)
let rec doc_of_mllib_r (MLLib mllib : mllib) =
    let rec for1_sig (x, sigmod, MLLib sub) =
        let head = reduce1 [text "module"; text x; text ":"; text "sig"] in
        let tail = reduce1 [text "end"] in
        let doc  = Option.map (fun (s, _) -> doc_of_sig s) sigmod in
        let sub  = List.map for1_sig sub in
        let sub  = List.map (fun x -> reduce [x; hardline; hardline]) sub in

        reduce [
            cat head hardline;
            (match doc with
             | None   -> empty
             | Some s -> cat s hardline);
            reduce sub;
            cat tail hardline;
        ]
    and for1_mod istop (x, sigmod, MLLib sub) =
        let head = reduce1 (if   not istop
                            then [text "module"; text x; text "="; text "struct"]
                            else [text "struct"]) in
        let tail = reduce1 [text "end"] in
        let doc  = Option.map (fun (_, m) -> doc_of_mod m) sigmod in
        let sub  = List.map (for1_mod false) sub in
        let sub  = List.map (fun x -> reduce [x; hardline; hardline]) sub in

        reduce [
            cat head hardline;
            (match doc with
             | None   -> empty
             | Some s -> cat s hardline);
            reduce sub;
            cat tail hardline;
        ]

    in

    let docs = List.combine (List.map for1_sig mllib) (List.map (for1_mod true) mllib) in
    let docs = List.map (fun (sig_, mod_) -> reduce [sig_; text "="; mod_; hardline]) docs in

    reduce docs

(* -------------------------------------------------------------------- *)
let doc_of_mllib mllib =
    doc_of_mllib_r mllib
