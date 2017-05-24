(*
   Copyright 2008-2015 Abhishek Anand, Nikhil Swamy and Microsoft Research

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
(* -------------------------------------------------------------------- *)
#light "off"

module FStar.Extraction.ML.Code
open FStar.All

open FStar
open FStar.Util
open FStar.Extraction.ML
open FStar.Extraction.ML.Syntax
open FStar.Format
open FStar.Const
open FStar.BaseTypes
module BU = FStar.Util


(* -------------------------------------------------------------------- *)
type assoc  = | ILeft | IRight | Left | Right | NonAssoc
type fixity = | Prefix | Postfix | Infix of assoc
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
let max_op_prec = (max_int, Infix NonAssoc)


(*copied from ocaml-asttrans.fs*)

(* -------------------------------------------------------------------- *)
let rec in_ns (x: (list<'a> * list<'a>)) : bool = match x with
    | [], _ -> true
    | x1::t1, x2::t2 when (x1 = x2) -> in_ns (t1, t2)
    | _, _ -> false

(* -------------------------------------------------------------------- *)
let path_of_ns (currentModule : mlsymbol) ns =
    let ns' = Util.flatten_ns ns in
    if ns' = currentModule
    then []
    else let cg_libs = Options.codegen_libs() in
         let ns_len = List.length ns in
         let found = BU.find_map cg_libs (fun cg_path ->
            let cg_len = List.length cg_path in
            if List.length cg_path < ns_len
            then let pfx, sfx = BU.first_N cg_len ns in
                 if pfx = cg_path
                 then Some (pfx@[Util.flatten_ns sfx])
                 else None
            else None) in
         match found with
            | None -> [ns']
            | Some x -> x

let mlpath_of_mlpath (currentModule : mlsymbol) (x : mlpath) : mlpath =
    match string_of_mlpath x with
    | "Prims.Some" -> ([], "Some")
    | "Prims.None" -> ([], "None")
    | _ ->
     let ns, x = x in
     (path_of_ns currentModule ns, x)

let ptsym_of_symbol (s : mlsymbol) : mlsymbol =
    if Char.lowercase (String.get s 0) <> String.get s 0
    then "l__" ^ s
    else s

let ptsym (currentModule : mlsymbol) (mlp : mlpath) : mlsymbol =
    if (List.isEmpty (fst mlp))
    then ptsym_of_symbol (snd  mlp)
    else
        let (p, s) = mlpath_of_mlpath currentModule mlp in
        String.concat "." (p @ [ptsym_of_symbol s])


let ptctor (currentModule : mlsymbol) (mlp : mlpath) : mlsymbol =
    let (p, s) = mlpath_of_mlpath currentModule mlp in
    let s = if Char.uppercase (String.get s 0) <> String.get s 0 then "U__" ^ s else s in
    String.concat "." (p @ [s])

(* -------------------------------------------------------------------- *)
let infix_prim_ops = [
    ("op_Addition"       , e_bin_prio_op1   , "+" );
    ("op_Subtraction"    , e_bin_prio_op1   , "-" );
    ("op_Multiply"       , e_bin_prio_op1   , "*" );
    ("op_Division"       , e_bin_prio_op1   , "/" );
    ("op_Equality"       , e_bin_prio_eq    , "=" );
    ("op_Colon_Equals"   , e_bin_prio_eq    , ":=");
    ("op_disEquality"    , e_bin_prio_eq    , "<>");
    ("op_AmpAmp"         , e_bin_prio_and   , "&&");
    ("op_BarBar"         , e_bin_prio_or    , "||");
    ("op_LessThanOrEqual"   , e_bin_prio_order , "<=");
    ("op_GreaterThanOrEqual", e_bin_prio_order , ">=");
    ("op_LessThan"          , e_bin_prio_order , "<" );
    ("op_GreaterThan"       , e_bin_prio_order , ">" );
    ("op_Modulus"           , e_bin_prio_order , "mod" );
]

(* -------------------------------------------------------------------- *)
let prim_uni_ops = [
    ("op_Negation", "not");
    ("op_Minus", "~-");
    ("op_Bang","Support.ST.read")
]

(* -------------------------------------------------------------------- *)
let prim_types = []

(* -------------------------------------------------------------------- *)
let prim_constructors = [
    ("Some", "Some");
    ("None", "None");
    ("Nil",  "[]");
    ("Cons", "::");
]

(* -------------------------------------------------------------------- *)
let is_prims_ns (ns : list<mlsymbol>) =
    ns = ["Prims"]

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
let is_standard_type (p : mlpath) = false

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
  let noparens _inner _outer side =
    let (pi, fi) = _inner in
    let (po, fo) = _outer in
    (pi > po) ||
     (match (fi, side) with
      | Postfix    , Left     -> true
      | Prefix     , Right    -> true
      | Infix Left , Left     -> (pi = po) && (fo = Infix Left )
      | Infix Right, Right    -> (pi = po) && (fo = Infix Right)
      | Infix Left , ILeft    -> (pi = po) && (fo = Infix Left )
      | Infix Right, IRight   -> (pi = po) && (fo = Infix Right)
      | _          , NonAssoc -> (pi = po) && (fi = fo)
      | _          , _        -> false)
  in

  if noparens inner outer side then doc else parens doc

(* -------------------------------------------------------------------- *)
let escape_byte_hex (x: byte) =
  "\\x" ^ hex_string_of_byte x

let escape_char_hex (x: char) =
  escape_byte_hex (byte_of_char x)

(* -------------------------------------------------------------------- *)
let escape_or fallback = function
  | c when (c = '\\')            -> "\\\\"
  | c when (c = ' ' )            -> " "
  | c when (c = '\b')            -> "\\b"
  | c when (c = '\t')            -> "\\t"
  | c when (c = '\r')            -> "\\r"
  | c when (c = '\n')            -> "\\n"
  | c when (c = '\'')            -> "\\'"
  | c when (c = '\"')            -> "\\\""
  | c when (is_letter_or_digit c)-> string_of_char c
  | c when (is_punctuation c)    -> string_of_char c
  | c when (is_symbol c)         -> string_of_char c
  | c                            -> fallback c


(* -------------------------------------------------------------------- *)
let string_of_mlconstant (sctt : mlconstant) =
  match sctt with
  | MLC_Unit -> "()"
  | MLC_Bool true  -> "true"
  | MLC_Bool false -> "false"
  | MLC_Char c -> "'"^ escape_or escape_char_hex c ^"'"
  | MLC_Int (s, Some (Signed, Int32)) -> s ^"l"
  | MLC_Int (s, Some (Signed, Int64)) -> s ^"L"
  | MLC_Int (s, Some (_, Int8))
  | MLC_Int (s, Some (_, Int16)) -> s
  | MLC_Int (s, None) -> "(Prims.parse_int \"" ^s^ "\")"
  | MLC_Float d -> string_of_float d

  | MLC_Bytes bytes ->
      (* A byte buffer. Not meant to be readable. *)
      "\"" ^ FStar.Bytes.f_encode escape_byte_hex bytes ^ "\""

  | MLC_String chars ->
      (* It was a string literal. Escape what was (likely) escaped originally.
         Leave everything else as is. That way, we get the OCaml semantics,
         which is that strings are series of bytes, and that if you happen to
         provide some well-formed UTF-8 sequence (e.g. "héhé", which has length
         6), then you get the same well-formed UTF-8 sequence on exit. It is up
         to userland to provide some UTF-8 compatible functions (e.g.
         utf8_length). *)
      "\"" ^ String.collect (escape_or string_of_char) chars ^ "\""

  | _ -> failwith "TODO: extract integer constants properly into OCaml"


(* -------------------------------------------------------------------- *)
let rec doc_of_mltype' (currentModule : mlsymbol) (outer : level) (ty : mlty) =
    match ty with
    | MLTY_Var x ->
        let escape_tyvar s =
            if BU.starts_with s "'_" //this denotes a weak type variable in OCaml; it cannot be written in source programs
            then BU.replace_char s '_' 'u'
            else s in
        text (escape_tyvar <| idsym x)

    | MLTY_Tuple tys ->
        let doc = List.map (doc_of_mltype currentModule (t_prio_tpl, Left)) tys in
        let doc = parens (hbox (combine (text " * ") doc)) in
        doc

    | MLTY_Named (args, name) -> begin
        let args =
            match args with
            | []    -> empty
            | [arg] -> doc_of_mltype currentModule (t_prio_name, Left) arg
            | _     ->
                let args = List.map (doc_of_mltype currentModule (min_op_prec, NonAssoc)) args in
                parens (hbox (combine (text ", ") args))

        in

        let name = ptsym currentModule name in

        hbox (reduce1 [args; text name])
    end

    | MLTY_Fun (t1, _, t2) ->
        let d1 = doc_of_mltype currentModule (t_prio_fun, Left ) t1 in
        let d2 = doc_of_mltype currentModule (t_prio_fun, Right) t2 in
        maybe_paren outer t_prio_fun (hbox (reduce1 [d1; text " -> "; d2]))

    | MLTY_Top ->
      if Util.codegen_fsharp()
      then text "obj"
      else text "Obj.t"

and doc_of_mltype (currentModule : mlsymbol) (outer : level) (ty : mlty) =
    doc_of_mltype' currentModule outer (Util.resugar_mlty ty)

(* -------------------------------------------------------------------- *)
let rec doc_of_expr (currentModule : mlsymbol) (outer : level) (e : mlexpr) : doc =
    match e.expr with
    | MLE_Coerce (e, t, t') ->
      let doc = doc_of_expr currentModule (min_op_prec, NonAssoc) e in
      if Util.codegen_fsharp()
      then parens (reduce [text "Prims.checked_cast"; doc])
      else parens (reduce [text "Obj.magic "; parens doc])

    | MLE_Seq es ->
        let docs = List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) es in
        let docs = List.map (fun d -> reduce [d; text ";"; hardline]) docs in
        parens (reduce docs)

    | MLE_Const c ->
        text (string_of_mlconstant c)

    | MLE_Var (x, _) ->
        text x

    | MLE_Name path ->
        text (ptsym currentModule path)

    | MLE_Record (path, fields) ->
        let for1 (name, e) =
            let doc = doc_of_expr currentModule (min_op_prec, NonAssoc) e in
            reduce1 [text (ptsym currentModule (path, name)); text "="; doc] in

        cbrackets (combine (text "; ") (List.map for1 fields))

    | MLE_CTor (ctor, []) ->
       let name =
         if is_standard_constructor ctor then
           snd (Option.get (as_standard_constructor ctor))
         else
           ptctor currentModule  ctor in
        text name

    | MLE_CTor (ctor, args) ->
       let name =
         if is_standard_constructor ctor then
           snd (Option.get (as_standard_constructor ctor))
         else
           ptctor currentModule  ctor in
        let args = List.map (doc_of_expr currentModule (min_op_prec, NonAssoc)) args in
        let doc =
          match name, args with
            (* Special case for Cons *)
            | "::", [x;xs] -> reduce [parens x; text "::"; xs]
            | _, _ -> reduce1 [text name; parens (combine (text ", ") args)] in
        maybe_paren outer e_app_prio doc

    | MLE_Tuple es ->
        let docs = List.map (fun x -> parens (doc_of_expr currentModule (min_op_prec, NonAssoc) x)) es in
        let docs = parens (combine (text ", ") docs) in
        docs

    | MLE_Let ((rec_, _, lets), body) ->
        let pre =
            if e.loc <> dummy_loc
            then reduce [hardline; doc_of_loc e.loc]
            else empty
        in
        let doc  = doc_of_lets currentModule (rec_, false, lets) in
        let body = doc_of_expr  currentModule (min_op_prec, NonAssoc) body in
        parens (combine hardline [pre; doc; reduce1 [text "in"; body]])

    | MLE_App (e, args) -> begin
        match e.expr, args with
        | MLE_Name p, [
            ({ expr = MLE_Fun ([ _ ], scrutinee) });
            ({ expr = MLE_Fun ([ (arg, _) ], possible_match)})
          ] when (string_of_mlpath p = "FStar.All.try_with") ->
            let branches =
              match possible_match with
              | ({ expr = MLE_Match ({ expr = MLE_Var arg' }, branches) }) when (idsym arg = idsym arg') ->
                  branches
              | e ->
                  (* F* may reduce [match ... with ... -> e | ... -> e] into [e]. *)
                  [ (MLP_Wild, None, e) ]
            in
            doc_of_expr currentModule outer ({
              expr = MLE_Try (scrutinee, branches);
              mlty = possible_match.mlty;
              loc = possible_match.loc
            })
        | (MLE_Name p, [e1; e2]) when is_bin_op p -> doc_of_binop currentModule p e1 e2

        | (MLE_App ({expr=MLE_Name p},[unitVal]), [e1; e2]) when (is_bin_op p && unitVal=ml_unit) ->
                     doc_of_binop currentModule p e1 e2

        | (MLE_Name p, [e1]) when is_uni_op p -> doc_of_uniop currentModule p e1

        | (MLE_App ({expr=MLE_Name p},[unitVal]), [e1]) when (is_uni_op p  && unitVal=ml_unit) -> doc_of_uniop currentModule p e1

        | _ ->
            let e    = doc_of_expr  currentModule (e_app_prio, ILeft) e in
            let args = List.map (doc_of_expr currentModule  (e_app_prio, IRight)) args in
            parens (reduce1 (e :: args))
    end

    | MLE_Proj (e, f) ->
       let e = doc_of_expr  currentModule  (min_op_prec, NonAssoc) e in
       let doc =
        if Util.codegen_fsharp() //field names are not qualified in F#
        then reduce [e; text "."; text (snd f)]
        else reduce [e; text "."; text (ptsym currentModule f)] in
       doc

    | MLE_Fun (ids, body) ->
        let bvar_annot x xt =
            if Util.codegen_fsharp() //type inference in F# is not complete, particularly for field projections; so these annotations are needed
            then reduce1 [text "("; text x ;
                          (match xt with | Some xxt -> reduce1 [text " : "; doc_of_mltype currentModule outer xxt] | _ -> text "");
                          text ")"]
            else text x in
        let ids  = List.map (fun ((x, _),xt) -> bvar_annot x (Some xt)) ids in
        let body = doc_of_expr currentModule (min_op_prec, NonAssoc) body in
        let doc  = reduce1 [text "fun"; reduce1 ids; text "->"; body] in
        parens doc

    | MLE_If (cond, e1, None) ->
        let cond = doc_of_expr currentModule  (min_op_prec, NonAssoc) cond in
        let doc  =
            combine hardline [
                reduce1 [text "if"; cond; text "then"; text "begin"];
                doc_of_expr currentModule  (min_op_prec, NonAssoc) e1;
                text "end"
            ]

        in maybe_paren outer e_bin_prio_if doc

    | MLE_If (cond, e1, Some e2) ->
        let cond = doc_of_expr currentModule  (min_op_prec, NonAssoc) cond in
        let doc  =
            combine hardline [
                reduce1 [text "if"; cond; text "then"; text "begin"];
                doc_of_expr currentModule  (min_op_prec, NonAssoc) e1;
                reduce1 [text "end"; text "else"; text "begin"];
                doc_of_expr currentModule  (min_op_prec, NonAssoc) e2;
                text "end"
            ]

        in maybe_paren outer e_bin_prio_if doc

    | MLE_Match (cond, pats) ->
        let cond = doc_of_expr currentModule  (min_op_prec, NonAssoc) cond in
        let pats = List.map (doc_of_branch currentModule) pats in
        let doc  = reduce1 [text "match"; parens cond; text "with"] :: pats in
        let doc  = combine hardline doc in

        parens doc

    | MLE_Raise (exn, []) ->
        reduce1 [text "raise"; text (ptctor currentModule  exn)]

    | MLE_Raise (exn, args) ->
        let args = List.map (doc_of_expr currentModule  (min_op_prec, NonAssoc)) args in
        reduce1 [text "raise"; text (ptctor currentModule  exn); parens (combine (text ", ") args)]

    | MLE_Try (e, pats) ->
        combine hardline [
            text "try";
            doc_of_expr currentModule (min_op_prec, NonAssoc) e;
            text "with";
            combine hardline (List.map (doc_of_branch currentModule) pats)
        ]
and  doc_of_binop currentModule p e1 e2 : doc =
        let (_, prio, txt) = Option.get (as_bin_op p) in
        let e1  = doc_of_expr  currentModule (prio, Left ) e1 in
        let e2  = doc_of_expr  currentModule (prio, Right) e2 in
        let doc = reduce1 [e1; text txt; e2] in
        parens doc

and  doc_of_uniop currentModule p e1  : doc =
        let (_, txt) = Option.get (as_uni_op p) in
        let e1  = doc_of_expr  currentModule  (min_op_prec, NonAssoc ) e1 in
        let doc = reduce1 [text txt; parens e1] in
        parens doc
(* -------------------------------------------------------------------- *)
and doc_of_pattern (currentModule : mlsymbol) (pattern : mlpattern) : doc =
    match pattern with
    | MLP_Wild     -> text "_"
    | MLP_Const  c -> text (string_of_mlconstant c)
    | MLP_Var    x -> text (fst x)

    | MLP_Record (path, fields) ->
        let for1 (name, p) = reduce1 [text (ptsym currentModule  (path, name)); text "="; doc_of_pattern currentModule p] in
        cbrackets (combine (text "; ") (List.map for1 fields))

    | MLP_CTor (ctor, []) ->
       let name =
         if is_standard_constructor ctor then
           snd (Option.get (as_standard_constructor ctor))
         else
           ptctor currentModule  ctor in
        text name

    | MLP_CTor (ctor, pats) ->
       let name =
         if is_standard_constructor ctor then
           snd (Option.get (as_standard_constructor ctor))
         else
           ptctor currentModule  ctor in
       let doc =
         match name, pats with
           (* Special case for Cons *)
           | "::", [x;xs] -> reduce [parens (doc_of_pattern currentModule x); text "::"; doc_of_pattern currentModule xs]
           | _, [MLP_Tuple _] -> reduce1 [text name; doc_of_pattern currentModule (List.hd pats)] //no redundant parens; particularly if we have (T of a * b), we must generate T (x, y) not T ((x, y))
           | _ -> reduce1 [text name; parens (combine (text ", ") (List.map (doc_of_pattern currentModule) pats))] in
       maybe_paren (min_op_prec, NonAssoc) e_app_prio doc

    | MLP_Tuple ps ->
        let ps = List.map (doc_of_pattern currentModule) ps in
        parens (combine (text ", ") ps)

    | MLP_Branch ps ->
        let ps = List.map (doc_of_pattern currentModule) ps in
        let ps = List.map parens ps in
        combine (text " | ") ps

(* -------------------------------------------------------------------- *)
and doc_of_branch (currentModule : mlsymbol) ((p, cond, e) : mlbranch) : doc =
    let case =
        match cond with
        | None   -> reduce1 [text "|"; doc_of_pattern currentModule p]
        | Some c ->
            let c = doc_of_expr currentModule  (min_op_prec, NonAssoc) c in
            reduce1 [text "|"; doc_of_pattern currentModule p; text "when"; c] in

    combine hardline [
        reduce1 [case; text "->"; text "begin"];
        doc_of_expr currentModule  (min_op_prec, NonAssoc) e;
        text "end";
    ]

(* -------------------------------------------------------------------- *)
and doc_of_lets (currentModule : mlsymbol) (rec_, top_level, lets) =
    let for1 {mllb_name=name; mllb_tysc=tys; mllb_def=e; print_typ=pt} =
        let e   = doc_of_expr currentModule  (min_op_prec, NonAssoc) e in
        let ids = [] in //TODO: maybe extract the top-level binders from e and print it alongside name
        //let f x = x
        //let f = fun x -> x
        //i.e., print the latter as the former
        let ids = List.map (fun (x, _) -> text x) ids in
        let ty_annot =
            if (not pt) then text ""
            else
            if Util.codegen_fsharp () && (rec_ = Rec || top_level) //needed for polymorphic recursion and to overcome incompleteness of type inference in F#
            then match tys with
                    | Some (_::_, _) | None -> //except, emitting binders for type variables in F# sometimes also requires emitting type constraints; which is not yet supported
                      text ""
                    | Some ([], ty) ->
                      let ty = doc_of_mltype currentModule (min_op_prec, NonAssoc) ty in
                      reduce1 [text ":"; ty]
//                      let ids = List.map (fun (x, _) -> text x) ids in
//                      begin match ids with
//                        | [] -> reduce1 [text ":"; ty]
//                        | _ ->  reduce1 [text "<"; combine (text ", ") ids; text ">"; text ":"; ty]
//                      end
            else if top_level
            then match tys with
                    | None | Some (_::_, _) -> text ""
                    | Some ([], ty) ->
                      let ty = doc_of_mltype currentModule (min_op_prec, NonAssoc) ty in
//                      let vars = vars |> List.map (fun x -> doc_of_mltype currentModule (min_op_prec, NonAssoc) (MLTY_Var x)) |>  reduce1  in
                      reduce1 [text ":"; ty]
            else text "" in
        reduce1 [text (idsym name); reduce1 ids; ty_annot; text "="; e] in

    let letdoc = if rec_ = Rec then reduce1 [text "let"; text "rec"] else text "let" in

    let lets = List.map for1 lets in
    let lets = List.mapi (fun i doc ->
        reduce1 [(if i = 0 then letdoc else text "and"); doc])
        lets in

    combine hardline lets


and doc_of_loc (lineno, file) =
    if (Options.no_location_info()) || Util.codegen_fsharp () then
        empty
    else
        let file = BU.basename file in
        reduce1 [ text "#"; num lineno; text ("\"" ^ file ^ "\"") ]

(* -------------------------------------------------------------------- *)
let doc_of_mltydecl (currentModule : mlsymbol) (decls : mltydecl) =
    let for1 (_, x, mangle_opt, tparams, body) =
        let x = match mangle_opt with
                | None -> x
                | Some y -> y in
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
                doc_of_mltype currentModule  (min_op_prec, NonAssoc) ty

            | MLTD_Record fields -> begin
                let forfield (name, ty) =
                    let name = text name in
                    let ty   = doc_of_mltype currentModule  (min_op_prec, NonAssoc) ty in
                    reduce1 [name; text ":"; ty]

                in cbrackets (combine (text "; ") (List.map forfield fields))
            end

            | MLTD_DType ctors ->
                let forctor (name, tys) =
                    match tys with
                    | [] -> text name
                    | _  ->
                        let tys = List.map (doc_of_mltype currentModule  (t_prio_tpl, Left)) tys in
                        let tys = combine (text " * ") tys in
                        reduce1 [text name; text "of"; tys]
                in

                let ctors = List.map forctor ctors in
                let ctors = List.map (fun d -> reduce1 [text "|"; d]) ctors in
                combine hardline ctors

        in

        let doc = reduce1 [tparams; text (ptsym currentModule  ([], x))] in

        match body with
        | None      -> doc
        | Some body ->
            let body = forbody body in
            combine hardline [reduce1 [doc; text "="]; body]

    in

    let doc = List.map for1 decls in
    let doc = if (List.length doc >0) then reduce1 [text "type"; combine (text " \n and ") doc] else text "" in
    doc

(* -------------------------------------------------------------------- *)
let rec doc_of_sig1 currentModule s =
    match s with
    | MLS_Mod (x, subsig) ->
        combine hardline
            [reduce1 [text "module"; text x; text "="];
             doc_of_sig currentModule subsig;
             reduce1 [text "end"]]

    | MLS_Exn (x, []) ->
        reduce1 [text "exception"; text x]

    | MLS_Exn (x, args) ->
        let args = List.map (doc_of_mltype currentModule  (min_op_prec, NonAssoc)) args in
        let args = parens (combine (text " * ") args) in
        reduce1 [text "exception"; text x; text "of"; args]

    | MLS_Val (x, (_, ty)) ->
        let ty = doc_of_mltype currentModule  (min_op_prec, NonAssoc) ty in
        reduce1 [text "val"; text x; text ": "; ty]

    | MLS_Ty decls ->
        doc_of_mltydecl currentModule decls

(* -------------------------------------------------------------------- *)
and doc_of_sig (currentModule : mlsymbol) (s : mlsig) =
    let docs = List.map (doc_of_sig1 currentModule) s in
    let docs = List.map (fun x -> reduce [x; hardline; hardline]) docs in
    reduce docs


(* -------------------------------------------------------------------- *)
let doc_of_mod1 (currentModule : mlsymbol) (m : mlmodule1) =
    match m with
    | MLM_Exn (x, []) ->
        reduce1 [text "exception"; text x]

    | MLM_Exn (x, args) ->
        let args = List.map (doc_of_mltype currentModule  (min_op_prec, NonAssoc)) args in
        let args = parens (combine (text " * ") args) in
        reduce1 [text "exception"; text x; text "of"; args]

    | MLM_Ty decls ->
        doc_of_mltydecl currentModule decls

    | MLM_Let (rec_, _, lets) ->
      doc_of_lets currentModule (rec_, true, lets)

    | MLM_Top e ->
        reduce1 [
            text "let"; text "_"; text "=";
            doc_of_expr currentModule  (min_op_prec, NonAssoc) e
        ]

    | MLM_Loc loc ->
        doc_of_loc loc

(* -------------------------------------------------------------------- *)
let doc_of_mod (currentModule : mlsymbol) (m : mlmodule) =
    let docs = List.map (fun x ->
        let doc = doc_of_mod1 currentModule x in
        [doc; (match x with | MLM_Loc _ -> empty | _ -> hardline); hardline]) m in
    reduce (List.flatten docs)

(* -------------------------------------------------------------------- *)
let rec doc_of_mllib_r (MLLib mllib) =
    let rec for1_sig (x, sigmod, MLLib sub) =
        let x = Util.flatten_mlpath x in
        let head = reduce1 [text "module"; text x; text ":"; text "sig"] in
        let tail = reduce1 [text "end"] in
        let doc  = Option.map (fun (s, _) -> doc_of_sig x s) sigmod in
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
    and for1_mod istop (mod_name, sigmod, MLLib sub) =
        let target_mod_name = Util.flatten_mlpath mod_name in
        let maybe_open_pervasives =
            match mod_name with
            | ["FStar"], "Pervasives" -> []
            | _ ->
              let pervasives = Util.flatten_mlpath (["FStar"], "Pervasives") in
              [hardline;
               text ("open " ^ pervasives)]
        in
        let head = reduce1 (if Util.codegen_fsharp()
                            then [text "module";  text target_mod_name]
                            else if not istop
                            then [text "module";  text target_mod_name; text "="; text "struct"]
                            else []) in
        let tail = if not istop
                   then reduce1 [text "end"]
                   else reduce1 [] in
        let doc  = Option.map (fun (_, m) -> doc_of_mod target_mod_name m) sigmod in
        let sub  = List.map (for1_mod false)  sub in
        let sub  = List.map (fun x -> reduce [x; hardline; hardline]) sub in
        let prefix = if Util.codegen_fsharp () then [cat (text "#light \"off\"") hardline] else [] in
        reduce <| (prefix @ [
            head;
            hardline;
            text "open Prims"] @
            maybe_open_pervasives @
            [hardline;
            (match doc with
             | None   -> empty
             | Some s -> cat s hardline);
            reduce sub;
            cat tail hardline;
        ])

    in

    let docs = List.map (fun (x,s,m) ->
      (Util.flatten_mlpath x,for1_mod true (x,s,m))) mllib in
    docs

(* -------------------------------------------------------------------- *)
let doc_of_mllib mllib =
    doc_of_mllib_r mllib

let string_of_mlexpr cmod (e:mlexpr) =
    let doc = doc_of_expr (Util.flatten_mlpath cmod) (min_op_prec, NonAssoc) e in
    FStar.Format.pretty 0 doc

let string_of_mlty (cmod) (e:mlty) =
    let doc = doc_of_mltype (Util.flatten_mlpath cmod) (min_op_prec, NonAssoc) e in
    FStar.Format.pretty 0 doc
