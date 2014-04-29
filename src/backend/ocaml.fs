(* -------------------------------------------------------------------- *)
module Microsoft.FStar.Backends.OCaml

open System
open System.Text

open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Absyn.Util
open Microsoft.FStar.Backends.NameEnv

open FSharp.Format

(* -------------------------------------------------------------------- *)
let unexpected () =
    failwith "ocaml-backend-unexpected-construction"

(* -------------------------------------------------------------------- *)
let unsupported () =
    failwith "ocaml-backend-unsupported-construction"

(* -------------------------------------------------------------------- *)
let ocaml_u8_codepoint (i : byte) =
  if (int)i = 0 then "" else sprintf "\\x%x" i

(* -------------------------------------------------------------------- *)
let encode_char c =
  if (int)c > 127 then // Use UTF-8 encoding
    let bytes = System.String (c, 1)
    let bytes = (new UTF8Encoding (false, true)).GetBytes(bytes)
    bytes
      |> Array.map ocaml_u8_codepoint
      |> String.concat ""
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
let string_of_sconst sctt =
  match sctt with
  | Const_unit         -> "()"
  | Const_char   c     -> sprintf "'%s'" (encode_char c)
  | Const_uint8  c     -> sprintf "'%s'" (ocaml_u8_codepoint c)
  | Const_int32  i     -> sprintf "%d" i // FIXME
  | Const_int64  i     -> sprintf "%d" i // FIXME
  | Const_bool   true  -> "true"
  | Const_bool   false -> "false"
  | Const_float  d     -> sprintf "%f" d

  | Const_bytearray (bytes, _) ->
      let bytes = bytes |> Array.map ocaml_u8_codepoint
      sprintf "\"%s\"" (bytes |> String.concat "")

  | Const_string (bytes, _) ->
      let chars = (new UTF8Encoding (false, true)).GetString(bytes)
      let chars = chars |> String.collect encode_char
      sprintf "\"%s\"" chars

(* -------------------------------------------------------------------- *)
let is_prim_ns (ns : list<ident>) =
    match ns with
    | [{ idText = "Prims" }] -> true
    | _ -> false

(* -------------------------------------------------------------------- *)
let is_op_equality (x : lident) =
    is_prim_ns x.ns && x.ident.idText = "op_Equality"

(* -------------------------------------------------------------------- *)
let name_of_let_ident (x : either<bvvdef,lident>) =
    match x with
    | Inl x -> x.realname.idText
    | Inr x -> x.ident.idText

(* -------------------------------------------------------------------- *)
let string_of_primop (_env : env) (x : string) =
    x

(* -------------------------------------------------------------------- *)
let rec doc_of_exp (env : env) (e : exp) =
    let e = Absyn.Util.compress_exp e in

    match Absyn.Util.destruct_app e with
    | (Exp_fvar (x, _), [(e1, _); (e2, _)]) when is_op_equality x.v ->
        let d1 = doc_of_exp env e1
        let d2 = doc_of_exp env e2
        d1 +. %"=" +. d2

    | _ ->
        match e with
        | Exp_bvar x ->
            %(resolve env x.v.realname.idText)

        | Exp_fvar (x, _) ->
            %(x.v.ident.idText)

        | Exp_constant c ->
            %(string_of_sconst c)

        | Exp_abs (x, _, e) ->
            let lenv = push env x.realname.idText x.ppname.idText
            let x    = resolve lenv x.realname.idText
            let d    = doc_of_exp lenv e
            %"fun" +. %x +. %"->" +. d

        | Exp_app (e1, e2, _) ->
            let d1 = doc_of_exp env e1 in
            let d2 = doc_of_exp env e2 in
            (paren d1) +. (paren d2)

        | Exp_match (e, bs) ->
            let de = doc_of_exp env e
            let bs = bs |> List.map (fun b -> %"|" +. doc_of_branch env b)
            %"match" +. de +. %"with" +. (List.reduce (+.) bs)

        | Exp_let ((rec_, lb), body) ->
            let downct (x, _, e) =
                match x with
                | Inl x -> (x, e)
                | Inr _ -> unexpected ()
            let kw = if rec_ then "let rec" else "let"
            let lenv, ds = lb |> List.map downct |> Util.fold_map (doc_of_let rec_) env
            %kw +. (join %"and" (ds |> List.map group)) +. %"in" +. (doc_of_exp lenv body)

        | Exp_primop (x, es) ->
            let x = string_of_primop env x.idText
            if   List.isEmpty es
            then %x
            else %x +. (groups (es |> List.map (doc_of_exp env)))

        | Exp_ascribed (e, _) ->
            doc_of_exp env e

        | Exp_meta (Meta_info (e, _, _)) ->
            doc_of_exp env e

        | Exp_meta (Meta_dataapp e) ->
            doc_of_exp env e

        | Exp_meta (Meta_datainst (e, _)) ->
            doc_of_exp env e

        | Exp_uvar _ -> unexpected  ()
        | Exp_tabs _ -> unsupported ()
        | Exp_tapp _ -> unsupported ()

(* -------------------------------------------------------------------- *)
and doc_of_constr (env : env) c args =
    let x = c.ident.idText
    match args with
    | [] -> %x
    | _  -> %x +. group (paren (join %", " args))

(* -------------------------------------------------------------------- *)
and doc_of_let (rec_ : bool) (env : env) (x, e) =
    let lenv = push env x.realname.idText x.ppname.idText
    let x    = resolve lenv x.realname.idText
    let d    = doc_of_exp (if rec_ then lenv else env) e
    lenv, %x +. %"=" +. d

(* -------------------------------------------------------------------- *)
and doc_of_toplet (rec_ : bool) (env : env) (x, e) =
    let lenv = push env x.idText x.idText
    let x    = resolve lenv x.idText

    let bds, e = destruct_fun e
    let benv, args =
        Util.fold_map
            (fun lenv (x, _) ->
                let lenv = push lenv x.realname.idText x.ppname.idText
                let x    = resolve lenv x.realname.idText
                (lenv, %x))
            (if rec_ then lenv else env) bds
    let d = doc_of_exp benv e

    lenv, %x +. (group (join %" " args)) +. %"=" +. d

(* -------------------------------------------------------------------- *)
and doc_of_pattern env (p : pat) : env * doc =
    match p with
    | Pat_cons (x, ps) ->
        let env, ds = ps |> Util.fold_map doc_of_pattern env
        (env, doc_of_constr env x ds)

    | Pat_var x ->
        let env = push env x.realname.idText x.ppname.idText
        (env, %(resolve env x.realname.idText))

    | Pat_constant c ->
        (env, %(string_of_sconst c))

    | Pat_disj ps ->
        let env, ds = ps |> Util.fold_map doc_of_pattern env
        (env, paren (join %"|" ds))

    | Pat_wild ->
        (env, %"_")

    | Pat_withinfo (p, _) ->
        doc_of_pattern env p

    | Pat_tvar  _ -> unsupported ()
    | Pat_twild _ -> unsupported ()

(* -------------------------------------------------------------------- *)
and doc_of_branch (env : env) ((p, cl, body) : pat * exp option * exp) : doc =
    let env, pd = doc_of_pattern env p
    let dwhen = cl |> Option.map (doc_of_exp env)
    let dbody = body |> doc_of_exp env 

    match dwhen with
    | None -> pd +. %"->" +. dbody
    | Some dwhen -> pd +. %"when" +. (paren dwhen) +. %"->" +. dbody

(* -------------------------------------------------------------------- *)
let doc_of_modelt (env : env) (modx : sigelt) : env * doc option =
    match modx with
    | Sig_let (rec_, lb) ->
        let downct (x, _, e) =
            match x with
            | Inr x -> (x.ident, e)
            | Inl _ -> unexpected ()
        let kw = if rec_ then "let rec" else "let"
        let env, ds = lb |> List.map downct |> Util.fold_map (doc_of_toplet rec_) env
        env, Some (%kw +. (join %"and" (ds |> List.map group)))

    | Sig_main e ->
        env, Some (%"let" +. %"_" +. %"=" +. (doc_of_exp env e))

    | Sig_tycon _ ->
        env, Some %"tycon"

    | Sig_typ_abbrev _ ->
        env, Some %"abbrev"

    | Sig_datacon _ ->
        env, Some %"datacon"

    | Sig_bundle _ ->
        env, Some %"bundle"

    | Sig_assume         _ -> env, None
    | Sig_val_decl       _ -> env, None
    | Sig_logic_function _ -> env, None

(* -------------------------------------------------------------------- *)
let pp_module (mod_ : modul) =
    let env = NameEnv.create [mod_.name.str]
    let env, parts = mod_.declarations |> Util.choose_map doc_of_modelt env

    sprintf "module %s = struct\n%s\nend"
        mod_.name.ident.idText
        (parts |> List.map (FSharp.Format.tostring 80) |> String.concat "\n\n")
