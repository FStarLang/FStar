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
type assoc  = ILeft | IRight | Left | Right | NonAssoc
type fixity = Prefix | Postfix | Infix of assoc
type opprec = int * fixity

let e_bin_prio_lambda = ( 5, Prefix)
let e_bin_prio_if     = (15, Prefix)
let e_bin_prio_letin  = (19, Prefix)
let e_bin_prio_eq     = (27, Infix NonAssoc)
let e_bin_prio_seq    = (35, Infix Left)
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

  if noparens inner outer side then doc else parens doc

(* -------------------------------------------------------------------- *)
let rec doc_of_ty (env : env) (ty : typ) =
    let ty = Absyn.Util.compress_typ ty in

    match ty.t with
    | Typ_refine (_, ty, _) ->
        doc_of_ty env ty

    | Typ_ascribed (ty, _) ->
        doc_of_ty env ty

    | Typ_meta (Meta_pos (ty, _)) ->
        doc_of_ty env ty

    | Typ_lam     _ -> unsupported ()
    | Typ_tlam    _ -> unsupported ()
    | Typ_dep     _ -> unsupported ()
    | Typ_meta    _ -> unexpected  ()
    | Typ_uvar    _ -> unexpected  ()
    | Typ_unknown   -> unexpected  ()

(* -------------------------------------------------------------------- *)
let rec doc_of_exp outer (env : env) (e : exp) =
    match Absyn.Util.destruct_app e with
    | (Exp_fvar (x, _), [(e1, _); (e2, _)]) when is_op_equality x.v ->
        let d1 = doc_of_exp (e_bin_prio_eq, Left ) env e1
        let d2 = doc_of_exp (e_bin_prio_eq, Right) env e2
        maybe_paren outer e_bin_prio_eq (d1 +. %"=" +. d2)

    | (e, args) when not (List.isEmpty args) ->
        let e    = e    |> doc_of_exp (e_app_prio, ILeft) env
        let args = args |> List.map (fst >> doc_of_exp (e_app_prio, IRight) env)
        maybe_paren outer e_app_prio (e +. (joins args))

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
            let d    = doc_of_exp (min_op_prec, NonAssoc) lenv e
            maybe_paren outer e_bin_prio_lambda (%"fun" +. %x +. %"->" +. d)

        | Exp_match ((Exp_fvar _ | Exp_bvar _), [p, None, e]) when Absyn.Util.is_wild_pat p ->
            doc_of_exp outer env e

        | Exp_match (e, bs) ->
            match bs with
            | [(Pat_constant (Const_bool true ), None, e1);
               (Pat_constant (Const_bool false), None, e2)]

            | [(Pat_constant (Const_bool false), None, e1);
               (Pat_constant (Const_bool true ), None, e2)] ->

                let doc = %"if"   +. (doc_of_exp (e_bin_prio_if, Left)     env e ) +.
                          %"then" +. (doc_of_exp (e_bin_prio_if, NonAssoc) env e1) +.
                          %"else" +. (doc_of_exp (e_bin_prio_if, Right   ) env e2)

                maybe_paren outer e_bin_prio_if doc

            | _ ->
                let de = doc_of_exp (min_op_prec, NonAssoc) env e
                let bs = bs |> List.map (fun b -> %"|" +. doc_of_branch env b)
                align ((%"match" +. de +. %"with") :: bs)

        | Exp_let ((rec_, lb), body) ->
            let downct (x, _, e) =
                match x with
                | Inl x -> (x, e)
                | Inr _ -> unexpected ()
            let kw = if rec_ then "let rec" else "let"
            let lenv, ds = lb |> List.map downct |> Util.fold_map (doc_of_let rec_) env
            let doc = %kw +. (join "and" (ds |> List.map group)) +. %"in" +.
                      (doc_of_exp (min_op_prec, NonAssoc) lenv body)

            maybe_paren outer e_bin_prio_letin doc

        | Exp_primop (x, es) ->
            (* FIXME: prioritoy of operators *)
            let x = string_of_primop env x.idText
            if   List.isEmpty es
            then %x
            else %x +. (groups (es |> List.map (doc_of_exp outer env)))

        | Exp_ascribed (e, _) ->
            doc_of_exp outer env e

        | Exp_meta (Meta_info (e, _, _)) ->
            doc_of_exp outer env e

        | Exp_meta (Meta_desugared (e, Data_app)) ->
            let (c, args) =
                match Absyn.Util.destruct_app e with
                | Exp_fvar (c, true), args -> (c, args)
                | _, _ -> unexpected ()
            in
            
            let dargs = args |> List.map (fst >> doc_of_exp (min_op_prec, NonAssoc) env)

            doc_of_constr env c.v dargs
            
        | Exp_meta (Meta_desugared (e, Sequence)) ->
            match e with
            | Exp_let ((false, [Inl _, _, e1]), e2) ->
                let d1 = doc_of_exp (e_bin_prio_seq, Left ) env e1
                let d2 = doc_of_exp (e_bin_prio_seq, Right) env e2

                maybe_paren outer e_bin_prio_seq (d1 @. %";" +. d2)

            | _ -> unexpected ()

        | Exp_meta (Meta_datainst (e, _)) ->
            doc_of_exp outer env e

        | Exp_app  _ -> unexpected  ()
        | Exp_uvar _ -> unexpected  ()
        | Exp_tabs _ -> unsupported ()
        | Exp_tapp _ -> unsupported ()

(* -------------------------------------------------------------------- *)
and doc_of_constr (env : env) c args =
    let x = c.ident.idText
    match args with
    | [] -> %x
    | _  -> %x +. group (parens (join ", " args))

(* -------------------------------------------------------------------- *)
and doc_of_let (rec_ : bool) (env : env) (x, e) =
    let lenv = push env x.realname.idText x.ppname.idText
    let x    = resolve lenv x.realname.idText
    let d    = doc_of_exp (min_op_prec, NonAssoc) (if rec_ then lenv else env) e
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
    let d = doc_of_exp (min_op_prec, NonAssoc) benv e

    lenv, %x +. (group (joins args)) +. %"=" +. d

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
        (env, parens (join "|" ds))

    | Pat_wild ->
        (env, %"_")

    | Pat_withinfo (p, _) ->
        doc_of_pattern env p

    | Pat_tvar  _ -> unsupported ()
    | Pat_twild _ -> unsupported ()

(* -------------------------------------------------------------------- *)
and doc_of_branch (env : env) ((p, cl, body) : pat * exp option * exp) : doc =
    let env, pd = doc_of_pattern env p
    let dwhen = cl |> Option.map (doc_of_exp (min_op_prec, NonAssoc) env)
    let dbody = body |> doc_of_exp (min_op_prec, NonAssoc) env 

    match dwhen with
    | None -> pd +. %"->" +. dbody
    | Some dwhen -> pd +. %"when" +. (parens dwhen) +. %"->" +. dbody

(* -------------------------------------------------------------------- *)
let doc_of_modelt (env : env) (modx : sigelt) : env * doc option =
    match modx with
    | Sig_let ((rec_, lb), _) ->
        let downct (x, _, e) =
            match x with
            | Inr x -> (x.ident, e)
            | Inl _ -> unexpected ()
        let kw = if rec_ then "let rec" else "let"
        let env, ds = lb |> List.map downct |> Util.fold_map (doc_of_toplet rec_) env
        env, Some (%kw +. (join "and" (ds |> List.map group)))

    | Sig_main (e, _) ->
        env, Some (%"let" +. %"_" +. %"=" +. (doc_of_exp (min_op_prec, NonAssoc) env e))

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
        (parts |> List.map (FSharp.Format.pretty 80) |> String.concat "\n\n")
