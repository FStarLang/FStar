(* -------------------------------------------------------------------- *)
#light "off"

module Microsoft.FStar.Backends.OCaml.CodeGen

open System
open System.Text

open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Range
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Absyn.Util

open Microsoft.FStar.Backends
open Microsoft.FStar.Backends.NameEnv
open Microsoft.FStar.Backends.OCaml.Syntax

open FSharp.Format

(* -------------------------------------------------------------------- *)
type mltyname = list<string> * string

type mlty =
    | Ty_var   of string
    | Ty_tuple of mlty list
    | Ty_fun   of string option * mlty * mlty
    | Ty_named of mltyname * mlty list

type mltycons =
    (string option * mlty) list * mlty

(* To be changed for polymorphic types *)
type mldtype = string * mlty list

type mlenv = {
    mle_types : Map<mltyname, mldtype>;
    mle_vals  : unit;
}

(* -------------------------------------------------------------------- *)
let unexpected rg =
    failwith ((string_of_range rg) ^ ": ocaml-backend-unexpected-construction")

(* -------------------------------------------------------------------- *)
let unsupported rg =
    failwith ((string_of_range rg) ^ ": ocaml-backend-unsupported-construction")

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
      let bytes = Array.map ocaml_u8_codepoint bytes in
      sprintf "\"%s\"" (String.concat "" bytes)

  | Const_string (bytes, _) ->
      let chars = (new UTF8Encoding (false, true)).GetString(bytes) in
      let chars = String.collect encode_char chars in
      sprintf "\"%s\"" chars

(* -------------------------------------------------------------------- *)
let is_prim_ns (ns : list<ident>) =
    match ns with
    | [{ idText = "Prims" }] -> true
    | _ -> false

(* -------------------------------------------------------------------- *)
let is_tuple_name (id : lident) =
    if is_prim_ns id.ns then
        match id.ident.idText with
        | "Tuple2" -> Some 2
        | "Tuple3" -> Some 3
        | "Tuple4" -> Some 4
        | "Tuple5" -> Some 5
        | "Tuple6" -> Some 6
        | _        -> None
    else
        None

(* -------------------------------------------------------------------- *)
let is_exn (id : lident) =
    is_prim_ns id.ns && id.ident.idText = "exn"

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
let infix_prim_ops = [
    ("op_Addition"       , e_bin_prio_op1   , "+" );
    ("op_Subtraction"    , e_bin_prio_op1   , "-" );
    ("op_Equality"       , e_bin_prio_eq    , "=" );
    ("op_AmpAmp"         , e_bin_prio_and   , "&&");
    ("op_BarBar"         , e_bin_prio_or    , "||");
    ("op_LessThanOrEqual", e_bin_prio_order , "<=");
]

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
let mltyname_of_lident (ns, x) =
    (List.map (fun x -> x.idText) ns, x.idText)

(* -------------------------------------------------------------------- *)
let rec mlty_of_ty (rg : range) (ty : typ) =
    let ty = Absyn.Util.compress_typ ty in
    let rg = ty.pos in
    match maybe_tuple rg ty with
    | None -> begin
        match maybe_mltynamed_of_ty rg [] ty with
        | None -> begin
            match ty.n with
            | Typ_btvar x ->
                Ty_var x.v.realname.idText

            | Typ_refine (x, _) ->
                mlty_of_ty rg x.sort

            | Typ_ascribed (ty, _) ->
                mlty_of_ty rg ty

            | Typ_fun(bs, c) -> 
               let t2 = comp_result c in 
               let mlt2 = mlty_of_ty rg t2 in
               List.fold_right (fun b out -> match fst b with 
                | Inl _ -> unsupported rg
                | Inr x -> 
                  let mlt1 = mlty_of_ty rg x.sort in
                  if is_null_binder b then Ty_fun(None, mlt1, out)  
                  else Ty_fun(Some x.v.ppname.idText, mlt1, out)) bs mlt2


            | Typ_const   _ -> unexpected  rg
            | Typ_app     _ -> unsupported rg
            | Typ_lam     _ -> unsupported rg
            | Typ_meta    _ -> unexpected  rg
            | Typ_uvar    _ -> unexpected  rg
            | Typ_unknown   -> unexpected  rg
            | Typ_delayed _ -> unexpected  rg
        end

        | Some (c, tys) -> Ty_named (c, tys)
    end

    | Some tys -> Ty_tuple tys

and maybe_mltynamed_of_ty (rg : range) acc ty =
    let rg = ty.pos in
    match (Absyn.Util.compress_typ ty).n with
    | Typ_const c ->
        Some (mltyname_of_lident (c.v.ns, c.v.ident), acc)

    | Typ_app(head, args) -> 
      let args = args |> List.map (function 
        | Inl t, _ -> mlty_of_ty rg t
        | _ -> unsupported rg) in
      maybe_mltynamed_of_ty rg (args @ acc) head
//
//    | Typ_app (t1, t2, _) ->
//        maybe_mltynamed_of_ty rg (mlty_of_ty rg t2 :: acc) t1

    | Typ_refine ({sort=ty}, _) ->
        maybe_mltynamed_of_ty rg acc ty

    | Typ_ascribed (ty, _) ->
        maybe_mltynamed_of_ty rg acc ty

    | Typ_btvar   _ -> None
    | Typ_fun     _ -> None
    | Typ_lam     _ -> unsupported rg
    | Typ_meta    _ -> unexpected  rg
    | Typ_uvar    _ -> unexpected  rg
    | Typ_unknown   -> unexpected  rg
    | Typ_delayed _ -> unexpected  rg

and maybe_tuple (rg : range) ty =
    let rec unfun n ty =
        if n > 0 then
            match (Absyn.Util.compress_typ ty).n with
            | Typ_lam (bs, ty)          -> unfun (n - List.length bs) ty
            | Typ_ascribed (ty, _)        -> unfun n ty
            | _ -> unsupported rg
        else
            ty
    in

    let rec aux acc ty =
        match (Absyn.Util.compress_typ ty).n with
        | Typ_const c -> begin
            match is_tuple_name c.v with
            | None -> None
            | Some n ->
                if List.length acc <> n then
                    unsupported rg;
                let acc = List.mapi unfun acc in
                Some (List.map (mlty_of_ty rg) acc)
        end

        | Typ_app (t, args) ->
            let targs = args |> List.map (function 
                | Inl t, _ -> t
                | _ -> unsupported rg) in 
            aux (targs @ acc) t

        | Typ_ascribed (ty, _) ->
            aux acc ty

        | _ -> None
    in

    aux [] ty

(* -------------------------------------------------------------------- *)
let mltycons_of_mlty (ty : mlty) =
    let rec aux acc ty =
        match ty with
        | Ty_fun (x, dom, codom) ->
            aux ((x, dom) :: acc) codom
        | _ ->
            (List.rev acc, ty)
    in aux [] ty

(* -------------------------------------------------------------------- *)
let rec doc_of_mltype_r tvmap outer mlty =
    match mlty with
    | Ty_var x -> begin
        match List.tryFind (fun (y, _) -> x = y) tvmap with
        | None -> text x
        | Some (_, x) -> text x
    end

    | Ty_tuple tys ->
        let docs = List.map (doc_of_mltype tvmap (min_op_prec, NonAssoc)) tys in
        reduce1 [text "("; parens (combine (text " * ") docs); text ")"]

    | Ty_named ((_, name), args) -> begin
        let doc =
            match args with
            | [] ->
                text name

            | [arg] ->
                reduce1 [doc_of_mltype tvmap (t_prio_name, Left) arg; text name]

            | _ ->
                let docs =
                    List.map (doc_of_mltype tvmap (min_op_prec, NonAssoc)) args
                in
                    reduce1 [parens (combine (text ",") docs); text name]

        in maybe_paren outer t_prio_name doc
    end

    | Ty_fun (_, t1, t2) ->
        let d1 = doc_of_mltype tvmap (t_prio_fun, Left ) t1 in
        let d2 = doc_of_mltype tvmap (t_prio_fun, Right) t2 in

        maybe_paren outer t_prio_fun (reduce1 [d1; text "->"; d2])

(* -------------------------------------------------------------------- *)
and doc_of_mltype tvmap outer ty =
    group (doc_of_mltype_r tvmap outer ty)

(* -------------------------------------------------------------------- *)
let doc_of_mltypes_bundle bundle =
    let for1 (name, _) = text name in
    let docs = List.map for1 bundle in
    reduce1 [text "type"; combine (text "and") docs]

(* -------------------------------------------------------------------- *)
let rec doc_of_exp (rg : range) outer (env : env) (e : exp) =
    let doc =
        match maybe_doc_of_primexp_r rg outer env e with
        | None   -> doc_of_exp_r rg outer env e
        | Some d -> d

    in group doc

(* -------------------------------------------------------------------- *)
and doc_of_exp_r (rg : range) outer (env : env) (e : exp) =
    let rg = e.pos in
    let e = Absyn.Util.compress_exp e in

     begin
        match e.n with
        | Exp_app(e, args) -> 
            let e    = doc_of_exp rg (e_app_prio, ILeft) env e in
            let args = List.collect (function
                | Inl _, _ -> []
                | Inr e, _ -> [doc_of_exp rg (e_app_prio, IRight) env e]) args in
            maybe_paren outer e_app_prio (cat1 e (reduce args))

        | Exp_bvar x ->
            text (resolve env x.v.realname.idText)

        | Exp_fvar (x, _) ->
            text x.v.ident.idText

        | Exp_constant c ->
            text (string_of_sconst c)

        | Exp_abs ([], body) ->
            doc_of_exp rg outer env body

        | Exp_abs ((Inl _, _)::bs, body) ->
            doc_of_exp rg outer env (mk_Exp_abs(bs, body) tun e.pos)

        | Exp_abs((Inr {v=x}, _)::bs, body) -> 
            let lenv = push env x.realname.idText x.ppname.idText in
            let x    = resolve lenv x.realname.idText in
            let d    = doc_of_exp rg (min_op_prec, NonAssoc) lenv (mk_Exp_abs(bs, body) tun e.pos) in
            maybe_paren outer e_bin_prio_lambda (reduce1 [text "fun"; text x; text "->"; d])

        | Exp_match ({n=(Exp_fvar _ | Exp_bvar _)}, [p, None, e]) when Absyn.Util.is_wild_pat p ->
            doc_of_exp rg outer env e

        | Exp_match (e, bs) -> begin
            match bs with
            | [({v=Pat_constant (Const_bool true )}, None, e1);
               ({v=Pat_constant (Const_bool false)}, None, e2)]

            | [({v=Pat_constant (Const_bool false)}, None, e1);
               ({v=Pat_constant (Const_bool true )}, None, e2)] ->

                let doc = reduce1 [
                    text "if"  ; doc_of_exp rg (e_bin_prio_if, Left)     env e ;
                    text "then"; doc_of_exp rg (e_bin_prio_if, NonAssoc) env e1;
                    text "else"; doc_of_exp rg (e_bin_prio_if, Right   ) env e2
                ] in

                maybe_paren outer e_bin_prio_if doc

            | _ ->
                let de = doc_of_exp rg (min_op_prec, NonAssoc) env e in
                let bs =
                    List.map
                        (fun b -> group (reduce1 [text " | "; doc_of_branch rg env b]))
                        bs
                in
                align ((group (reduce1 [text "match"; de; text "with"])) :: bs)
        end

        | Exp_let ((rec_, lb), body) ->
            let downct (x, _, e) =
                match x with
                | Inl x -> (x, e)
                | Inr _ -> unexpected rg in

            let kw = if rec_ then "let rec" else "let" in
            let lenv, ds = Util.fold_map (doc_of_let rg rec_) env (List.map downct lb) in
            let doc = reduce1 [
                text kw; combine (text "and") (List.map group ds); text "in";
                doc_of_exp rg (min_op_prec, NonAssoc) lenv body
            ]

            in maybe_paren outer e_bin_prio_letin doc

//NS: this case replaced by Exp_meta(Meta_desugared(e, Primop))
//        | Exp_primop (x, es) ->
//            let x = string_of_primop env x.idText in
//            if   List.isEmpty es
//            then text x
//            else cat1 (text x) (groups (List.map (doc_of_exp rg outer env) es))

        | Exp_ascribed (e, _) ->
            doc_of_exp rg outer env e

        | Exp_meta (Meta_desugared (e, Data_app)) ->
            let (c, args) =
                match Absyn.Util.head_and_args_e e with
                | {n=Exp_fvar (c, true)}, args -> (c, args)
                | _, _ -> unexpected rg
            in
            
            let dargs =
                List.collect
                    (function Inl _, _ -> [] | Inr e, _ -> [doc_of_exp rg (min_op_prec, NonAssoc) env e]) args
            in
            doc_of_constr rg env c.v dargs
            
        | Exp_meta (Meta_desugared (e, Sequence)) -> begin
            match e.n with
            | Exp_let ((false, [Inl _, _, e1]), e2) ->
                let d1 = doc_of_exp rg (e_bin_prio_seq, Left ) env e1 in
                let d2 = doc_of_exp rg (e_bin_prio_seq, Right) env e2 in

                maybe_paren outer e_bin_prio_seq (cat1 (cat d1 (text ";")) d2)

            | _ -> unexpected rg
        end

        | Exp_meta (Meta_desugared (e, Primop)) -> //NS: Fixme?
            doc_of_exp rg outer env e

        | Exp_meta (Meta_datainst (e, _)) ->
            doc_of_exp rg outer env e

//        | Exp_tapp (e, _) ->
//            (* FIXME: add a type annotation *)
//            doc_of_exp rg outer env e

//        | Exp_tabs (_, _, e) ->
//            doc_of_exp rg outer env e

//        | Exp_app  _ -> unexpected  rg
        | Exp_uvar _ -> unexpected  rg
        | Exp_delayed _ -> unexpected rg
    end

(* -------------------------------------------------------------------- *)
and maybe_doc_of_primexp_r (rg : range) outer (env : env) (e : exp) =
    let rec strip_tapp e =
        match (Absyn.Util.compress_exp e).n with
        | Exp_ascribed (e, _) -> strip_tapp e
        | Exp_app(head, args) -> mk_Exp_app(head, args |> List.filter (function Inl _, _ -> false | _ -> true)) e.tk e.pos 
        | _ -> e
    in

    let e = Absyn.Util.compress_exp e in
    let c = strip_tapp e in
    let (c, args) = Absyn.Util.head_and_args_e c in

    match (c.n, args) with
    | (Exp_fvar (x, _), [(Inr e1, _); (Inr e2, _)]) when is_prim_ns x.v.ns -> begin
        let test (y, _, _) = x.v.ident.idText = y in

        match List.tryFind test infix_prim_ops with
        | None -> None
        | Some (_, prio, txt) ->
            let d1 = doc_of_exp rg (prio, Left ) env e1 in
            let d2 = doc_of_exp rg (prio, Right) env e2 in
            Some (maybe_paren outer prio (reduce1 [d1; text txt; d2]))
    end

    | (Exp_fvar (x, _), [(Inr e, _)])
        when is_prim_ns x.v.ns && x.v.ident.idText = "op_Negation" -> begin

        let d = doc_of_exp rg (min_op_prec, NonAssoc) env e in
        Some (cat1 (text "not") (parens d)) (* FIXME *)
    end

    | _ -> None

(* -------------------------------------------------------------------- *)
and doc_of_constr (rg : range) (env : env) c args =
    let x = c.ident.idText in

    match args with
    | [] -> text x
    | _  -> reduce1 [text x; group (parens (combine (text ", ") args))]

(* -------------------------------------------------------------------- *)
and doc_of_let (rg : range) (rec_ : bool) (env : env) (x, e) =
    let lenv = push env x.realname.idText x.ppname.idText in
    let x    = resolve lenv x.realname.idText in
    let d    = doc_of_exp rg (min_op_prec, NonAssoc) (if rec_ then lenv else env) e in
    lenv, (reduce1 [text x; text "="; d])

(* -------------------------------------------------------------------- *)
and doc_of_toplet (rg : range) (rec_ : bool) (env : env) (x, e) =
    let lenv = push env x.idText x.idText in
    let x    = resolve lenv x.idText in

    let bds, e = match e.n with 
        | Exp_abs(bs, e) -> List.collect (function Inl _, _ -> [] | Inr x, _ -> [x]) bs, e 
        | _ -> [], e in
    let benv, args =
        Util.fold_map
            (fun lenv x ->
                let lenv = push lenv x.v.realname.idText x.v.ppname.idText in
                let x    = resolve lenv x.v.realname.idText in
                (lenv, text x))
            (if rec_ then lenv else env) bds in
    let d = doc_of_exp rg (min_op_prec, NonAssoc) benv e in

    lenv, cat1 (group (reduce1 [text x; group (reduce args); text "="])) d

(* -------------------------------------------------------------------- *)
and doc_of_pattern (rg : range) env p : env * doc =
    let env, d = doc_of_pattern_r rg env p in
    (env, group d)

(* -------------------------------------------------------------------- *)
and doc_of_pattern_r (rg : range) env (p : pat) : env * doc =
    match p.v with
    | Pat_cons (x, ps) ->
        let ps = ps |> List.filter (fun p -> match p.v with
            | Pat_dot_term _ 
            | Pat_dot_typ _ -> false
            | _ -> true) in
        let env, ds = Util.fold_map (doc_of_pattern rg) env ps in
        (env, doc_of_constr rg env x.v ds)

    | Pat_var x ->
        let env = push env x.v.realname.idText x.v.ppname.idText in
        (env, text (resolve env x.v.realname.idText))

    | Pat_constant c ->
        (env, text (string_of_sconst c))

    | Pat_disj ps ->
        let env, ds = Util.fold_map (doc_of_pattern rg) env ps in
        (env, parens (combine (text "|") ds))

    | Pat_wild _ ->
        (env, text "_")

    | Pat_dot_term _
    | Pat_dot_typ _
    | Pat_tvar  _ -> unsupported rg
    | Pat_twild _ -> unsupported rg

(* -------------------------------------------------------------------- *)
and doc_of_branch (rg : range) (env : env) ((p, cl, body) : pat * exp option * exp) : doc =
    let env, pd = doc_of_pattern rg env p in
    let dwhen = Option.map (doc_of_exp rg (min_op_prec, NonAssoc) env) cl in
    let dbody = doc_of_exp rg (min_op_prec, NonAssoc) env body in
    let doc =
        match dwhen with
        | None -> reduce1 [pd; text "->"; dbody]
        | Some dwhen -> reduce1 [pd; text "when"; (parens dwhen); text "->"; dbody] in

    group doc

(* -------------------------------------------------------------------- *)
let is_kind_for_mldtype rg (k : knd) =
    let rg = k.pos in
    let rec aux n (k : knd) =
        match k.n with
        | Kind_type     -> Some n
        | Kind_unknown  -> Some n

        | Kind_arrow([], k) -> aux n k

        | Kind_arrow((Inr _, _)::_, _) -> None

        | Kind_arrow((Inl {sort=k1}, _)::rest, k) when aux 0 k1 = Some 0 ->
          aux (n+1) (mk_Kind_arrow(rest, k) k.pos)

        | Kind_effect   -> None
        | Kind_abbrev _ -> unsupported rg
        | Kind_uvar _   -> unexpected rg
        | Kind_delayed _ -> unexpected rg
        | _ -> unexpected rg
    in
        aux 0 k

(* -------------------------------------------------------------------- *)
let mldtype_of_bundle (env : env) (indt : list<sigelt>) =
    let (ts, cs) =
        let fold1 sigelt (types, ctors) =
            match sigelt with
            | Sig_tycon (x, tps, k, ts, cs, _, rg) -> begin
                let tps = List.map (function
                    | Inl ({v=x; sort={n=Kind_type}}), _ -> x.realname.idText
                    | _ -> unsupported rg) tps
                in
                
                match is_kind_for_mldtype rg k with
                | Some n ->
                    ((x.ident.idText, tps, cs, n + List.length tps, rg) :: types, ctors)
                | _ ->
                    unsupported rg
            end

            | Sig_datacon (x, ty, pr, _, rg) ->
                (types, (x.ident.idText, (ty, pr)) :: ctors)

            | Sig_val_decl (_, _, _, rg)
            | Sig_typ_abbrev (_, _, _, _, _, rg)
            | Sig_assume (_, _, _, rg)
            | Sig_let (_, rg, _)
            | Sig_main (_, rg)
            | Sig_bundle (_, rg, _)
            | Sig_monads (_, _, rg, _) -> unexpected rg

        in

        let (ts, cs) = List.foldBack fold1 indt ([], []) in

        (ts, Map.ofList cs)
    in

    let fortype (x, tps, tcs, ar, rg) =
        let strip ar ty =
            let rec aux acc ar ty =
                if ar = 0 then (List.rev acc, ty) else
                    match (Absyn.Util.compress_typ ty).n with
                    | Typ_fun([], c) -> 
                      let ty = comp_result c in
                      aux acc ar ty
                    
                    | Typ_fun((Inl {v=x; sort={n=Kind_type}}, _)::rest, c) -> 
                        let ty = mk_Typ_fun(rest, c) ktype c.pos in
                        aux (x.realname.idText :: acc) (ar-1) ty
//                    
//                    | Typ_univ (x, {n=Kind_type}, c) -> 
//                        let ty = comp_result c in
//                        aux (x.realname.idText :: acc) (ar-1) ty
                    | _ ->
                        unexpected rg
                in
                    aux [] ar ty
        in

        let mldcons_of_cons cname =
            let (c, _) = Map.find cname.ident.idText cs in
            let ctynames, c = strip ar c in
            let (args, name) = mltycons_of_mlty (mlty_of_ty rg c) in

            match name with
            | Ty_named (name, tyargs) when name = (root env, x) ->
                let check x mty = match mty with | Ty_var mtyx -> x = mtyx | _ -> false in

                if List.length tyargs <> List.length ctynames then
                    unexpected rg;
                if not (List.forall2 check ctynames tyargs) then
                    unsupported rg;
                (cname.ident.idText, args, ctynames)
            | _ -> unexpected rg    

        in (x, ar, List.map mldcons_of_cons tcs)

    in List.map fortype ts

(* -------------------------------------------------------------------- *)
let vars = "abcdefghijklmnopqrstuvwxyz"

let tyvar_of_int n =
    let rec aux n =
        let s = sprintf "%c" vars.[n % 26] in
        if n >= String.length vars then (aux (n/26)) ^ s else s
    in
            "'" ^ (aux n)

let tvmap_of_tv tv =
    List.mapi (fun i x -> (x, tyvar_of_int i)) tv

let doc_of_indt (env : env) (indt : list<sigelt>) =

    try
        let mltypes = mldtype_of_bundle env indt in

        let for_mltype (name, ar, constrs) =
            let tyvars = List.init ar tyvar_of_int in

            let for_constr (name, tys, ctyvars) =
                let tvmap = List.zip ctyvars tyvars in

                let docs =
                    List.map
                        (fun (_, ty) -> doc_of_mltype tvmap (t_prio_tpl, NonAssoc) ty)
                        tys
                in
                group (reduce1 [text " |"; text name; text "of";
                                parens (combine (text "*") docs)])

            in
            
            let docargs =
                match tyvars with
                | []  -> empty
                | [x] -> text x
                | _   -> parens (combine (text ", ") (List.map text tyvars))
            in

            group (reduce1 [
                docargs; text name; text "="; 
                group (reduce (List.map for_constr constrs))
            ])
        in
        let types = List.map for_mltype mltypes in
        let doc = reduce1 [text "type"; combine (text "and") types] in
        (env, Some doc)

    with Failure _ -> (* FIXME *)
        (env, None)

(* -------------------------------------------------------------------- *)
let doc_of_modelt (env : env) (modx : sigelt) : env * doc option =
    match modx with
    | Sig_let ((rec_, lb), rg, _) ->
        let downct (x, _, e) =
            match x with
            | Inr x -> (x.ident, e)
            | Inl _ -> unexpected rg in

        let kw = if rec_ then "let rec" else "let" in
        let env, ds = Util.fold_map (doc_of_toplet rg rec_) env (List.map downct lb) in
        env, Some (reduce1 [text kw; combine (text "and") (List.map group ds)])

    | Sig_typ_abbrev (t, tps, _, ty, _, rg) ->
        let tps = List.map (function
            | Inl ({v=x; sort={n=Kind_type}}), _ -> x.realname.idText
            | _ -> unsupported rg) tps
        in

        let tvmap = tvmap_of_tv tps in
        let tps = List.map (fun x -> snd (List.find (fun (x', _) -> x = x') tvmap)) tps in
        let ty = mlty_of_ty rg ty in
        let dty = doc_of_mltype tvmap (min_op_prec, NonAssoc) ty in
        let docargs =
            match tps with
            | []  -> empty
            | [x] -> text x
            | _   -> parens (combine (text ", ") (List.map text tps))
        in

        env, Some (reduce1 [text "type"; docargs; text t.ident.idText; text "="; dty])

    | Sig_val_decl (x, ty, [], rg) ->        
        let rec strip ty =
            let ty = Absyn.Util.compress_typ ty in
            match ty.n with
            | Typ_fun(bs, c) -> 
               let ts, vs = List.partition (function (Inl _, _) -> false | _ -> true) bs in
               List.map (function (Inl x, _) -> x.v.ppname.idText | _ -> failwith "Impos") ts, mk_Typ_fun(vs, c) ktype ty.pos
            
            | _ ->
                ([], ty)
        in
        let tv, ty = strip ty in
        let ty = mlty_of_ty rg ty in
        let tvmap = tvmap_of_tv tv in
        let dty = doc_of_mltype tvmap (min_op_prec, NonAssoc) ty in
        env, Some (reduce1 [text "val"; text x.ident.idText; text " : "; dty])

    | Sig_main (e, rg) ->
        env, Some (reduce1 [
            text "let"; text "_"; text "=";
            doc_of_exp rg (min_op_prec, NonAssoc) env e
        ])

    | Sig_tycon (x, [], _, [], [], [], rg) ->
        env, Some (reduce1 [text "type"; text x.ident.idText])

    | Sig_tycon _ ->
        env, None

    | Sig_monads (_, _, rg, _) ->
        unsupported rg

    | Sig_bundle (indt, _, _) ->
        doc_of_indt env indt

    | Sig_assume         _ -> env, None
    | Sig_val_decl       _ -> env, None

    | Sig_datacon (x, ty, (n,_,_), _, rg) when is_exn n ->
        let rec aux ty =
            match (Absyn.Util.compress_typ ty).n with
            | Typ_fun(bs, c) -> 
               let tys = bs |> List.collect (function Inl _, _ -> [] | Inr x, _ -> [x.sort]) in
               tys

            | Typ_const x when is_exn x.v ->
                []

            | _ ->
                unexpected rg
        in

        let args = aux ty in
        let args = List.map (mlty_of_ty rg) args in

        begin match args with
        | [] -> env, Some (reduce1 [text "exception"; text x.ident.idText])
        | _  ->
            let args = List.map (doc_of_mltype [] (min_op_prec, NonAssoc)) args in
            let args = parens (combine (text " * ") args) in
            env, Some (reduce1 [text "exception"; text x.ident.idText; text "of"; group args])
        end
    | _ -> unexpected (Microsoft.FStar.Absyn.Util.range_of_sigelt modx)

(* -------------------------------------------------------------------- *)
let pp_module (mod_ : modul) =
    let env = NameEnv.create (path_of_lid mod_.name) in
    let env, parts = Util.choose_map doc_of_modelt env mod_.declarations in

    sprintf "module %s = struct\n%s\nend"
        mod_.name.ident.idText
        (String.concat "\n\n"
            (List.map (FSharp.Format.pretty 80) parts))
