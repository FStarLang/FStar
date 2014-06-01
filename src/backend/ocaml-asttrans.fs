(* -------------------------------------------------------------------- *)
#light "off"

module Microsoft.FStar.Backends.OCaml.ASTTrans

open System
open System.Text

open Microsoft.FStar
open Microsoft.FStar.Util
open Microsoft.FStar.Range
open Microsoft.FStar.Absyn.Syntax
open Microsoft.FStar.Absyn.Util
open Microsoft.FStar.Backends.OCaml.Syntax

(* -------------------------------------------------------------------- *)
type error =
| Unexpected      of string
| Unsupported     of string
| UnboundVar      of string
| UnboundTyVar    of string
| DuplicatedLocal of string * string

exception OCamlFailure of Range.range * error

let unexpected (rg : range) (what : string) =
    raise (OCamlFailure (rg, Unexpected what))

let unsupported (rg : range) (what : string) =
    raise (OCamlFailure (rg, Unsupported what))

let unbound_var (rg : range) (x : ident) =
    raise (OCamlFailure (rg, UnboundVar x.idText))

let unbound_ty_var (rg : range) (x : ident) =
    raise (OCamlFailure (rg, UnboundTyVar x.idText))

let duplicated_local (rg : range) (x : string * string) =
    raise (OCamlFailure (rg, DuplicatedLocal x))

(* -------------------------------------------------------------------- *)
let fresh = let c = ref 0 in fun x -> incr c; ((x, !c) : mlident)

(* -------------------------------------------------------------------- *)
type lenv = LEnv of Map<mlsymbol, mlident>

let lempty : lenv =
    LEnv Map.empty

let lpush (LEnv lenv : lenv) (real : ident) (pp : ident) =
    if Map.containsKey real.idText lenv then
        duplicated_local real.idRange (real.idText, pp.idText);
    let mlid = fresh pp.idText in
    (LEnv (Map.add real.idText mlid lenv), mlid)

let lresolve (LEnv lenv : lenv) (x : ident) =
    match Map.tryFind x.idText lenv with
    | None   -> unbound_var x.idRange x
    | Some x -> x

(* -------------------------------------------------------------------- *)
type tenv = TEnv of Map<string, mlident>

let tvar_of_btvar (TEnv tenv : tenv) (x : bvar<typ, knd>) =
    let name = x.v.realname.idText in

    match Map.tryFind name tenv with
    | None   -> unbound_ty_var x.p x.v.ppname
    | Some x -> x

(* -------------------------------------------------------------------- *)
type mlenv = unit

(* -------------------------------------------------------------------- *)
let is_prim_ns (ns : list<ident>) =
    match ns with
    | [{ idText = "Prims" }] -> true
    | _ -> false

(* -------------------------------------------------------------------- *)
type prims =
| Tuple of int

(* -------------------------------------------------------------------- *)
let as_prims (id : lident) : prims option =
    if is_prim_ns id.ns then
        match id.ident.idText with
        | "Tuple2" -> Some (Tuple 2)
        | "Tuple3" -> Some (Tuple 3)
        | "Tuple4" -> Some (Tuple 4)
        | "Tuple5" -> Some (Tuple 5)
        | "Tuple6" -> Some (Tuple 6)
        | _        -> None
    else
        None

(* -------------------------------------------------------------------- *)
let mlconst_of_const (rg : range) (sctt : sconst) =
  match sctt with
  | Const_unit         -> MLC_Unit
  | Const_char   c     -> MLC_Char  c
  | Const_uint8  c     -> MLC_Byte  c
  | Const_int32  i     -> MLC_Int   ((int64) i)
  | Const_int64  i     -> MLC_Int   i
  | Const_bool   b     -> MLC_Bool  b
  | Const_float  d     -> MLC_Float d

  | Const_bytearray (bytes, _) ->
      MLC_Bytes bytes

  | Const_string (bytes, _) ->
      MLC_String ((new UTF8Encoding (false, true)).GetString(bytes))

(* -------------------------------------------------------------------- *)
let mlkind_of_kind (k : knd) =
    let rec aux n (k : knd) =
        match Absyn.Util.compress_kind k with
        | Kind_type -> Some n

        | Kind_tcon (_, k1, k2, _) -> begin
            match aux 0 k1 with
            | Some 0 -> aux (n+1) k2
            | _      -> None
        end

        | _ -> None
    in
        aux 0 k

(* -------------------------------------------------------------------- *)
let rec mlty_of_ty_core (tenv : tenv) ((rg, ty) : range * typ) =
    let ty = Absyn.Util.compress_typ ty in

    match ty.t with
    | Typ_btvar x ->
        MLTY_Var (tvar_of_btvar tenv x)

    | Typ_refine (_, ty, _) ->
        mlty_of_ty tenv (rg, ty)

    | Typ_ascribed (ty, _) ->
        mlty_of_ty tenv (rg, ty)

    | Typ_meta (Meta_pos (ty, rg)) ->
        mlty_of_ty tenv (rg, ty)

    | Typ_fun (x, t1, (Pure t2 | Computation t2), _) ->
        let mlt1 = mlty_of_ty tenv (rg, t1) in
        let mlt2 = mlty_of_ty tenv (rg, t2) in
        MLTY_Fun (mlt1, mlt2)

    | Typ_const   _ -> unexpected  rg "type-constant"
    | Typ_app     _ -> unsupported rg "type-application"
    | Typ_dep     _ -> unsupported rg "type-expr-app"
    | Typ_lam     _ -> unsupported rg "type-fun"
    | Typ_tlam    _ -> unsupported rg "type-type-fun"
    | Typ_univ    _ -> unsupported rg "type-universe"
    | Typ_meta    _ -> unexpected  rg "type-meta"
    | Typ_uvar    _ -> unexpected  rg "type-uvar"
    | Typ_unknown   -> unexpected  rg "type-unknown"

(* -------------------------------------------------------------------- *)
and maybe_named (tenv : tenv) ((rg, ty) : range * typ) =
    let rec aux acc (rg, ty) =
        match (Absyn.Util.compress_typ ty).t with
        | Typ_const c ->
            Some (mlpath_of_lident c.v, acc)

        | Typ_app (t1, t2, _) ->
            aux (mlty_of_ty tenv (rg, t2) :: acc) (rg, t1)

        | Typ_refine (_, ty, _)        -> aux acc (rg, ty)
        | Typ_ascribed (ty, _)         -> aux acc (rg, ty)
        | Typ_meta (Meta_pos (ty, rg)) -> aux acc (rg, ty)

        | _ -> None

    in aux [] (rg, ty)

(* -------------------------------------------------------------------- *)
and maybe_tuple (tenv : tenv) ((rg, ty) : range * typ) =
    let rec unfun n ty =
        if n <= 0 then Some ty else
            match (Absyn.Util.compress_typ ty).t with
            | Typ_lam (_, _, ty)          -> unfun (n-1) ty
            | Typ_ascribed (ty, _)        -> unfun n ty
            | Typ_meta (Meta_pos (ty, _)) -> unfun n ty
            | _ -> None
    in

    let rec aux acc ty =
        match (Absyn.Util.compress_typ ty).t with
        | Typ_const c -> begin
            match as_prims c.v with
            | Some (Tuple n) ->
                let acc = List.choose id (List.mapi unfun acc) in
                if List.length acc <> n then None else
                Some (List.map (fun ty -> mlty_of_ty tenv (rg, ty)) acc)
            | _ -> None
        end

        | Typ_app (t1, t2, _)         -> aux (t2 :: acc) t1
        | Typ_ascribed (ty, _)        -> aux acc ty
        | Typ_meta (Meta_pos (ty, _)) -> aux acc ty

        | _ -> None
    in

    aux [] ty

(* -------------------------------------------------------------------- *)
and mlty_of_ty (tenv : tenv) (rgty : range * typ) : mlty =
    match maybe_tuple tenv rgty with
    | Some x -> MLTY_Tuple x
    | None   -> begin
        match maybe_named tenv rgty with
        | Some x -> MLTY_Named (snd x, fst x)
        | None   -> mlty_of_ty_core tenv rgty
    end

(* -------------------------------------------------------------------- *)
and mlpat_of_pat (rg : range) (lenv : lenv) (p : pat) : lenv * mlpattern =
    match p with
    | Pat_cons (x, ps) ->
        let lenv, ps = Util.fold_map (mlpat_of_pat rg) lenv ps in
        (lenv, MLP_CTor (mlpath_of_lident x, ps))

    | Pat_var x ->
        let lenv, mlid = lpush lenv x.realname x.ppname in
        (lenv, MLP_Var mlid)

    | Pat_constant c ->
        (lenv, MLP_Const (mlconst_of_const rg c))

    | Pat_disj ps ->
        let lenv, ps = Util.fold_map (mlpat_of_pat rg) lenv ps in
        (lenv, MLP_Branch ps)

    | Pat_wild ->
        lenv, MLP_Wild

    | Pat_withinfo (p, rg) ->
        mlpat_of_pat rg lenv p

    | Pat_tvar  _ -> unsupported rg "pattern-type-variable"
    | Pat_twild _ -> unsupported rg "pattern-type-wild"

(* -------------------------------------------------------------------- *)
let rec mlexpr_of_expr (rg : range) (lenv : lenv) (e : exp) =
    let e = Absyn.Util.compress_exp e in

    match Absyn.Util.destruct_app e with
    | (e, args) when not (List.isEmpty args) ->
        let e    = mlexpr_of_expr rg lenv e in
        let args = List.map (fun (e, _) -> mlexpr_of_expr rg lenv e) args in

        MLE_App (e, args)

    | _ -> begin
        match e with
        | Exp_bvar x ->
            MLE_Var (lresolve lenv x.v.realname)

        | Exp_fvar (x, _) ->
            MLE_Name (mlpath_of_lident x.v)

        | Exp_constant c ->
            MLE_Const (mlconst_of_const rg c)

        | Exp_abs (x, _, e) ->
            let lenv, mlid = lpush lenv x.realname x.ppname in
            let e = mlexpr_of_expr rg lenv e in
            mlfun mlid e

        | Exp_match ((Exp_fvar _ | Exp_bvar _), [p, None, e]) when Absyn.Util.is_wild_pat p ->
            mlexpr_of_expr rg lenv e

        | Exp_match (e, bs) -> begin
            match bs with
            | [(Pat_constant (Const_bool true ), None, e1);
               (Pat_constant (Const_bool false), None, e2)]

            | [(Pat_constant (Const_bool false), None, e1);
               (Pat_constant (Const_bool true ), None, e2)] ->

               let e  = mlexpr_of_expr rg lenv e  in
               let e1 = mlexpr_of_expr rg lenv e1 in
               let e2 = mlexpr_of_expr rg lenv e2 in

               mlif e (e1, e2)

            | _ ->
                let e  = mlexpr_of_expr rg lenv e in
                let bs = List.map (mlbranch_of_branch rg lenv) bs in

                MLE_Match (e, bs)
        end

        | Exp_let ((rec_, lb), body) ->
            let lenv, bindings = mllets_of_lets rg lenv (rec_, lb) in
            let body = mlexpr_of_expr rg lenv body in
            MLE_Let (rec_, bindings, body)

        | Exp_primop (x, args) ->
            let args = List.map (mlexpr_of_expr rg lenv) args in
            MLE_App (MLE_Var (lresolve lenv x), args)

        | Exp_meta (Meta_desugared (e, Data_app)) ->
            let (c, args) =
                match Absyn.Util.destruct_app e with
                | Exp_fvar (c, true), args -> (c, args)
                | _, _ -> unexpected rg "meta-data-app-without-fvar"
            in
            
            let args = List.map fst args in
            let args = List.map (mlexpr_of_expr rg lenv) args in

            MLE_CTor (mlpath_of_lident c.v, args)
            
        | Exp_meta (Meta_desugared (e, Sequence)) -> begin
            match e with
            | Exp_let ((false, [Inl _, _, e1]), e2) ->
                let d1 = mlexpr_of_expr rg lenv e1 in
                let d2 = mlexpr_of_expr rg lenv e2 in
                mlseq d1 d2

            | _ -> unexpected rg "expr-seq-mark-without-let"
        end

        | Exp_ascribed (e, _) ->
            mlexpr_of_expr rg lenv e

        | Exp_meta (Meta_info (e, _, rg)) ->
            mlexpr_of_expr rg lenv e

        | Exp_meta (Meta_datainst (e, _)) ->
            mlexpr_of_expr rg lenv e

        | Exp_tapp (e, _) ->
            (* FIXME: add a type annotation *)
            mlexpr_of_expr rg lenv e

        | Exp_tabs (_, _, e) ->
            (* FIXME: should only occur after a let-binding *)
            mlexpr_of_expr rg lenv e

        | Exp_app  _ -> unexpected  rg "expr-app"
        | Exp_uvar _ -> unexpected  rg "expr-uvar"
    end

(* -------------------------------------------------------------------- *)
and mllets_of_lets (rg : range) (lenv : lenv) (rec_, lbs) =    
    let downct (x, _, e) =
        match x with
        | Inl x -> (x, e)
        | Inr _ -> unexpected rg "expr-let-in-with-fvar" in


    let lbs = List.map downct lbs in

    let lenvb, mlids =
        Util.fold_map
            (fun lenv (x, _) -> lpush lenv x.realname x.ppname)
            lenv lbs in

    let es =
        let inlenv = if rec_ then lenvb else lenv in
        List.map (fun (x, e) ->
            let mlid = lresolve lenvb x.realname in
            (mlid, [], mlexpr_of_expr rg inlenv e)) lbs
    in

    (lenvb, es)

(* -------------------------------------------------------------------- *)
and mlbranch_of_branch (rg : range) (lenv : lenv) (pat, when_, body) =
    let lenv, pat = mlpat_of_pat rg lenv pat in
    let when_ = Option.map (mlexpr_of_expr rg lenv) when_ in
    let body  = mlexpr_of_expr rg lenv body in
    (pat, when_, body)
