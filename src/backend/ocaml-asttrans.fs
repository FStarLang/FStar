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
    LEnv (Map.add real.idText (fresh pp.idText) lenv)

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
        let lenv = lpush lenv x.realname x.ppname in
        (lenv, MLP_Var (lresolve lenv x.realname))

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
