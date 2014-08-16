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
open FSharp.Format

(* -------------------------------------------------------------------- *)
type error =
| Unexpected      of string
| Unsupported     of string
| UnboundVar      of string
| UnboundTyVar    of string
| DuplicatedLocal of string * string

exception OCamlFailure of Range.range * error

let string_of_error (error : error) =
    sprintf "%A" error

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
let tyvar_of_int =
    let tyvars = "abcdefghijklmnopqrstuvwxyz" in
    let rec aux n =
        let s = sprintf "%c" tyvars.[n % 26] in (* FIXME *)
        if n >= String.length tyvars then (aux (n/26)) ^ s else s
    in fun n -> "'" ^ (aux n)

(* -------------------------------------------------------------------- *)
type mlenv = MLEnv of unit

(* -------------------------------------------------------------------- *)
type lenv = LEnv of Map<mlsymbol, mlident>

(* -------------------------------------------------------------------- *)
let lempty : lenv =
    LEnv Map.empty

(* -------------------------------------------------------------------- *)
let lenv_of_mlenv (_ : mlenv) : lenv =
    lempty

(* -------------------------------------------------------------------- *)
let lpush (LEnv lenv : lenv) (real : ident) (pp : ident) =
(* FIXME
    if Map.containsKey real.idText lenv then
        duplicated_local real.idRange (real.idText, pp.idText);
*)
    let mlid = fresh pp.idText in
    (LEnv (Map.add real.idText mlid lenv), mlid)

(* -------------------------------------------------------------------- *)
let lresolve (LEnv lenv : lenv) (x : ident) =
    match Map.tryFind x.idText lenv with
    | None   -> unbound_var x.idRange x
    | Some x -> x

(* -------------------------------------------------------------------- *)
type tenv = TEnv of Map<string, mlident>

(* -------------------------------------------------------------------- *)
let tempty : tenv =
    TEnv Map.empty

(* -------------------------------------------------------------------- *)
let tenv_of_tvmap (tvs : list<option<ident * ident>>) =
    let rec fresh_tyvar used i =
        let pp = tyvar_of_int 0 in

        if Set.contains pp used then
            fresh_tyvar used (i+1)
        else
            (Set.add pp used, pp) in

    let freshen used pp =
        match pp with
        | Some pp when not (Set.contains pp.idText used) ->
            (Set.add pp.idText used, pp.idText)
        | _ ->
            fresh_tyvar used 0 in

    let _, tvs =
        let for1 used tv =
            match tv with
            | Some (real, pp) ->
                let (used, pp) = freshen used (Some pp) in 
                (used, (fresh pp, Some real.idText))
            | None ->
                let (used, pp) = freshen used None in
                (used, (fresh pp, None)) in

        Util.fold_map for1 Set.empty tvs
    in
    
    let tparams = List.map (fun (x, _) -> x) tvs in
    let tvs = List.choose (fun (x, y) ->
        match y with None -> None | Some y -> Some (y, x))
        tvs
    in

    (TEnv (Map.ofList tvs), tparams)

(* -------------------------------------------------------------------- *)
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
type tprims =
| Tuple of int
| Exn

(* -------------------------------------------------------------------- *)
let as_tprims (id : lident) : option<tprims> =
    if is_prim_ns id.ns then
        match id.ident.idText with
        | "Tuple2" -> Some (Tuple 2)
        | "Tuple3" -> Some (Tuple 3)
        | "Tuple4" -> Some (Tuple 4)
        | "Tuple5" -> Some (Tuple 5)
        | "Tuple6" -> Some (Tuple 6)
        | "Exn"    -> Some Exn
        | _        -> None
    else
        None

(* -------------------------------------------------------------------- *)
let is_xtuple (x : lident) =
    if is_prim_ns x.ns then
        match x.ident.idText with
        | "MkTuple2" -> Some 2
        | "MkTuple3" -> Some 3
        | "MkTuple4" -> Some 4
        | "MkTuple5" -> Some 5
        | "MkTuple6" -> Some 6
        | _          -> None
    else
        None

(* -------------------------------------------------------------------- *)
let is_etuple (e : exp) =
    let rec aux n e =
        match (Absyn.Util.compress_exp e).n with
        | Exp_tapp (e, _) -> aux (n+1) e
        | Exp_fvar (x, _) -> begin
            match is_xtuple x.v with
            | Some k when k = n -> Some k
            | _ -> None
        end
        | _ -> None
    in aux 0 e

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
let mlkind_of_kind (tps : list<tparam>) (k : knd) =
    let mltparam_of_tparam = function
        | Tparam_typ (x, {n=Kind_type}) -> Some (x.realname, x.ppname)
        | _ -> None
    in

    let rec aux acc (k : knd) =
        match (Absyn.Util.compress_kind k).n with
        | Kind_type    -> Some (List.rev acc)
        | Kind_unknown -> Some (List.rev acc) (* FIXME *)

        | Kind_tcon (x, k1, k2, _) -> begin
            match aux [] k1 with
            | Some [] ->
                let x = Option.map (fun x -> (x.realname, x.ppname)) x in
                aux (x :: acc) k2
            | _ -> None
        end

        | _ -> None in

    let aout = List.choose mltparam_of_tparam tps in

    if List.length aout <> List.length tps then
        None
    else
        aux (List.rev (List.map Some aout)) k

(* -------------------------------------------------------------------- *)
let rec mlty_of_ty_core (tenv : tenv) ((rg, ty) : range * typ) =
    let rg = ty.pos in
    let ty = Absyn.Util.compress_typ ty in
    match ty.n with
    | Typ_btvar x ->
        MLTY_Var (tvar_of_btvar tenv x)

    | Typ_refine (_, ty, _) ->
        mlty_of_ty tenv (rg, ty)

    | Typ_ascribed (ty, _) ->
        mlty_of_ty tenv (rg, ty)

    | Typ_fun (x, t1, c, _) -> 
        let t2 = comp_result c in
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
    | Typ_delayed _ -> unexpected  rg "type-delayed"

(* -------------------------------------------------------------------- *)
and maybe_named (tenv : tenv) ((rg, ty) : range * typ) =
    let rg = ty.pos in
    let rec aux acc (rg, ty) =
        match (Absyn.Util.compress_typ ty).n with
        | Typ_const c ->
            Some (mlpath_of_lident c.v, acc)

        | Typ_app (t1, t2, _) ->
            aux (mlty_of_ty tenv (rg, t2) :: acc) (rg, t1)

        | Typ_refine (_, ty, _)        -> aux acc (rg, ty)
        | Typ_ascribed (ty, _)         -> aux acc (rg, ty)
      
        | _ -> None

    in aux [] (rg, ty)

(* -------------------------------------------------------------------- *)
and maybe_tuple (tenv : tenv) ((rg, ty) : range * typ) =
    let rg = ty.pos in
    let rec unfun n ty =
        if n <= 0 then Some ty else
            match (Absyn.Util.compress_typ ty).n with
            | Typ_lam (_, _, ty)          -> unfun (n-1) ty
            | Typ_ascribed (ty, _)        -> unfun n ty
            | _ -> None
    in

    let rec aux acc ty =
        match (Absyn.Util.compress_typ ty).n with
        | Typ_const c -> begin
            match as_tprims c.v with
            | Some (Tuple n) ->
                let acc = List.choose id (List.mapi unfun acc) in
                if List.length acc <> n then None else
                Some (List.map (fun ty -> mlty_of_ty tenv (rg, ty)) acc)
            | _ -> None
        end

        | Typ_app (t1, t2, _)         -> aux (t2 :: acc) t1
        | Typ_ascribed (ty, _)        -> aux acc ty

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
let mltycons_of_mlty (ty : mlty) =
    let rec aux acc ty =
        match ty with
        | MLTY_Fun (dom, codom) ->
            aux (dom :: acc) codom
        | _ ->
            (List.rev acc, ty)
    in aux [] ty

(* -------------------------------------------------------------------- *)
let rec strip_polymorphism acc rg ty =
    let rg = ty.pos in
    match (Absyn.Util.compress_typ ty).n with
    | Typ_univ (x, {n=Kind_type}, c) -> 
        let ty = comp_result c in 
        strip_polymorphism ((x.realname, x.ppname) :: acc) rg ty
    | _ ->
        (List.rev acc, rg, ty)

(* -------------------------------------------------------------------- *)
let mlscheme_of_ty (rg : range) (ty : typ) : mltyscheme =
    let tparams, rg, ty = strip_polymorphism [] rg ty in
    let tenv, tparams   = tenv_of_tvmap (List.map Some tparams) in

    (tparams, mlty_of_ty tenv (rg, ty))

(* -------------------------------------------------------------------- *)
let rec mlpat_of_pat (rg : range) (lenv : lenv) (p : pat) : lenv * mlpattern =
    match p with
    | Pat_cons (x, ps) when is_xtuple x = Some (List.length ps) ->
        let lenv, ps = Util.fold_map (mlpat_of_pat rg) lenv ps in
        (lenv, MLP_Tuple ps)

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
    let rg = e.pos in
    let e = Absyn.Util.compress_exp e in

    match Absyn.Util.destruct_app e with
    | (e, args) when is_etuple e = Some (List.length args) ->
        let args = List.map (fun (e, _) -> mlexpr_of_expr rg lenv e) args in
        MLE_Tuple args

    | (e, args) when not (List.isEmpty args) ->
        let e    = mlexpr_of_expr rg lenv e in
        let args = List.map (fun (e, _) -> mlexpr_of_expr rg lenv e) args in

        MLE_App (e, args)

    | _ -> begin
        match e.n with
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

        | Exp_match ({n=(Exp_fvar _ | Exp_bvar _)}, [p, None, e]) when Absyn.Util.is_wild_pat p ->
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

//NS: This case replaced by Exp_meta(Meta_desugared(e, Primop)) ... see below
//        | Exp_primop (x, args) ->
//            let args = List.map (mlexpr_of_expr rg lenv) args in
//            MLE_App (MLE_Var (lresolve lenv x), args)

        | Exp_meta (Meta_desugared (e, Data_app)) ->
            let (c, args) =
                match Absyn.Util.destruct_app e with
                | {n=Exp_fvar (c, true)}, args -> (c, args)
                | _, _ -> unexpected rg "meta-data-app-without-fvar"
            in
            
            let args = List.map fst args in
            let args = List.map (mlexpr_of_expr rg lenv) args in

            MLE_CTor (mlpath_of_lident c.v, args)
            
        | Exp_meta (Meta_desugared (e, Sequence)) -> begin
            match e.n with
            | Exp_let ((false, [Inl _, _, e1]), e2) ->
                let d1 = mlexpr_of_expr rg lenv e1 in
                let d2 = mlexpr_of_expr rg lenv e2 in
                mlseq d1 d2

            | _ -> unexpected rg "expr-seq-mark-without-let"
        end

        | Exp_meta (Meta_desugared (e, Primop)) -> //NS: Fixme?
             mlexpr_of_expr rg lenv e
      
        | Exp_ascribed (e, _) ->
            mlexpr_of_expr rg lenv e

        
        | Exp_meta (Meta_datainst (e, _)) ->
            mlexpr_of_expr rg lenv e

        | Exp_tapp (e, _) ->
            (* FIXME: add a type annotation *)
            mlexpr_of_expr rg lenv e

        | Exp_tabs (_, _, e) ->
            (* FIXME: should only occur after a let-binding *)
            mlexpr_of_expr rg lenv e

        | Exp_app     _ -> unexpected rg "expr-app"
        | Exp_uvar    _ -> unexpected rg "expr-uvar"
        | Exp_delayed _ -> unexpected rg "expr-delayed"
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

(* -------------------------------------------------------------------- *)
type mode    = Sig | Struct
type mlitem1 = either<mlsig1, mlmodule1>

let mlitem1_ty mode args =
    match mode with
    | Sig    -> Inl (MLS_Ty args)
    | Struct -> Inr (MLM_Ty args)

let mlitem1_exn mode args =
    match mode with
    | Sig    -> Inl (MLS_Exn args)
    | Struct -> Inr (MLM_Exn args)

(* -------------------------------------------------------------------- *)
type mldtype = mlsymbol * mlidents * mltybody

let mldtype_of_indt (mlenv : mlenv) (indt : list<sigelt>) : list<mldtype> =
    let (ts, cs) =
        let fold1 sigelt (types, ctors) =
            match sigelt with
            | Sig_tycon (x, tps, k, ts, cs, _, rg) -> begin
                let ar =
                    match mlkind_of_kind tps k with
                    | None    -> unsupported rg "not-an-ML-kind"
                    | Some ar -> ar in
                ((x.ident.idText, cs, snd (tenv_of_tvmap ar), rg) :: types, ctors)
            end

            | Sig_datacon (x, ty, pr, _, rg) ->
                (types, (x.ident.idText, (ty, pr)) :: ctors)

            | _ ->
                unexpected
                    (Absyn.Util.range_of_sigelt sigelt)
                    "no-dtype-in-bundle"
        in

        let (ts, cs) = List.foldBack fold1 indt ([], []) in

        (ts, Map.ofList cs)
    in

    let fortype (x, tcs, tparams, rg) =
        let mldcons_of_cons cname =
            let (c, _) = Map.find cname.ident.idText cs in
            let cparams, rgty, c = strip_polymorphism [] rg c in

            if List.length cparams <> List.length tparams then
                unexpected rg "invalid-number-of-ctor-params";

            let cparams = List.map (fun (x, _) -> x.idText) cparams in

            let tenv = List.zip cparams tparams in
            let tenv = TEnv (Map.ofList tenv) in

            let c = mlty_of_ty tenv (rgty, c) in
            let (args, name) = mltycons_of_mlty c in

            match name with
            | MLTY_Named (tyargs, name) when snd name = x ->
                let check x mty = match mty with | MLTY_Var mtyx -> x = mtyx | _ -> false in

                if List.length tyargs <> List.length cparams then
                    unexpected rg "dtype-invalid-ctor-result";
                if not (List.forall2 check tparams tyargs) then
                    unsupported rg "dtype-invalid-ctor-result";
                (cname.ident.idText, args)

            | _ -> unexpected rg "dtype-invalid-ctor-result"   

        in (x, tparams, MLTD_DType (List.map mldcons_of_cons tcs))

    in List.map fortype ts

(* -------------------------------------------------------------------- *)
let mlmod1_of_mod1 mode (mlenv : mlenv) (modx : sigelt) : option<mlitem1> =
    match modx with
    | Sig_val_decl (x, ty, _, rg) when mode = Sig ->
        let tparams, ty = mlscheme_of_ty rg ty in
        Some (Inl (MLS_Val (x.ident.idText, (tparams, ty))))

    | Sig_let ((rec_, lbs), rg) when mode = Struct ->
        let downct (x, _, e) =
            match x with
            | Inr x -> (x, e)
            | Inl _ -> unexpected rg "expr-top-let-with-bvar" in

        let lbs = List.map downct lbs in
        let lbs = List.map (fun (x, e) ->
            (x.ident.idText, [], mlexpr_of_expr rg (lenv_of_mlenv mlenv) e))
            lbs
        in

        Some (Inr (MLM_Let (rec_, lbs)))

    | Sig_main (e, rg) when mode = Struct ->
        let lenv = lenv_of_mlenv mlenv in
        Some (Inr (MLM_Top (mlexpr_of_expr rg lenv e)))

    | Sig_typ_abbrev (t, tps, k, ty, _, rg) -> begin
        let ar =
            match mlkind_of_kind tps k with
            | None    -> unsupported rg "not-an-ML-kind"
            | Some ar -> ar in

        let tenv, tparams = tenv_of_tvmap ar in
        let ty = mlty_of_ty tenv (rg, ty) in
        let ty = MLTD_Abbrev ty in

        Some (mlitem1_ty mode [t.ident.idText, tparams, Some ty])
    end

    | Sig_tycon (t, tps, k, [], [], [], rg) ->
        let ar =
            match mlkind_of_kind tps k with
            | None    -> unsupported rg "not-an-ML-kind"
            | Some ar -> ar
        in

        let _tenv, tparams = tenv_of_tvmap ar in

        Some (mlitem1_ty mode [t.ident.idText, tparams, None])

    | Sig_monads (_, _, rg) ->
        unsupported rg "mod1-monad"

    | Sig_bundle (indt, _) -> begin
        let aout = mldtype_of_indt mlenv indt in
        let aout = List.map (fun (x, y, z) -> (x, y, Some z)) aout in

        match mode with
        | Sig    -> Some (Inl (MLS_Ty aout))
        | Struct -> Some (Inr (MLM_Ty aout))
    end

    | Sig_datacon (x, ty, tx, _, rg) when as_tprims tx = Some Exn -> begin
        let rec aux acc ty =
            match (Absyn.Util.compress_typ ty).n with
            | Typ_fun (_, ty1, c, _) ->
                let ty2 = comp_result c in 
                aux (ty1 :: acc) ty2
            | Typ_const x when as_tprims x.v = Some Exn->
                List.rev acc
            | _ ->
                unexpected rg "invalid-exn-type"
        in

        let args = aux [] ty in
        let tenv = fst (tenv_of_tvmap []) in
        let args = List.map (fun ty -> mlty_of_ty tenv (rg, ty)) args in

        Some (mlitem1_exn mode (x.ident.idText, args))
    end

    | Sig_assume         _ -> None
    | Sig_val_decl       _ -> None
    | Sig_tycon          _ -> None
    | Sig_datacon        _ -> None
    | Sig_let            _ -> None
    | Sig_main           _ -> None

(* -------------------------------------------------------------------- *)
let mlmod_of_mod (mlenv : mlenv) (modx : list<sigelt>) : mlmodule =
    let asright = function Inr x -> x | Inl _ -> failwith "asright" in
    List.choose (fun x -> Option.map asright (mlmod1_of_mod1 Struct mlenv x)) modx

(* -------------------------------------------------------------------- *)
let mlsig_of_sig (mlenv : mlenv) (modx : list<sigelt>) : mlsig =
    let asleft = function Inl x -> x | Inr _ -> failwith "asleft" in
    List.choose (fun x -> Option.map asleft (mlmod1_of_mod1 Sig mlenv x)) modx

(* -------------------------------------------------------------------- *)
let mlmod_of_fstar (fmod_ : modul) =
    let mod_ = mlmod_of_mod (MLEnv ()) fmod_.declarations in
    let sig_ = mlsig_of_sig (MLEnv ()) fmod_.declarations in
    (mlpath_of_lident fmod_.name, sig_, mod_)

(* -------------------------------------------------------------------- *)
let mllib_empty : mllib =
    MLLib []

(* -------------------------------------------------------------------- *)
let rec mllib_add (MLLib mllib : mllib) ((path : mlpath), sig_, mod_) =
    match fst path with
    | [] ->
        let rec aux = function
        | [] ->
            [snd path, Some (sig_, mod_), mllib_empty]
        | ((name, sigmod, sublibs) as the) :: tl ->
            if name = snd path then begin
                if Option.isSome sigmod then
                    failwith "duplicated-module";
                (name, Some (sig_, mod_), sublibs) :: tl
            end else
                the :: (aux tl)

        in MLLib (aux mllib)

    | x :: subns ->
        let subpath = (subns, snd path) in

        let rec aux = function
        | [] ->
            let sub = mllib_add mllib_empty (subpath, sig_, mod_) in
            [snd path, Some (sig_, mod_), sub]
        | ((name, sigmod, sublibs) as the) :: tl ->
            if name = snd path then
                (name, sigmod, mllib_add sublibs (subpath, sig_, mod_)) :: tl
            else
                the :: (aux tl)
                
        in MLLib (aux mllib)

(* -------------------------------------------------------------------- *)
let mlmod_of_fstars (fmods : list<modul>) =
    let fmods = List.map mlmod_of_fstar fmods in
    List.fold mllib_add mllib_empty fmods
    
