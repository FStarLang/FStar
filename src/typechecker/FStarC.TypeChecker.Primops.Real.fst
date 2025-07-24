module FStarC.TypeChecker.Primops.Real

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Class.Monad
open FStarC.Order

open FStarC.TypeChecker.Primops.Base
open FStarC.Syntax.Syntax
open FStarC.Syntax.Embeddings

module PC = FStarC.Parser.Const
module U = FStarC.Syntax.Util
module NBETerm = FStarC.TypeChecker.NBETerm

(* Range ops *)

type tf =
  | T
  | F

instance e_tf : Syntax.Embeddings.embedding tf =
  let ty = U.fvar_const PC.prop_lid in
  let emb_t_prop = ET_app(PC.prop_lid |> Ident.string_of_lid, []) in
  let em (p:tf) (rng:Range.t) _shadow _norm : term =
    match p with
    | T -> U.t_true
    | F -> U.t_false
  in
  let un (t:term) _norm : option tf =
    match (unmeta_div_results t).n with
    | Tm_fvar fv when FStarC.Syntax.Syntax.fv_eq_lid fv PC.true_lid -> Some T
    | Tm_fvar fv when FStarC.Syntax.Syntax.fv_eq_lid fv PC.false_lid -> Some F
    | _ -> None
  in
  mk_emb_full
      em
      un
      (fun () -> ty)
      (function T -> "T" | F -> "F")
      (fun () -> emb_t_prop)

instance nbe_e_tf : NBETerm.embedding tf =
  let open FStarC.TypeChecker.NBETerm in
  let lid_as_typ l us args =
    mkFV (lid_as_fv l None) us args
  in
  let em _cb a =
    match a with
    | T -> lid_as_typ PC.true_lid [] []
    | F -> lid_as_typ PC.false_lid [] []
  in
  let un _cb t =
    match t.nbe_t with
    | FV (fv, [], []) when fv_eq_lid fv PC.true_lid -> Some T
    | FV (fv, [], []) when fv_eq_lid fv PC.false_lid -> Some F
    | _ -> None
  in
  mk_emb em un (fun () -> lid_as_typ PC.bool_lid [] []) (Syntax.Embeddings.emb_typ_of tf)

let lt (r1 r2 : Real.real) : option tf =
  Real.cmp r1 r2 |> Class.Monad.fmap (function Lt -> T | _ -> F)
let le (r1 r2 : Real.real) : option tf =
  Real.cmp r1 r2 |> Class.Monad.fmap (function Lt | Eq -> T | _ -> F)
let gt (r1 r2 : Real.real) : option tf =
  Real.cmp r1 r2 |> Class.Monad.fmap (function Gt -> T | _ -> F)
let ge (r1 r2 : Real.real) : option tf =
  Real.cmp r1 r2 |> Class.Monad.fmap (function Gt | Eq -> T | _ -> F)

let is_lit (s:string) (t:term)  : bool =
  match try_unembed_simple t with
  | Some r -> Real.cmp r (Real.Real s) = Some Eq
  | _ -> false

let bogus_cbs = {
    NBETerm.iapp = (fun h _args -> h);
    NBETerm.translate = (fun _ -> failwith "bogus_cbs translate");
}

let is_nbe_lit (s:string) (t:NBETerm.t)  : bool =
  match NBETerm.unembed NBETerm.e_real bogus_cbs t with
  | Some r -> Real.cmp r (Real.Real s) = Some Eq
  | _ -> false

let is_zero     = is_lit "0.0"
let is_one      = is_lit "1.0"
let is_nbe_zero = is_nbe_lit "0.0"
let is_nbe_one  = is_nbe_lit "1.0"

let add_op : psc -> FStarC.Syntax.Embeddings.norm_cb -> universes -> args -> option term
= fun psc _norm_cb _us args ->
  match args with
  | [(a1, None); (a2, None)] ->
    if is_zero a1 then Some a2
    else if is_zero a2 then Some a1
    else None
  | _ -> None

let mul_op : psc -> FStarC.Syntax.Embeddings.norm_cb -> universes -> args -> option term
= fun psc _norm_cb _us args ->
  match args with
  | [(a1, None); (a2, None)] ->
    if is_one a1 then Some a2
    else if is_one a2 then Some a1
    else None
  | _ -> None

let add_op_nbe =
  fun univs args ->
    match args with 
    | [(r, None); (l, None)] ->
      if is_nbe_zero l then Some r
      else if is_nbe_zero r then Some l
      else None
    | _ -> None

let mul_op_nbe =
  fun univs args ->
    match args with 
    | [(r, None); (l, None)] ->
      if is_nbe_one l then Some r
      else if is_nbe_one r then Some l
      else None
    | _ -> None

let of_int (i:int) : Real.real =
  Real.Real (string_of_int i ^ ".0")

let as_primitive_step is_strong (l, arity, u_arity, f, f_nbe) =
  as_primitive_step_nbecbs is_strong (l, arity, u_arity, f, (fun cb univs args -> f_nbe univs args))

let ops = [
  mk1 0 PC.real_of_int of_int;
] @ List.map (as_primitive_step true) [
  (PC.real_op_Addition, 2, 0, add_op, add_op_nbe);
  (PC.real_op_Multiply, 2, 0, mul_op, mul_op_nbe);
]

let simplify_ops = [
  mk2' 0 PC.real_op_LT  lt lt;
  mk2' 0 PC.real_op_LTE le le;
  mk2' 0 PC.real_op_GT  gt gt;
  mk2' 0 PC.real_op_GTE ge ge;
]
