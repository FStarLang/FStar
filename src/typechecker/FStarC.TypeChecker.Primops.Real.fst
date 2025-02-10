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
module Z = FStarC.BigInt
module U = FStarC.Syntax.Util

(* Range ops *)

type tf =
  | T
  | F

instance e_tf : Syntax.Embeddings.embedding tf =
  let ty = U.fvar_const PC.prop_lid in
  let emb_t_prop = ET_app(PC.prop_lid |> Ident.string_of_lid, []) in
  let em (p:tf) (rng:Range.range) _shadow _norm : term =
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

instance nbe_e_tf : TypeChecker.NBETerm.embedding tf =
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

let cmp (r1 r2 : Real.real) : option order =
  match r1._0, r2._0 with
  | "0.0", "0.0" -> Some Eq
  | "0.0", "0.5" -> Some Lt
  | "0.0", "1.0" -> Some Lt
  | "0.5", "0.0" -> Some Gt
  | "0.5", "0.5" -> Some Eq
  | "0.5", "1.0" -> Some Lt
  | "1.0", "0.0" -> Some Gt
  | "1.0", "0.5" -> Some Gt
  | "1.0", "1.0" -> Some Eq
  | _ -> None

let lt (r1 r2 : Real.real) : option tf =
  cmp r1 r2 |> Class.Monad.fmap (function Lt -> T | _ -> F)
let le (r1 r2 : Real.real) : option tf =
  cmp r1 r2 |> Class.Monad.fmap (function Lt | Eq -> T | _ -> F)
let gt (r1 r2 : Real.real) : option tf =
  cmp r1 r2 |> Class.Monad.fmap (function Gt -> T | _ -> F)
let ge (r1 r2 : Real.real) : option tf =
  cmp r1 r2 |> Class.Monad.fmap (function Gt | Eq -> T | _ -> F)

let of_int (i:Z.t) : Real.real =
  Real.Real (string_of_int (Z.to_int_fs i) ^ ".0")

let ops = [
  mk1 0 PC.real_of_int of_int;
]

let simplify_ops = [
  mk2' 0 PC.real_op_LT  lt lt;
  mk2' 0 PC.real_op_LTE le le;
  mk2' 0 PC.real_op_GT  gt gt;
  mk2' 0 PC.real_op_GTE ge ge;
]
