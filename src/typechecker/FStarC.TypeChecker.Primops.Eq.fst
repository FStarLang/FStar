module FStarC.TypeChecker.Primops.Eq

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Syntax.Syntax
open FStarC.TypeChecker
open FStarC.Class.Monad
open FStarC.Class.Show

module PC = FStarC.Parser.Const
module S  = FStarC.Syntax.Syntax
module U  = FStarC.Syntax.Util
module EMB = FStarC.Syntax.Embeddings
module NBE = FStarC.TypeChecker.NBETerm
module TEQ = FStarC.TypeChecker.TermEqAndSimplify
module Env = FStarC.TypeChecker.Env

open FStarC.TypeChecker.Primops.Base

let s_eq (env:Env.env_t) (_typ x y : EMB.abstract_term) : option bool =
  match TEQ.eq_tm env x.t y.t with
  | TEQ.Equal -> Some true
  | TEQ.NotEqual -> Some false
  | _ -> None

let nbe_eq env (_typ x y : NBETerm.abstract_nbe_term) : option bool =
  match NBETerm.eq_t env x.t y.t with
  | TEQ.Equal -> Some true
  | TEQ.NotEqual -> Some false
  | _ -> None

let push3 f g x y z = f (g x y z)
let negopt3 = push3 (fmap #option not)

let dec_eq_ops env : list primitive_step = [
  mk3' 0 PC.op_Eq     (s_eq env)          (nbe_eq env);
  mk3' 0 PC.op_notEq (negopt3 (s_eq env)) (negopt3 (nbe_eq env));
]

(* Propositional equality follows. We use the abstract newtypes to
easily embed exactly the term we want. *)

let s_eq2 env (_typ x y : EMB.abstract_term) : option EMB.abstract_term =
  match TEQ.eq_tm env x.t y.t with
  | TEQ.Equal -> Some (EMB.Abstract U.t_true)
  | TEQ.NotEqual -> Some (EMB.Abstract U.t_false)
  | _ -> None

let nbe_eq2 env (_typ x y : NBE.abstract_nbe_term) : option NBE.abstract_nbe_term =
  let open FStarC.TypeChecker.NBETerm in
  match NBETerm.eq_t env x.t y.t with
  | TEQ.Equal    -> Some (AbstractNBE (mkFV (S.lid_as_fv PC.true_lid None)  [] []))
  | TEQ.NotEqual -> Some (AbstractNBE (mkFV (S.lid_as_fv PC.false_lid None) [] []))
  | TEQ.Unknown  -> None

let s_eq3 env (typ1 typ2 x y : EMB.abstract_term) : option EMB.abstract_term =
  match TEQ.eq_tm env typ1.t typ2.t, TEQ.eq_tm env x.t y.t with
  | TEQ.Equal, TEQ.Equal -> Some (EMB.Abstract U.t_true)
  | TEQ.NotEqual, _
  | _, TEQ.NotEqual ->
    Some (EMB.Abstract U.t_false)
  | _ -> None

let nbe_eq3 env (typ1 typ2 x y : NBE.abstract_nbe_term) : option NBE.abstract_nbe_term =
  let open FStarC.TypeChecker.NBETerm in
  match eq_t env typ1.t typ2.t, eq_t env x.t y.t with
  | TEQ.Equal, TEQ.Equal -> Some (AbstractNBE (mkFV (S.lid_as_fv PC.true_lid None)  [] []))
  | TEQ.NotEqual, _
  | _, TEQ.NotEqual ->
    Some (AbstractNBE (mkFV (S.lid_as_fv PC.false_lid None) [] []))
  | _ -> None

let prop_eq_ops env : list primitive_step = [
  mk3' 1 PC.eq2_lid (s_eq2 env) (nbe_eq2 env);
  mk4' 2 PC.eq3_lid (s_eq3 env) (nbe_eq3 env);
]
