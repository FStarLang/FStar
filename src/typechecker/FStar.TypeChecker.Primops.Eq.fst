module FStar.TypeChecker.Primops.Eq

open FStar
open FStar.Compiler
open FStar.Compiler.Effect
open FStar.Compiler.List
open FStar.Syntax.Syntax
open FStar.TypeChecker
open FStar.Class.Monad
open FStar.Class.Show

module PC = FStar.Parser.Const
module S  = FStar.Syntax.Syntax
module U  = FStar.Syntax.Util
module EMB = FStar.Syntax.Embeddings
module NBE = FStar.TypeChecker.NBETerm

open FStar.TypeChecker.Primops.Base

let s_eq (_typ x y : EMB.abstract_term) : option bool =
  match U.eq_tm x.t y.t with
  | U.Equal -> Some true
  | U.NotEqual -> Some false
  | _ -> None

let nbe_eq (_typ x y : NBETerm.abstract_nbe_term) : option bool =
  match NBETerm.eq_t x.t y.t with
  | U.Equal -> Some true
  | U.NotEqual -> Some false
  | _ -> None

let push3 f g x y z = f (g x y z)
let negopt3 = push3 (fmap #option not)

let dec_eq_ops : list primitive_step = [
  mk3' 0 PC.op_Eq     s_eq           nbe_eq;
  mk3' 0 PC.op_notEq (negopt3 s_eq) (negopt3 nbe_eq);
]

(* Propositional equality follows. We use the abstract newtypes to
easily embed exactly the term we want. *)

let s_eq2 (_typ x y : EMB.abstract_term) : option EMB.abstract_term =
  match U.eq_tm x.t y.t with
  | U.Equal -> Some (EMB.Abstract U.t_true)
  | U.NotEqual -> Some (EMB.Abstract U.t_false)
  | _ -> None

let nbe_eq2 (_typ x y : NBE.abstract_nbe_term) : option NBE.abstract_nbe_term =
  let open FStar.TypeChecker.NBETerm in
  match NBETerm.eq_t x.t y.t with
  | U.Equal    -> Some (AbstractNBE (mkFV (S.lid_as_fv PC.true_lid None)  [] []))
  | U.NotEqual -> Some (AbstractNBE (mkFV (S.lid_as_fv PC.false_lid None) [] []))
  | U.Unknown  -> None

let s_eq3 (typ1 typ2 x y : EMB.abstract_term) : option EMB.abstract_term =
  match U.eq_tm typ1.t typ2.t, U.eq_tm x.t y.t with
  | U.Equal, U.Equal -> Some (EMB.Abstract U.t_true)
  | U.NotEqual, _
  | _, U.NotEqual ->
    Some (EMB.Abstract U.t_false)
  | _ -> None

let nbe_eq3 (typ1 typ2 x y : NBE.abstract_nbe_term) : option NBE.abstract_nbe_term =
  let open FStar.TypeChecker.NBETerm in
  match eq_t typ1.t typ2.t, eq_t x.t y.t with
  | U.Equal, U.Equal -> Some (AbstractNBE (mkFV (S.lid_as_fv PC.true_lid None)  [] []))
  | U.NotEqual, _
  | _, U.NotEqual ->
    Some (AbstractNBE (mkFV (S.lid_as_fv PC.false_lid None) [] []))
  | _ -> None

let prop_eq_ops : list primitive_step = [
  mk3' 1 PC.eq2_lid s_eq2 nbe_eq2;
  mk4' 2 PC.eq3_lid s_eq3 nbe_eq3;
]
