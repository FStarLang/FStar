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
module U  = FStar.Syntax.Util
module EMB = FStar.Syntax.Embeddings
module NBE = FStar.TypeChecker.NBETerm

open FStar.TypeChecker.Primops.Base

type abstract_term = | Abstract : t:term -> abstract_term
instance _ : EMB.embedding abstract_term =
  EMB.embed_as EMB.e_any (fun x -> Abstract x) (fun x -> match x with Abstract x -> x) None

type abstract_nbe_term = | AbstractNBE : t:NBETerm.t -> abstract_nbe_term

instance _ : NBE.embedding abstract_nbe_term =
  NBE.embed_as NBE.e_any (fun x -> AbstractNBE x) (fun x -> match x with AbstractNBE x -> x) None

let s_eq (_typ x y : abstract_term) : option bool =
  match U.eq_tm x.t y.t with
  | U.Equal -> Some true
  | U.NotEqual -> Some false
  | _ -> None

let nbe_eq (_typ x y : abstract_nbe_term) : option bool =
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
