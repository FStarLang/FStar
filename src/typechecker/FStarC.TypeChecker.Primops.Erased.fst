module FStarC.TypeChecker.Primops.Erased

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

open FStarC.TypeChecker.Primops.Base

(* This type is kind of a pun *)
type emb_erased (tm_t : Type) (a:Type) =
  | Hide   : ty:tm_t -> x:a -> emb_erased tm_t a
  | Reveal : ty:tm_t -> x:a -> emb_erased tm_t a

instance e_erased (a:Type) (d : EMB.embedding a) : Tot (EMB.embedding (emb_erased term a)) =
  let em (x:emb_erased term a) rng shadow cbs =
    match x with
    | Hide _ty x ->
      let h = S.fvar PC.hide None in
      let ty = EMB.type_of d in
      U.mk_app h [S.iarg ty; S.as_arg (EMB.embed x rng shadow cbs)]
    | Reveal _ty x ->
      let r = S.fvar PC.reveal None in
      let ty = EMB.type_of d in
      U.mk_app r [S.iarg ty; S.as_arg (EMB.embed x rng shadow cbs)]
  in
  let un (t:term) cbs : option (emb_erased term a) =
    let head, args = U.head_and_args t in
    match (U.un_uinst head).n, args with
    | Tm_fvar fv, [(ty, Some _); (a, None)] when fv_eq_lid fv PC.hide ->
      let! v = EMB.unembed a cbs in
      return (Hide ty v)
    | Tm_fvar fv, [(ty, Some _); (a, None)] when fv_eq_lid fv PC.reveal ->
      let! v = EMB.unembed a cbs in
      return (Reveal ty v)
    | _ ->
      None
  in
  EMB.mk_emb_full em un
    (fun () -> S.t_erased_of (EMB.type_of d))
    (function
     | Hide   _ty x -> "Hide "   ^ EMB.printer_of d x
     | Reveal _ty x -> "Reveal " ^ EMB.printer_of d x)
    (fun () -> ET_abstract)

instance nbe_e_erased (a:Type) (d : NBE.embedding a) : Tot (NBE.embedding (emb_erased NBETerm.t a)) =
  let em cbs (x:emb_erased NBETerm.t a) =
    match x with
    | Hide _ty x ->
      let fv = S.lid_as_fv PC.hide None in
      NBE.mkFV fv [] [NBE.as_arg (NBE.embed d cbs x); NBE.as_iarg (NBE.type_of d)]
    | Reveal _ty x ->
      let fv = S.lid_as_fv PC.reveal None in
      NBE.mkFV fv [] [NBE.as_arg (NBE.embed d cbs x); NBE.as_iarg (NBE.type_of d)]
  in
  let un cbs (t:NBETerm.t) : option (emb_erased NBETerm.t a) =
    match NBETerm.nbe_t_of_t t with
    | NBETerm.FV (fv, _, [(body, _); (ty, _)]) // NB: Argument order in NBE terms is reversed; so the body is first, the type is second
      when fv_eq_lid fv PC.hide ->
      let! v = NBE.unembed d cbs body in
      return (Hide ty v)
    | NBETerm.FV (fv, _, [(body, _); (ty, _)]) when fv_eq_lid fv PC.reveal ->
      let! v = NBE.unembed d cbs body in
      return (Reveal ty v)
    | _ ->
      None
  in
  NBETerm.mk_emb em un
    (fun () -> magic()) //NBET.t_erased_of (NBE.type_of d))
    (fun () -> ET_abstract)

let s_reveal (a:EMB.abstract_term) (e : emb_erased term EMB.abstract_term) =
  match e with
  | Hide _ x -> Some x
  | _ -> None

let nbe_reveal (a:NBE.abstract_nbe_term) (e : emb_erased NBETerm.t NBE.abstract_nbe_term) =
  match e with
  | Hide _ x -> Some x
  | _ -> None

let ops = [
  (* unconditionally reduce reveal #t' (hide #t x) to x *)
  mk2' 1 PC.reveal s_reveal nbe_reveal
]

let s_hide (a:EMB.abstract_term) (e : emb_erased term EMB.abstract_term) =
  match e with
  | Reveal a' x when U.term_eq a.t a' -> Some x
  | _ -> None

let nbe_hide (a:NBE.abstract_nbe_term) (e : emb_erased NBETerm.t NBE.abstract_nbe_term) =
  match e with
  | Reveal a' x when NBETerm.term_eq a.t a' -> Some x
  | _ -> None

let simplify_ops = [
  (* reduce hide t (reveal #t x) to x, making sure the types match exactly. *)
  mk2' 1 PC.hide s_hide nbe_hide;
]
