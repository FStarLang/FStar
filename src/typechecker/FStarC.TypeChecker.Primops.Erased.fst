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

type emb_erased (a:Type) = | Hide : x:a -> emb_erased a

instance e_erased (a:Type) (d : EMB.embedding a) : Tot (EMB.embedding (emb_erased a)) =
  let em (x:emb_erased a) rng shadow cbs =
    let Hide x = x in
    let h = S.fvar PC.hide None in
    U.mk_app h [S.iarg (EMB.type_of d); S.as_arg (EMB.embed x rng shadow cbs)]
  in
  let un (t:term) cbs : option (emb_erased a) =
    let head, args = U.head_and_args t in
    match (U.un_uinst head).n, args with
    | Tm_fvar fv, [_t; (a, None)] when fv_eq_lid fv PC.hide ->
      let! v = EMB.unembed a cbs in
      return (Hide v)
    | _ ->
      None
  in
  EMB.mk_emb_full em un
    (fun () -> S.t_erased_of (EMB.type_of d))
    (fun (Hide x) -> "Hide " ^ EMB.printer_of d x)
    (fun () -> ET_abstract)

instance nbe_e_erased (a:Type) (d : NBE.embedding a) : Tot (NBE.embedding (emb_erased a)) =
  let em cbs (x:emb_erased a) =
    let Hide x = x in
    let fv = S.lid_as_fv PC.hide None in
    NBE.mkFV fv [] [NBE.as_arg (NBE.embed d cbs x)]
  in
  let un cbs (t:NBETerm.t) : option (emb_erased a) =
    match NBETerm.nbe_t_of_t t with
    | NBETerm.FV (fv, _, [(_t, _); (body, _)])
      when fv_eq_lid fv PC.hide ->
      let! v = NBE.unembed d cbs body in
      return (Hide v)
    | _ ->
      None
  in
  NBETerm.mk_emb em un
    (fun () -> magic()) //NBET.t_erased_of (NBE.type_of d))
    (fun () -> ET_abstract)

let s_reveal (a:EMB.abstract_term) (e : emb_erased EMB.abstract_term) =
  let Hide x = e in Some x

let nbe_reveal (a:NBE.abstract_nbe_term) (e : emb_erased NBE.abstract_nbe_term) =
  let Hide x = e in Some x

let ops = [
  (* unconditionally reduce reveal #t' (hide #t x) to x *)
  mk2' 1 PC.reveal s_reveal nbe_reveal
]
