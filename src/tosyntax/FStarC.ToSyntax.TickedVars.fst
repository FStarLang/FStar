(*
  Copyright 2008-2025 Nikhil Swamy and Microsoft Research

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

  http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
*)
module FStarC.ToSyntax.TickedVars

open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.Syntax
open FStarC.Syntax.Syntax
open FStarC.Syntax.DsEnv
open FStarC.Parser.AST
open FStarC.Ident
open FStarC.Class.Monad
open FStarC.Writer
open FStarC.Class.Setlike

module C   = FStarC.Parser.Const
module Env = FStarC.Syntax.DsEnv

let ident_is_ticked (id: ident) : bool =
  let nm   = string_of_id id in
  String.length nm > 0 && String.get nm 0 = '\''

(* Empty namespace (so a local variable) and its name component starts with a tick *)
let lident_is_ticked (id: lident) : bool =
  let ns = ns_of_lid id in
  let id = ident_of_lid id in
  Nil? ns && ident_is_ticked id

instance _ : Class.Monoid.monoid (RBSet.t ident) = {
  mzero = RBSet.empty ();
  mplus = RBSet.union;
}

(* A monad for collecting free ticked variables in a term. *)

(* The monad we use to collect free ticked variables.
TODO: this should probably be a flatset if we want to collect
these variables in order of appearence, but the current code
will sort the list at the end, so an RBSet works fne. *)
let m = writer (RBSet.t ident)

let emit1 (x : ident) : m unit =
  emit (singleton x)

let rec go_term (env : DsEnv.env) (t: term) : m unit =
  match t.tm with
  | Paren t -> go_term env t
  | Labeled _ -> failwith "Impossible --- labeled source term"

  | Var a ->
    if lident_is_ticked a && None? (Env.try_lookup_id env (Ident.ident_of_lid a)) then
      emit1 (Ident.ident_of_lid a)
    else
      return ()

  | Var x ->
    return ()

  | Wild
  | Const _
  | Uvar _

  | Projector _
  | Discrim _
  | Name _  -> return ()

  | Requires t
  | Ensures t
  | Decreases t
  | NamedTyp(_, t) -> go_term env t

  | LexList l -> iterM (go_term env) l

  | WFOrder (rel, e) ->
    go_term env rel;!
    go_term env e

  | Paren t -> failwith "impossible"

  | Ascribed(t, t', tacopt, _) ->
    go_term env t;!
    go_term env t';!
    (match tacopt with
    | None -> return ()
    | Some tac -> go_term env tac)

  | Construct(_, ts) -> iterM (fun (a, _) -> go_term env a) ts
  | Op(_, ts)        -> iterM (go_term env) ts

  | App(t1,t2,_)     ->
    go_term env t1;!
    go_term env t2

  | Refine (b, t) ->
    let! env' = go_binder env b in
    go_term env' t

  | Sum (binders, body) ->
    let! env' =
      foldM_left (fun env bt ->
        match bt with
        | Inl binder -> go_binder env binder
        | Inr t -> go_term env t;! return env
      ) env binders in
    go_term env' body

  | Product (binders, body) ->
    let! env' = foldM_left go_binder env binders in
    go_term env' body

  | Project (t, _) -> go_term env t

  | Attributes cattributes ->
      (* attributes should be closed but better safe than sorry *)
      iterM (go_term env) cattributes

  | CalcProof (rel, init, steps) ->
    go_term env rel;!
    go_term env init;!
    iterM (fun (CalcStep (rel, just, next)) ->
      go_term env rel;!
      go_term env just;!
      go_term env next) steps

  | ElimForall (bs, t, ts) ->
    let! env' = go_binders env bs in
    go_term env' t;!
    iterM (go_term env') ts

  | ElimExists (binders, p, q, y, e) ->
    go_term env q;!
    let! env' = go_binders env binders in
    go_term env' p;!
    let! env'' = go_binder env' y in
    go_term env'' e

  | ElimImplies (p, q, e) ->
    go_term env p;!
    go_term env q;!
    go_term env e

  | ElimOr(p, q, r, x, e, x', e') ->
    go_term env p;!
    go_term env q;!
    go_term env r;!
    let! env_x = go_binder env x in
    go_term env_x e;!
    let! env_x' = go_binder env x' in
    go_term env_x' e'

  | ElimAnd(p, q, r, x, y, e) ->
    go_term env p;!
    go_term env q;!
    go_term env r;!
    let! env' = go_binders env [x; y] in
    go_term env' e

  | ListLiteral ts -> iterM (go_term env) ts
  | SeqLiteral ts  -> iterM (go_term env) ts

  | Abs _  (* not closing implicitly over free vars in all these forms: TODO: Fixme! *)
  | Function _
  | Let _
  | LetOpen _
  | If _
  | QForall _
  | QExists _
  | QuantOp _
  | Record _
  | Match _
  | TryWith _
  | Bind _
  | Quote _
  | VQuote _
  | Antiquote _
  | Seq _ -> return ()


and go_binder (env : DsEnv.env) (b: binder) : m DsEnv.env =
  match b.b with
  | Variable x ->
    (* This handles ticks in declarations like `type foo 'a`. The 'a
    is used in a binding position. *)
    if ident_is_ticked x && None? (Env.try_lookup_id env x) then
      emit1 x
    else
      return ();!
    let env', _ = Env.push_bv env x in
    return env'

  | Annotated (x, t) ->
    if ident_is_ticked x && None? (Env.try_lookup_id env x) then
      emit1 x
    else
      return ();!
    go_term env t;!
    let env', _ = Env.push_bv env x in
    return env'

  | NoName t ->
    go_term env t;!
    return env

and go_binders (env : DsEnv.env) (bs: list binder) : m DsEnv.env =
  foldM_left go_binder env bs

(* GM: Note: variables are sorted alphabetically. This is weird to me,
   I would expect them to be abstracted over in textual order, but I'm
   retaining this feature. *)
let free_ticked_vars env t : list ident =
  let fvs, () = run_writer <| go_term env t in
  elems fvs // relying on elems from RBSet returning a sorted list

let rec unparen t = match t.tm with
  | Paren t -> unparen t
  | _ -> t

let tm_type r = mk_term (Name (lid_of_path ["Type"] r)) r Kind

let close env t =
  let ftv = free_ticked_vars env t in
  if Nil? ftv then t else
    let binders = ftv |> List.map (fun x -> mk_binder (Annotated(x, tm_type (pos x))) (pos x) Type_level (Some Implicit)) in
    let result = mk_term (Product(binders, t)) t.range t.level in
    result

let close_fun env (t:term) =
  let ftv = free_ticked_vars env t in
  if Nil? ftv then t else
    let binders = ftv |> List.map (fun x -> mk_binder (Annotated(x, tm_type (pos x))) (pos x) Type_level (Some Implicit)) in
    let t = match (unparen t).tm with
     | Product _ -> t
     | _ -> mk_term (App(mk_term (Name C.effect_Tot_lid) t.range t.level, t, Nothing)) t.range t.level in
    let result = mk_term (Product(binders, t)) t.range t.level in
    result
