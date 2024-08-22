module FStar.TypeChecker.ContextPruning
open FStar.Compiler
open FStar.Compiler.Effect
open FStar.Ident
open FStar.Syntax.Syntax
open FStar.TypeChecker.Env
open FStar.Class.Monad
open FStar.Class.Show
open FStar.List.Tot
module BU = FStar.Compiler.Util
module SS = FStar.Syntax.Subst
open FStar.Class.Setlike

let lid_set = FStar.Compiler.RBSet.rbset lident

type ctxt = {
  env: env;
  reached: lid_set;
  pending_lemmas: pending_lemma_patterns;
}


let st a = ctxt -> (a & ctxt)
let get : st ctxt = fun s -> (s, s)
let put (c:ctxt) : st unit = fun _ -> ((), c)
instance st_monad: monad st = {
  return= (fun (#a:Type) (x:a) -> (fun s -> (x, s)) <: st a);
  ( let! ) = (fun (#a #b:Type) (m:st a) (f:a -> st b) (s:ctxt) ->
                let (x, s) = m s in
                f x s)
}

let remove_trigger (lid:lident)
: st unit
= let! ctxt = get in
  put {ctxt with pending_lemmas=remove_pending_lemma lid ctxt.pending_lemmas}

let find_lemmas_waiting_on_trigger (lid:lident)
: st (list lident)
= let! ctxt = get in
  let lems = Env.find_lemmas_waiting_on_trigger lid ctxt.pending_lemmas in 
  // BU.print2 "Lemmas waiting on trigger %s = %s\n" (show lid) (show lems);
  return lems

let add_lident (x:lident)
: st unit
= let! ctxt = get in
  put {ctxt with reached=add x ctxt.reached}

let remove_trigger_for_lemma (pat:lident) (lem:lident)
: st bool
= let! ctxt = get in
  // BU.print2 "Removing trigger %s for %s\n" (show pat) (show lem);
  let pp, eligible = Env.remove_trigger_for_lemma pat lem ctxt.pending_lemmas in
  put {ctxt with pending_lemmas=pp} ;!
  // let! _ =
  //   if eligible 
  //   then add_lident lem
  //   else return () in
  return eligible
 
let ctx_contains (x:lident)
: st bool
= let! ctxt = get in
  return (mem x ctxt.reached)

let reachable_of_inductive env (ty:lident)
= let aux (a_lids, a_tys) ty =
    let _,dcs = Env.datacons_of_typ env ty in
    let tys =
      List.collect
        (fun dc -> 
          match Env.try_lookup_lid env dc with
          | None -> []
          | Some ((_, t), _) -> [t])
        dcs
    in
    let tys =
      match Env.try_lookup_lid env ty with
      | None -> tys
      | Some ((_, t), _) -> t::tys
    in
    dcs@a_lids, tys@a_tys
  in
  let aux mutuals = List.fold_left aux ([], []) mutuals in
  match Env.lookup_qname env ty with
  | Some (Inr (se, _), _) -> (
    match se.sigel with
    | Sig_inductive_typ { mutuals } -> aux mutuals
    | _ -> [], []
  )
  | _ -> [], []
    
let lookup_lident_in_env env (x:lident)
: list lident  //identifiers reachable from x
  & list term  //terms that need to be scanned=
= match Env.lookup_qname env x with
  | None -> [], []
  | Some (Inl (_, t), _) -> [], [t]
  | Some (Inr (se, _), _) -> (
    match se.sigel with
    | Sig_inductive_typ { lid } -> reachable_of_inductive env lid
    | Sig_datacon { ty_lid } -> reachable_of_inductive env ty_lid 
    | Sig_declare_typ { t } -> [], [t]
    | Sig_let { lbs; lids=mutuals } ->
      mutuals,
      snd lbs |> List.collect (fun lb -> [lb.lbtyp; lb.lbdef])
    | Sig_assume { phi } -> [], [phi]
    | _ -> [], []
  )

let lookup_definition_and_type (x:lident)
: st (list lident & list term)
= let open FStar.TypeChecker.Env in
  let! ctxt = get in
  let res = lookup_lident_in_env ctxt.env x in
  return res
  // let def =
  //   match lookup_definition [Env.Unfold delta_constant] ctxt.env x with
  //   | None -> []
  //   | Some (_, t) -> [t]
  // in
  // return <|
  // (match try_lookup_lid ctxt.env x with
  // | None -> def
  // | Some ((_, t),_) -> t::def)


let lookup_type (x:lident)
: st (option term)
= let! ctxt = get in
  match Env.try_lookup_lid ctxt.env x with
  | None ->
    return None
  | Some ((_, t), _) -> return (Some t)

let rec context_of_term (t:term)
: st (list lident)
= let fvs = FStar.Syntax.Free.fvars t in
  foldM_left
    (fun acc fv ->
      if! ctx_contains fv
      then return acc
      else (
        add_lident fv ;!
        let! lids, terms = lookup_definition_and_type fv in
        iterM (fun lid -> add_lident lid) lids ;!
        foldM_left
          (fun acc t ->
            let! fvs = context_of_term t in
            return (fvs @ acc))
          (fv::lids@acc) terms))
    []
    (elems fvs)

let trigger_pending_lemmas (lids:list lident)
: st (either (list lident) bool) //either some lemmas were triggered; or maybe nothing changed
= let join_acc acc next =
    match acc, next with
    | Inl l, Inl m -> Inl (l @ m)
    | Inl l, Inr _ -> Inl l
    | Inr _, Inl m -> Inl m
    | Inr l, Inr m -> Inr (l || m)
  in
  foldM_left
    (fun acc lid ->
      match! find_lemmas_waiting_on_trigger lid with
      | [] -> return acc
      | lemmas ->
        remove_trigger lid ;!
        let! eligible_lemmas =
          foldM_left
            (fun acc lem ->
              if! remove_trigger_for_lemma lid lem
              then return (lem::acc)
              else return acc)
            []
            lemmas
        in
        match eligible_lemmas with
        | [] -> return (join_acc acc <| Inr true) //something changed
        | _ -> return (join_acc acc <| Inl eligible_lemmas))
  (Inr false)
  lids
open FStar.List.Tot
let rec scan (ts:list term)
: st unit
= let! new_fvs =
    foldM_left
      (fun acc t ->
        let! new_fvs = context_of_term t in
        return (new_fvs @ acc))
      [] ts
  in
  // BU.print1 "Scanned terms got %s\n" (show new_fvs);
  match! trigger_pending_lemmas new_fvs with
  | Inl triggered ->
    let! lemma_types =
      foldM_left
        (fun acc lem ->
          if! ctx_contains lem
          then (
            return acc
          )
          else (
            add_lident lem ;!
            match! lookup_type lem with
            | None -> return acc
            | Some t -> 
              return (t::acc)
          ))
        []
        triggered
    in
    scan lemma_types
  | Inr _ -> return ()

let context_of (env:env) (ts:list term)
: list lident
= let init = { env; pending_lemmas=env.pending_lemmas; reached=empty() } in
  let _, ctxt = scan ts init in
  elems ctxt.reached