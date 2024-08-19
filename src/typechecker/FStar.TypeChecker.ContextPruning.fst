module FStar.TypeChecker.ContextPruning
open FStar.Compiler
open FStar.Compiler.Effect
open FStar.Ident
open FStar.Syntax.Syntax
open FStar.TypeChecker.Env
open FStar.Class.Monad
module BU = FStar.Compiler.Util
module SS = FStar.Syntax.Subst
open FStar.Class.Setlike

type ctxt = {
  env: env;
  reached: list lident;
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
  return <| Env.find_lemmas_waiting_on_trigger lid ctxt.pending_lemmas

let remove_trigger_for_lemma (pat:lident) (lem:lident)
: st bool
= let! ctxt = get in
  let pp, eligible = Env.remove_trigger_for_lemma pat lem ctxt.pending_lemmas in
  put {ctxt with pending_lemmas=pp} ;!
  return eligible
 
let ctx_contains (x:lident)
: st bool
= let! ctxt = get in
  return (List.mem x ctxt.reached)

let lookup_definition (x:lident)
: st (option (univ_names & term))
= let! ctxt = get in
  return <| FStar.TypeChecker.Env.lookup_definition [Env.Unfold delta_constant] ctxt.env x
let lookup_type (x:lident)
: st (option (univ_names & term))
= return None
let add_lident (x:lident)
: st unit
= let! ctxt = get in
  put {ctxt with reached=x::ctxt.reached}

let rec context_of_term (t:term)
: st (list lident)
= let fvs = FStar.Syntax.Free.fvars t in
  foldM_left
    (fun acc fv ->
      if! ctx_contains fv
      then return acc
      else (
        add_lident fv ;!
        match! lookup_definition fv with
        | None -> return (fv::acc)
        | Some (_, t) -> let! fvs = context_of_term t in return (fv::fvs)))
    []
    (elems fvs)

let trigger_pending_lemmas (lids:list lident)
: st (either (list lident) bool) //either some lemmas were triggered; or maybe nothing changed
= foldM_left
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
        | [] -> return (Inr true) //something changed
        | _ -> return (Inl eligible_lemmas))
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
  match! trigger_pending_lemmas new_fvs with
  | Inl triggered ->
    let! lemma_types =
      foldM_left
        (fun acc lem ->
          if! ctx_contains lem
          then return acc
          else (
            add_lident lem ;!
            match! lookup_type lem with
            | None -> return acc
            | Some (_, t) -> return (t::acc)
          ))
        []
        triggered
    in
    scan lemma_types
  | Inr _ -> return ()

let context_of (env:env) (t:term)
: list lident
= let init = { env; pending_lemmas=env.pending_lemmas; reached=[] } in
  let _, ctxt = scan [t] init in
  ctxt.reached