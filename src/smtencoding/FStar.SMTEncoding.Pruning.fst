module FStar.SMTEncoding.Pruning
open FStar.Compiler.Effect
open FStar
open FStar.List.Tot
open FStar.Compiler
open FStar.SMTEncoding.Term
open FStar.Class.Setlike
open FStar.Class.Monad
module BU = FStar.Compiler.Util
type triggers = list (list string)

type pruning_state = {
  // assumptions: list assumption;
  trigger_to_assumption: BU.psmap (list assumption);
  assumption_to_triggers: BU.psmap triggers;
  assumption_name_map: BU.psmap decl;
  ambients: list string; //assumptions with no triggers
}

let init
: pruning_state 
= { //assumptions = [];
    trigger_to_assumption = BU.psmap_empty ();
    assumption_to_triggers = BU.psmap_empty ();
    assumption_name_map = BU.psmap_empty ();
    ambients=[] }

let add_assumption_to_triggers (a:assumption) (p:pruning_state) (trigs:triggers)
: pruning_state
= let p = { p with assumption_name_map = BU.psmap_add p.assumption_name_map a.assumption_name (Assume a) } in
  match trigs with
  | [] -> { p with ambients = a.assumption_name :: p.ambients }
  | _ -> { p with assumption_to_triggers = BU.psmap_add p.assumption_to_triggers a.assumption_name trigs }

let add_trigger_to_assumption (a:assumption) (p:pruning_state) (trig:string)
: pruning_state
= match BU.psmap_try_find p.trigger_to_assumption trig with
  | None -> { p with trigger_to_assumption = BU.psmap_add p.trigger_to_assumption trig [a] }
  | Some l -> { p with trigger_to_assumption = BU.psmap_add p.trigger_to_assumption trig (a::l) }

let trigger_reached (p:pruning_state) (trig:string)
: pruning_state
= { p with trigger_to_assumption = BU.psmap_remove p.trigger_to_assumption trig }

let remove_trigger_for_assumption (p:pruning_state) (aname:string) (trig:string)
: pruning_state & bool
= match BU.psmap_try_find p.assumption_to_triggers aname with
  | None -> p, false
  | Some l -> 
    let remaining_triggers =
      l |> List.map (fun disjunct ->
      disjunct |> List.filter (fun x -> x <> trig))
    in
    let eligible = BU.for_some Nil? remaining_triggers in
    { p with assumption_to_triggers = BU.psmap_add p.assumption_to_triggers aname remaining_triggers },
    eligible

let rec assumptions_of_decl (d:decl)
: list assumption
= match d with
  | Assume a -> [a]
  | Module (_, ds) -> List.collect assumptions_of_decl ds
  | d -> []

let triggers_of_assumption (a:assumption)
: triggers
= let rec aux (t:term) =
    match t.tm with
    | Quant(Forall, triggers, _, _, _) ->
      triggers |> List.map (fun disjunct ->
      disjunct |> List.collect (fun t -> elems (Term.free_top_level_names t)))
    | Labeled (t, _, _)
    | LblPos (t, _) -> aux t
    | _ -> []
  in aux a.assumption_term

let add_assumptions (ds:list decl) (p:pruning_state)
: pruning_state
= let assumptions = List.collect assumptions_of_decl ds in
  //let p = { p with assumptions = p.assumptions @ assumptions } in
  let p =
    List.fold_left
      (fun p a -> 
        let triggers = triggers_of_assumption a in
        let p = List.fold_left (List.fold_left (add_trigger_to_assumption a)) p triggers in
        add_assumption_to_triggers a p triggers)
      p assumptions
  in
  p

let sym = string
let reached_assumption_names = FStar.Compiler.RBSet.rbset string

type ctxt = {
  p: pruning_state;
  reached: reached_assumption_names;
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

let mark_trigger_reached (x:sym)
: st unit
= let! ctxt = get in
  put {ctxt with p=trigger_reached ctxt.p x }

let find_assumptions_waiting_on_trigger (x:sym)
: st (list assumption)
= let! ctxt = get in
  match BU.psmap_try_find ctxt.p.trigger_to_assumption x with
  | None -> return []
  | Some l -> return l

let reached_assumption (aname:string)
: st unit
= let! ctxt = get in
  put {ctxt with reached=add aname ctxt.reached}

let remove_trigger_for (trig:sym) (a:assumption)
: st bool
= let! ctxt = get in
  let p, eligible = remove_trigger_for_assumption ctxt.p trig a.assumption_name in
  put {ctxt with p} ;!
  return eligible
 
let already_reached (aname:string)
: st bool
= let! ctxt = get in
  return (mem aname ctxt.reached)

let trigger_pending_assumptions (lids:list sym)
: st (either (list assumption) bool) //either some assumptions were triggered; or maybe nothing changed
= let join_acc acc next =
    match acc, next with
    | Inl l, Inl m -> Inl (l @ m)
    | Inl l, Inr _ -> Inl l
    | Inr _, Inl m -> Inl m
    | Inr l, Inr m -> Inr (l || m)
  in
  foldM_left
    (fun acc lid ->
      match! find_assumptions_waiting_on_trigger lid with
      | [] -> return acc
      | assumptions ->
        mark_trigger_reached lid ;!
        let! eligible_assumptions =
          foldM_left
            (fun acc assumption ->
              if! remove_trigger_for lid assumption
              then return (assumption::acc)
              else return acc)
            []
            assumptions
        in
        match eligible_assumptions with
        | [] -> return (join_acc acc <| Inr true) //something changed
        | _ -> return (join_acc acc <| Inl eligible_assumptions))
  (Inr false)
  lids

let rec scan (ds:list assumption)
: st unit
= let new_syms = List.collect (fun a -> a.assumption_free_names) ds in
  // BU.print1 "Scanned terms got %s\n" (show new_fvs);
  match! trigger_pending_assumptions new_syms with
  | Inl triggered ->
    let! to_scan =
      foldM_left
        (fun acc assumption ->
          if! already_reached assumption.assumption_name
          then return acc
          else (
            reached_assumption assumption.assumption_name ;!
            return <| assumption::acc
          ))
        []
        triggered
    in
    scan to_scan
  | Inr _ -> return ()


let prune (p:pruning_state) (roots:list decl)
: list decl
= let roots = List.collect assumptions_of_decl roots in
  let init = { p; reached = empty () } in
  let _, ctxt = scan roots init in
  let reached_names = elems ctxt.reached in
  let reached_assumptions =
    List.collect
      (fun name ->
        match BU.psmap_try_find ctxt.p.assumption_name_map name with
        | None -> []
        | Some a -> [a]) 
      (reached_names@p.ambients)
  in
  reached_assumptions