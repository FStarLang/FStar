(*
   Copyright 2024 Microsoft Research

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
module FStarC.SMTEncoding.Pruning
open FStarC.Effect
open FStar.List.Tot
open FStarC
open FStarC.SMTEncoding.Term
open FStarC.Class.Setlike
open FStarC.Class.Show
open FStarC.Class.Monad
module BU = FStarC.Util
type triggers = list (list string)
type triggers_set = list (RBSet.t string)

let triggers_as_triggers_set (ts:triggers) : triggers_set = List.map from_list ts

type pruning_state = {
  //A macro is a (define-fun f ... (body)); Maps macro name 'f' to the free names of its body
  macro_freenames: PSMap.t (list string); 
  // Maps trigger symbols to assumptions that have triggers that mention that symbol
  // E.g., given `A : forall x. {:pattern (p x; q x) \/ (p' x; q' x)} R`
  // trigger_to_assumption maps p -> A, q -> A, p' -> A, q' -> A
  trigger_to_assumption: PSMap.t (list assumption);
  // Maps assumption name to triggers that  "waiting" on it
  // E.g., in the example above, assumption_to_trigger contains A -> [[p;q]; [p';q']]
  assumption_to_triggers: PSMap.t triggers_set;
  // Maps assumption names to the assumptions themselves
  assumption_name_map: PSMap.t decl;
  //assumptions with no triggers that will always included
  ambients: list string;
  //extra roots that will be added to the initial set of roots
  extra_roots: list assumption
}

let debug (f: unit -> unit) : unit =
  if Options.Ext.enabled "debug_context_pruning"
  then f()

let print_pruning_state (p:pruning_state)
: string
= let t_to_a =
    PSMap.fold
      p.trigger_to_assumption
      (fun k v (acc:list (string & int)) -> (k, List.length v) :: acc)
      []
  in
  let t_to_a = BU.sort_with (fun x y -> snd x - snd y) t_to_a in
  let a_to_t =
    PSMap.fold
      p.assumption_to_triggers
      (fun k v acc ->
        BU.format2 "[%s -> %s]" 
            k
            (show v) :: acc)
      []
  in
  let macros =
    PSMap.fold
      p.macro_freenames
      (fun k v acc ->
        BU.format2 "[%s -> %s]" 
            k
            (show v) :: acc)
      []
  in
  BU.format3 "Pruning state:\n\tTriggers to assumptions:\n\t%s\nAssumptions to triggers:\n\t%s\nMacros:\n\t%s\n"
    (String.concat "\n\t" (List.map show t_to_a))
    (String.concat "\n\t" a_to_t)
    (String.concat "\n\t" macros)

instance show_pruning_state: showable pruning_state = { show = print_pruning_state }

(* Initial state: everything is empty *)
let init
: pruning_state 
= { macro_freenames = PSMap.empty ();
    trigger_to_assumption = PSMap.empty ();
    assumption_to_triggers = PSMap.empty ();
    assumption_name_map = PSMap.empty ();
    ambients=[];
    extra_roots=[] }

(* Add: trig -> a*)
let add_trigger_to_assumption (a:assumption) (p:pruning_state) (trig:string)
: pruning_state
= match PSMap.try_find p.trigger_to_assumption trig with
  | None -> 
    { p with trigger_to_assumption = PSMap.add p.trigger_to_assumption trig [a] }
  | Some l -> { p with trigger_to_assumption = PSMap.add p.trigger_to_assumption trig (a::l) }

// Names that are excluded from the set of free names
// Since they are very common and are not useful to scan as triggers
let exclude_names : RBSet.t string =
  from_list [
    "SFuel";
    "ZFuel";
    "HasType";
    "HasTypeZ";
    "HasTypeFuel";
    "Valid";
    "ApplyTT";
    "ApplyTF";
    "Prims.lex_t"
  ]

let free_top_level_names t = diff (Term.free_top_level_names t) exclude_names
let assumption_free_names a = diff a.assumption_free_names exclude_names

(* Triggers of a universally quantified term *)
let triggers_of_term (t:term)
: triggers_set
= let rec aux (t:term) =
    match t.tm with
    | Quant(Forall, triggers, _, _, _) ->
      triggers |> List.map (fun disjunct ->
      disjunct |> List.fold_left (fun out t -> union out (free_top_level_names t)) (empty()))
    | Labeled (t, _, _)
    | LblPos (t, _) -> aux t
    | _ -> []
  in aux t

(* This function has lots of special cases for F*'s SMT encoding, 
   particularly its handling of top-level non-quantified assumptions.

   One quirk to note here, that we should probably fix in the SMT encoding
   itself:

    - Applications of nullary functions are sometimes encoded as
      App(Var "name", []) and sometiems as FreeV(FV("name", _, _))  
*)
let maybe_add_ambient (a:assumption) (p:pruning_state)
: pruning_state
= let add_assumption_with_triggers (triggers:triggers_set) =
    (* associate the triggers with the assumption in both directions *)
    let p = 
      { p with
        assumption_to_triggers=
        PSMap.add p.assumption_to_triggers a.assumption_name triggers}
    in
    List.fold_left (List.fold_left (add_trigger_to_assumption a)) p (List.map elems triggers)
  in
  let is_empty triggers =
    match triggers with
    | [] -> true
    | [t] -> is_empty t
    | _ -> false
  in
  let is_ambient_refinement ty =
    match ty.tm with
    | App(Var "Prims.squash", _) -> true
    | App(Var name, _) 
    | FreeV(FV(name, _, _)) -> BU.starts_with name "Tm_refine_"
    | _ -> false
  in
  let ambient_refinement_payload ty =
    match ty.tm with
    | App(Var "Prims.squash", [t]) -> t
    | _ -> ty
  in
  begin
    match a.assumption_term.tm with
    // - The top-level assumption `function_token_typing_Prims.__cache_version_number__`
    //   is always included in the pruned set, since it provides an inhabitation proof
    //   for int which some proofs rely on
    | _ when a.assumption_name = "function_token_typing_Prims.__cache_version_number__" ->
      { p with ambients = a.assumption_name::p.ambients }

    // - l_quant_interp assumptions give interpretations to deeply embedded quantifiers
    //   and have a specific shape of an Iff, where the LHS has a pattern, if the
    //   user annotated one.
    | App(Iff, [t0; t1]) when BU.starts_with a.assumption_name "l_quant_interp" -> (
      let triggers_lhs = free_top_level_names t0 in
      add_assumption_with_triggers [triggers_lhs]
    )

    // - Top-level `assume A : t` facts in F* are encoded as "assumption_" named
    //   declarations, handled similarly to squash and Tm_refine_ assumptions. 
    | _ when BU.starts_with a.assumption_name "assumption_" -> (
      let triggers = triggers_of_term a.assumption_term in
      if is_empty triggers
      then (
        let triggers = [free_top_level_names a.assumption_term] in
        add_assumption_with_triggers triggers
      )
      else 
        add_assumption_with_triggers triggers
    )    

    // - Top-level assumptions of the form `HasType term (squash ty)`
    //   or `HasType term (Tm_refine_... )` are deemed ambient and are
    //   always included in the pruned set and added as extra roots.
    | App (Var "HasType", [term; ty])
      when is_ambient_refinement ty -> (
      //HasType term (squash ty) is an ambient that should trigger on either the term or the type
      let triggers = triggers_of_term (ambient_refinement_payload ty) in
      if is_empty triggers
      then { p with ambients = a.assumption_name::p.ambients; 
                    extra_roots = a::p.extra_roots }
      else add_assumption_with_triggers triggers
    )
 
    // - Partial applications are triggered with a __uu__PartialApp token; this is
    //   triggered on either the symbol itself or its nullary token
    | App (Var "Valid", 
          [{tm=App (Var "ApplyTT", [{tm=FreeV (FV("__uu__PartialApp", _, _))}; term])}])
    | App (Var "Valid", 
          [{tm=App (Var "ApplyTT", [{tm=App(Var "__uu__PartialApp", _)}; term])}]) ->
      let triggers =
        match term.tm with
        | FreeV(FV(token, _, _))
        | App(Var token, []) ->
          if BU.ends_with token "@tok"
          then [singleton token; singleton (BU.substring token 0 (String.length token - 4))]
          else [singleton token]
        | _ -> 
          []
      in
      add_assumption_with_triggers triggers

    // HasType, Valid, IsTotFun, and is-Tm_arrow are so common that we exclude them as triggers
    // and instead only consider the free names of the underlying terms
    | App (Var "Valid", [term])
    | App (Var "HasType", [term; _])
    | App (Var "IsTotFun", [term])
    | App (Var "is-Tm_arrow", [term]) ->
      add_assumption_with_triggers [free_top_level_names term]

    // Term_constr_id assumptions trigger on the free names of the underlying term
    | App (Eq, [ _; {tm=App (Var "Term_constr_id", [term])}]) ->
      add_assumption_with_triggers [free_top_level_names term]

    // Descend into conjunctions and collect their triggers
    // Fire if any of the conjuncts have triggers that fire
    | App (And, tms) ->
      let t1 = List.collect triggers_of_term tms in
      add_assumption_with_triggers t1

    // Assumptions named "equation_" are encodings of F* definitions and are
    // equations oriented from left to right
    | App (Eq, [t0; t1]) when BU.starts_with a.assumption_name "equation_" ->
      let t0 = free_top_level_names t0 in
      add_assumption_with_triggers [t0]

    // Other equations and bi-implications are bidirectional
    | App (Iff, [t0; t1])
    | App (Eq, [t0; t1]) ->
      let t0 = free_top_level_names t0 in
      let t1 = free_top_level_names t1 in
      add_assumption_with_triggers [t0; t1]

    // we get many vacuous True facts; just drop them
    | App (TrueOp, _) -> p

    // Oterwise, add to ambients without scanning them further
    | _ ->
      { p with ambients = a.assumption_name::p.ambients }
  end

// Add an assumption to the pruning state
// If the assumption has triggers, add it to the trigger map
// Otherwise, use the custom logic for ambients
let add_assumption_to_triggers (a:assumption) (p:pruning_state) (trigs:triggers_set)
: pruning_state
= let p = { p with assumption_name_map = PSMap.add p.assumption_name_map a.assumption_name (Assume a) } in
  match trigs with
  | [] -> maybe_add_ambient a p
  | _ -> { p with assumption_to_triggers = PSMap.add p.assumption_to_triggers a.assumption_name trigs }

// Mark a trigger as reached; removing it from the trigger map
let trigger_reached (p:pruning_state) (trig:string)
: pruning_state
= { p with trigger_to_assumption = PSMap.remove p.trigger_to_assumption trig }

// remove one trigger from waiting triggers of aname
// if aname now has an empty set of triggers, return true, marking it as reachable/eligible
let remove_trigger_for_assumption (p:pruning_state) (trig:string) (aname:string)
: pruning_state & bool
= match PSMap.try_find p.assumption_to_triggers aname with
  | None ->
    // debug (fun _ -> BU.print2 "Removing trigger %s for assumption %s---no assumption found\n" trig aname);
    p, false
  | Some l -> 
    let remaining_triggers =
      l |> List.map (fun ts -> remove trig ts)
    in
    let eligible = BU.for_some is_empty remaining_triggers in
    // debug (fun _ ->
    //   BU.print5 "Removing trigger %s for assumption %s---eligible? %s, original triggers %s, remaining triggers %s\n"
    //     trig aname (show eligible) (show l) (show remaining_triggers));
    { p with assumption_to_triggers = PSMap.add p.assumption_to_triggers aname remaining_triggers },
    eligible

let rec assumptions_of_decl (d:decl)
: list assumption
= match d with
  | Assume a -> [a]
  | Module (_, ds) -> List.collect assumptions_of_decl ds
  | d -> []

// Add a declaration to the pruning state, updating the trigger and assumption tables
// and macro tables
let rec add_decl (d:decl) (p:pruning_state)
: pruning_state
= match d with
  | Assume a ->
    let triggers = triggers_of_term a.assumption_term in
    let p = List.fold_left (List.fold_left (add_trigger_to_assumption a)) p (List.map elems triggers) in
    add_assumption_to_triggers a p triggers
  | Module (_, ds) -> List.fold_left (fun p d -> add_decl d p) p ds
  | DefineFun(macro, _, _, body, _) ->
    let free_names = elems (free_top_level_names body) in
    let p = { p with macro_freenames = PSMap.add p.macro_freenames macro free_names } in
    p
  | _ -> p
    
let add_decls (ds:list decl) (p:pruning_state)
: pruning_state
= List.fold_left (fun p d -> add_decl d p) p ds

let sym = string
let reached_assumption_names = FStarC.RBSet.rbset string

// The main pruning algorithm is expresses as a state monad over the ctxt
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

// When a trigger as reached, mark it, removing it from the trigger map
let mark_trigger_reached (x:sym)
: st unit
= let! ctxt = get in
  put {ctxt with p=trigger_reached ctxt.p x }

// All assumptions that are waiting on a trigger
let find_assumptions_waiting_on_trigger (x:sym)
: st (list assumption)
= let! ctxt = get in
  match PSMap.try_find ctxt.p.trigger_to_assumption x with
  | None -> return []
  | Some l -> return l

// Mark an assumption as reached, to include in the resulting pruned set
// Remove it from the assumption map, so that we don't scan it again
let reached_assumption (aname:string)
: st unit
= let! ctxt = get in
  let p = { ctxt.p with assumption_to_triggers = PSMap.remove ctxt.p.assumption_to_triggers aname } in
  put {ctxt with reached=add aname ctxt.reached }

// Remove trigger x from assumption a, and return true if a is now eligible
let remove_trigger_for (trig:sym) (a:assumption)
: st bool
= let! ctxt = get in
  let p, eligible = remove_trigger_for_assumption ctxt.p trig a.assumption_name in
  put {ctxt with p} ;!
  return eligible

// Check if an assumption has already been reached 
let already_reached (aname:string)
: st bool
= let! ctxt = get in
  return (mem aname ctxt.reached)

// All assumptions that are now eligible given lids are reached
let trigger_pending_assumptions (lids:list sym)
: st (list assumption)
= foldM_left
    (fun acc lid ->
      match! find_assumptions_waiting_on_trigger lid with
      | [] -> return acc
      | assumptions ->
        // debug (fun _ -> BU.print2 "Found assumptions waiting on trigger %s: %s\n" lid (show <| List.map (fun a -> a.assumption_name) assumptions));
        mark_trigger_reached lid ;!
        foldM_left
          (fun acc assumption ->
            if! remove_trigger_for lid assumption
            then return (assumption::acc)
            else return acc)
          acc
          assumptions)
  []
  lids

// The main scanning loop
let rec scan (ds:list assumption)
: st unit
= let! ctxt = get in
  let macro_expand (s:sym) : list sym =
    match PSMap.try_find ctxt.p.macro_freenames s with
    | None -> [s]
    | Some l -> s::l
  in
  // Collect the free names of all assumptions and macro expand them
  let new_syms = List.collect (fun a -> List.collect macro_expand (elems (assumption_free_names a))) ds in
  // debug (fun _ -> 
  //   BU.print1 ">>>Scanning %s\n"
  //     (ds |> List.map (fun a -> BU.format2 "%s -> [%s]" a.assumption_name (elems (assumption_free_names a) |> show)) |> String.concat "\n\t"));

  // Trigger all assumptions that are waiting on the new symbols
  match! trigger_pending_assumptions new_syms with
  | [] ->
    // Done if no new assumptions are eligible
    return ()
  | triggered ->
    // Otherwise, mark them as reached, and scan them
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


let prune (p:pruning_state) (roots:list decl)
: list decl
= // debug (fun _ -> BU.print_string (show p));
  // Collect all assumptions from the roots
  let roots = List.collect assumptions_of_decl roots in
  let init = { p; reached = empty () } in
  // Scan to find all reachable assumptions
  let _, ctxt = scan (roots@p.extra_roots) init in
  // Collect their names
  let reached_names = elems ctxt.reached in
  // Map them to assumptions, together with ambients
  let reached_assumptions =
    List.collect
      (fun name ->
        match PSMap.try_find ctxt.p.assumption_name_map name with
        | None -> []
        | Some a -> [a]) 
      (reached_names@p.ambients)
  in
  // if Options.Ext.enabled "debug_context_pruning"
  // then (
  //   BU.print1 "Retained %s assumptions\n" (show (List.length reached_assumptions))
  // );
  reached_assumptions