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

instance showable_psmap (_:showable 'a) : Tot (showable (PSMap.t 'a)) = {
  show = fun s -> show (PSMap.fold s (fun key value out -> Format.fmt2 "(%s -> %s)" key (show value) :: out) [])
}

let triggers_as_triggers_set (ts:triggers) : triggers_set = List.map from_list ts
type assumption_name = string

// sym: is the type of a name that can trigger an assumption
type sym = {
  sym_name: string; //The symbol itself
  sym_provenance: assumption_name; //the assumption in which it appeared---useful for diagnostics, allowing tracking why an assumption was retained
}

instance showable_sym : showable sym = { show = fun s -> Format.fmt2 "%s {from %s}" s.sym_name s.sym_provenance }

type assumption_remaining_triggers = {
  remaining_triggers : triggers_set; //awaiting these triggers
  already_triggered: list sym // The triggers that already fired
}

let mk_remaining_triggers ts = {
  remaining_triggers = ts;
  already_triggered = []
}

// This option prunes away all top-level assumptions that have no patterns on them
let no_ambients () = Options.Ext.enabled "context_pruning_no_ambients"

let should_retain_assumption (a:assumption) =
  if a.assumption_caption = Some "pretyping" //pretyping assumptions are deprecated
  then Options.Ext.enabled "pretyping_axioms" //unless '--ext pretyping_axioms' is on
  else true

type pruning_state = {
  defs_and_decls: list decl;
  defs_and_decls_map: PSMap.t decl;
  //A macro is a (define-fun f ... (body)); Maps macro name 'f' to the free names of its body
  macro_freenames: PSMap.t (list string); 
  // Maps trigger symbols to assumptions that have triggers that mention that symbol
  // E.g., given `A : forall x. {:pattern (p x; q x) \/ (p' x; q' x)} R`
  // trigger_to_assumption maps p -> A, q -> A, p' -> A, q' -> A
  trigger_to_assumption: PSMap.t (list assumption);
  // Maps assumption name to triggers that  "waiting" on it
  // E.g., in the example above, assumption_to_trigger contains A -> [[p;q]; [p';q']]
  assumption_to_triggers: PSMap.t assumption_remaining_triggers;
  // Maps assumption names to the assumptions themselves
  assumption_name_map: PSMap.t decl;
  //assumptions with no triggers that will always included
  ambients: list string;
  //extra roots that will be added to the initial set of roots
  extra_roots: list assumption;
  //ambients that are pruned away, useful for debuging the no_ambients option
  pruned_ambients: list string
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
        Format.fmt2 "[%s -> %s]" 
            k
            (show v.remaining_triggers) :: acc)
      []
  in
  let macros =
    PSMap.fold
      p.macro_freenames
      (fun k v acc ->
        Format.fmt2 "[%s -> %s]" 
            k
            (show v) :: acc)
      []
  in
  Format.fmt3 "Pruning state:\n\tTriggers to assumptions:\n\t%s\nAssumptions to triggers:\n\t%s\nMacros:\n\t%s\n"
    (String.concat "\n\t" (List.map show t_to_a))
    (String.concat "\n\t" a_to_t)
    (String.concat "\n\t" macros)

instance show_pruning_state: showable pruning_state = { show = print_pruning_state }

let init_macro_freenames = 
  PSMap.of_list [
    ("is-BoxBool", ["BoxBool"]);
    ("is-BoxInt", ["BoxInt"]);
    ("is-BoxString", ["BoxString"]);
    ("is-BoxReal", ["BoxReal"]);
  ]

(* Initial state: everything is empty *)
let init
: pruning_state 
= { defs_and_decls = [];
    defs_and_decls_map = PSMap.empty();
    macro_freenames = init_macro_freenames;
    trigger_to_assumption = PSMap.empty ();
    assumption_to_triggers = PSMap.empty ();
    assumption_name_map = PSMap.empty ();
    ambients=[];
    extra_roots=[];
    pruned_ambients=[] }

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
    | Labeled (t, _, _) -> aux t
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
        PSMap.add p.assumption_to_triggers a.assumption_name (mk_remaining_triggers triggers) }
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
    | App(Var "Prims.squash", [_;t]) -> t
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
      then (
        let p = { p with extra_roots = a :: p.extra_roots } in
        if no_ambients()
        then { p with pruned_ambients = a.assumption_name::p.pruned_ambients }
        else { p with ambients = a.assumption_name::p.ambients }
      )
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

    | App (Iff, [t0; t1]) -> (
      match t0.tm, t1.tm with
      | App(Var "Valid", [{tm=App(Var "Prims.hasEq", [_u; lhs])}]),
        App(Var "Valid", [{tm=App(Var "Prims.hasEq", [_v; rhs])}]) ->
        //hasEq t0 <==> hasEq t1
        //We have many of these for every refinement type; triggers from left-to-right
        //perhaps these are better written hasEq t1 ==> hasEq t0, and trigger in a goal-directed way
        let triggers = free_top_level_names lhs in
        add_assumption_with_triggers [triggers]

      | _ ->
        //Other bi-implications are bidirectional
        let t0 = free_top_level_names t0 in
        let t1 = free_top_level_names t1 in
        add_assumption_with_triggers [t0; t1]
    )

    // Other equations are bidirectional
    | App (Eq, [t0; t1]) ->
      let t0 = free_top_level_names t0 in
      let t1 = free_top_level_names t1 in
      add_assumption_with_triggers [t0; t1]

    // we get many vacuous True facts; just drop them
    | App (TrueOp, _) -> p

    // Oterwise, add to ambients without scanning them further
    | _ ->
      if no_ambients()
      then { p with pruned_ambients = a.assumption_name::p.pruned_ambients }
      else { p with ambients = a.assumption_name::p.ambients }
  end

// Add an assumption to the pruning state
// If the assumption has triggers, add it to the trigger map
// Otherwise, use the custom logic for ambients
let add_assumption_to_triggers (a:assumption) (p:pruning_state) (trigs:triggers_set)
: pruning_state
= let p = { p with assumption_name_map = PSMap.add p.assumption_name_map a.assumption_name (Assume a) } in
  match trigs with
  | [] -> maybe_add_ambient a p
  | _ -> { p with assumption_to_triggers = PSMap.add p.assumption_to_triggers a.assumption_name (mk_remaining_triggers trigs) }

// Mark a trigger as reached; removing it from the trigger map
let trigger_reached (p:pruning_state) (trig:string)
: pruning_state
= { p with trigger_to_assumption = PSMap.remove p.trigger_to_assumption trig }

// remove one trigger from waiting triggers of aname
// if aname now has an empty set of triggers, return true, marking it as reachable/eligible
let remove_trigger_for_assumption (p:pruning_state) (trig:sym) (aname:string)
: pruning_state & bool & list sym
= match PSMap.try_find p.assumption_to_triggers aname with
  | None ->
    // debug (fun _ -> Format.print2 "Removing trigger %s for assumption %s---no assumption found\n" trig aname);
    p, false, []
  | Some l -> 
    let l =
      { remaining_triggers = l.remaining_triggers |> List.map (fun ts -> remove trig.sym_name ts);
        already_triggered = trig :: l.already_triggered }
    in
    let eligible = BU.for_some is_empty l.remaining_triggers in
    // debug (fun _ ->
    //   Format.print5 "Removing trigger %s for assumption %s---eligible? %s, original triggers %s, remaining triggers %s\n"
    //     trig aname (show eligible) (show l) (show remaining_triggers));
    { p with assumption_to_triggers = PSMap.add p.assumption_to_triggers aname l },
    eligible,
    l.already_triggered

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
    { p with defs_and_decls=d::p.defs_and_decls; 
             defs_and_decls_map = PSMap.add p.defs_and_decls_map macro d;
             macro_freenames = PSMap.add p.macro_freenames macro free_names } 
  | DeclFun(name, _, _, _) ->
    { p with defs_and_decls = d::p.defs_and_decls;
             defs_and_decls_map = PSMap.add p.defs_and_decls_map name d }
  | _ -> p
    
let add_decls (ds:list decl) (p:pruning_state)
: pruning_state
= List.fold_left (fun p d -> add_decl d p) p ds

// An assumption that is to be retained;
// together with the reason why it was triggered
type triggered_assumption = {
  assumption : assumption;
  triggered_by : list sym
}

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
  return = (fun (#a:Type) (x:a) -> (fun s -> (x, s)) <: st a);
  bind   = (fun (#a #b:Type) (m:st a) (f:a -> st b) (s:ctxt) ->
                let (x, s) = m s in
                f x s)
}

// When a trigger as reached, mark it, removing it from the trigger map
let mark_trigger_reached (x:sym)
: st unit
= let! ctxt = get in
  put {ctxt with p=trigger_reached ctxt.p x.sym_name }

// All assumptions that are waiting on a trigger
let find_assumptions_waiting_on_trigger (x:sym)
: st (list assumption)
= let! ctxt = get in
  match PSMap.try_find ctxt.p.trigger_to_assumption x.sym_name with
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
: st (bool & list sym)
= let! ctxt = get in
  let p, eligible, already_triggered = remove_trigger_for_assumption ctxt.p trig a.assumption_name in
  put {ctxt with p} ;!
  return (eligible, already_triggered)

// Check if an assumption has already been reached 
let already_reached (aname:string)
: st bool
= let! ctxt = get in
  return (mem aname ctxt.reached)

// All assumptions that are now eligible given lids are reached
let trigger_pending_assumptions (lids:list sym)
: st (list triggered_assumption)
= foldM_left
    (fun acc lid ->
      match! find_assumptions_waiting_on_trigger lid with
      | [] -> return acc
      | assumptions ->
        // debug (fun _ -> Format.print2 "Found assumptions waiting on trigger %s: %s\n" lid (show <| List.map (fun a -> a.assumption_name) assumptions));
        mark_trigger_reached lid ;!
        foldM_left
          (fun acc assumption ->
            let! eligible, triggered_by = remove_trigger_for lid assumption in
            if eligible
            then return ({assumption; triggered_by}::acc)
            else return acc)
          acc
          assumptions)
  []
  lids

// The main scanning loop
let rec scan (ds:list assumption)
: st unit
= let! ctxt = get in
  let mk_sym assumption_name l = { sym_name = l; sym_provenance = assumption_name } in
  let macro_expand (s:sym) : list sym =
    match PSMap.try_find ctxt.p.macro_freenames s.sym_name with
    | None -> [s]
    | Some l -> s::List.map (mk_sym s.sym_provenance) l
  in
  // Collect the free names of all assumptions and macro expand them
  let new_syms = List.collect (fun a -> List.collect macro_expand (List.map (mk_sym a.assumption_name) <| elems (assumption_free_names a))) ds in

  // Trigger all assumptions that are waiting on the new symbols
  match! trigger_pending_assumptions new_syms with
  | [] ->
    // Done if no new assumptions are eligible
    return ()
  | triggered ->
    // Otherwise, mark them as reached, and scan them
    let! to_scan =
      foldM_left
        (fun acc triggered_assumption ->
          let assumption = triggered_assumption.assumption in
          if! already_reached assumption.assumption_name
          then return acc
          else if not (should_retain_assumption assumption)
          then return acc
          else (
            reached_assumption assumption.assumption_name ;!
            return <| assumption::acc
          ))
        []
        triggered
    in
    scan to_scan

let print_reached_names_and_reasons (ctxt:ctxt) names =
  let print_one name = 
    match PSMap.try_find ctxt.p.assumption_to_triggers name with
    | None -> Format.fmt1 "%s (included but not found in map)" name
    | Some l -> Format.fmt2 "%s {triggered by %s}" name (show l.already_triggered)
  in
  String.concat "\n\t" (List.map print_one names)

let name_of_decl (d:decl) =
  match d with
  | Assume a -> a.assumption_name
  | DeclFun(a, _, _, _) -> a
  | DefineFun(a, _, _, _, _) -> a
  | _ -> "<none>"

let prune (p:pruning_state) (roots0:list decl)
: list decl
= // Collect all assumptions from the roots
  let roots = List.collect assumptions_of_decl roots0 in
  let init = { p; reached = empty () } in
  // Scan to find all reachable assumptions
  let roots = 
    if no_ambients()
    then roots
    else roots@p.extra_roots
  in
  let mk_triggered_assumption assumption = {assumption; triggered_by=[]} in
  let _, ctxt = scan roots init in
  // Collect their names
  let reached_names = elems ctxt.reached in
  if no_ambients()
  then (
    debug (fun _ ->
      let _, ctxt' = scan (roots@p.extra_roots) init in
      let extra_reached : list string = elems <| FStarC.RBSet.diff ctxt'.reached ctxt.reached in
      Format.print4 "Debug context pruning: Excluded %s ambients resulted in pruning %s assumptions\nambients %s\npruned assumptions %s\n"
              (show (List.length p.pruned_ambients))
              (show (List.length extra_reached))
              (show p.pruned_ambients)
              (show extra_reached))
  );
  // Map them to assumptions, together with ambients
  let reached_assumptions =
    List.collect
      (fun name ->
        match PSMap.try_find ctxt.p.assumption_name_map name with
        | None -> []
        | Some a -> [a]) 
      (reached_names@p.ambients)
  in
  debug (fun _ ->
    Format.print2 "Debug context pruning: Retained %s assumptions\n%s\n" 
        (show (List.length reached_assumptions))
        (print_reached_names_and_reasons ctxt (reached_names@p.ambients))
  );
  let decls_and_defs =
    if not (Options.Ext.enabled "prune_decls")
    then []
    else (
      let _, defs_and_decls = 
        List.fold_left #(RBSet.t string & list decl)
          (fun (included_decl_names, defs_and_decls) a ->
            match a with
            | Assume a -> 
              let free_names = assumption_free_names a in
              List.fold_left
                (fun (included_decl_names, defs_and_decls) name ->
                  if RBSet.mem name included_decl_names
                  then included_decl_names, defs_and_decls
                  else (
                    match PSMap.try_find p.defs_and_decls_map name with
                    | None -> 
                      included_decl_names, defs_and_decls
                    | Some d -> 
                      RBSet.add name included_decl_names, d::defs_and_decls
                  ))
                (included_decl_names, defs_and_decls)
                (elems free_names)

            | _ -> included_decl_names, defs_and_decls)
        (RBSet.empty(), [])
        (reached_assumptions@roots0)
      in
      let decls, defs = List.partition DeclFun? defs_and_decls in
      defs@decls
    )
  in
  let print_assumption (a:assumption) =
    Format.fmt2 "{name=%s; freevars={%s}}"
      (show a.assumption_name)
      (show (assumption_free_names a))
  in
  debug (fun _ ->
    Format.print2 "Debug context pruning: roots %s, retained decls and defs %s\n"
      (show (List.map print_assumption roots))
      (show (List.map name_of_decl decls_and_defs)));
  reached_assumptions@decls_and_defs
