module FStar.SMTEncoding.Pruning
open FStar.Compiler.Effect
open FStar
open FStar.List.Tot
open FStar.Compiler
open FStar.SMTEncoding.Term
open FStar.Class.Setlike
open FStar.Class.Show
open FStar.Class.Monad
module BU = FStar.Compiler.Util
type triggers = list (list string)

type pruning_state = {
  assumptions: list assumption;
  macro_freenames: BU.psmap (list string);
  trigger_to_assumption: BU.psmap (list assumption);
  assumption_to_triggers: BU.psmap triggers;
  assumption_name_map: BU.psmap decl;
  ambients: list string; //assumptions with no triggers
}

let debug (f: unit -> unit) : unit =
  if Options.Ext.get "debug_context_pruning" <> ""
  then f()

let print_pruning_state (p:pruning_state)
: string
= let t_to_a =
    BU.psmap_fold
      p.trigger_to_assumption
      (fun k v (acc:list (string & int)) -> (k, List.length v) :: acc) //List.map (fun a -> a.assumption_name) v) :: acc)
      []
  in
  let t_to_a = BU.sort_with (fun x y -> snd x - snd y) t_to_a in
  let a_to_t =
    BU.psmap_fold
      p.assumption_to_triggers
      (fun k v acc ->
        BU.format2 "[%s -> %s]" 
            k
            (show v) :: acc)
      []
  in
  let macros =
    BU.psmap_fold
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

let init
: pruning_state 
= { assumptions = [];
    macro_freenames = BU.psmap_empty ();
    trigger_to_assumption = BU.psmap_empty ();
    assumption_to_triggers = BU.psmap_empty ();
    assumption_name_map = BU.psmap_empty ();
    ambients=[] }

let add_trigger_to_assumption (a:assumption) (p:pruning_state) (trig:string)
: pruning_state
= match BU.psmap_try_find p.trigger_to_assumption trig with
  | None -> { p with trigger_to_assumption = BU.psmap_add p.trigger_to_assumption trig [a] }
  | Some l -> { p with trigger_to_assumption = BU.psmap_add p.trigger_to_assumption trig (a::l) }

let triggers_of_term (t:term)
: triggers
= let rec aux (t:term) =
    match t.tm with
    | Quant(Forall, triggers, _, _, _) ->
      triggers |> List.map (fun disjunct ->
      disjunct |> List.collect (fun t -> elems (Term.free_top_level_names t)))
    | Labeled (t, _, _)
    | LblPos (t, _) -> aux t
    | _ -> []
  in aux t

let maybe_add_ambient (a:assumption) (p:pruning_state)
: pruning_state
= let aux triggers =
    let p = 
      { p with
        assumption_to_triggers=
        BU.psmap_add p.assumption_to_triggers a.assumption_name triggers}
    in
    List.fold_left (List.fold_left (add_trigger_to_assumption a)) p triggers
  in
  let add_ambient_assumption_with_empty_trigger t =
    //add it to the context with an empty trigger, so it is always available
    //and it contributes its free variables to trigger other assumptions 
    let triggers = [elems (Term.free_top_level_names t)] in
    aux ([]::triggers)
  in
  begin
    match a.assumption_term.tm with
    | App(Iff, [t0; t1]) when BU.starts_with a.assumption_name "l_quant_interp" -> (
      let triggers_lhs = elems (Term.free_top_level_names t0) in
      aux [triggers_lhs]
    )
    
    | _ when BU.starts_with a.assumption_name "assumption_" -> 
      add_ambient_assumption_with_empty_trigger a.assumption_term

    | App (Var "HasType", [term; ty]) -> ( //HasType term (squash ty) is an ambient that should trigger on either the term or the type
      match ty.tm with
      | App (Var "Prims.squash", [ty]) ->
        //top-level squashes are treated like assumption
        add_ambient_assumption_with_empty_trigger a.assumption_term

      | _ ->
        aux [elems (Term.free_top_level_names term)]
    )
 
    | App (Var "Valid", 
          [{tm=App (Var "ApplyTT", [{tm=FreeV (FV("__uu__PartialApp", _, _))}; term])}])
    | App (Var "Valid", 
          [{tm=App (Var "ApplyTT", [{tm=App(Var "__uu__PartialApp", _)}; term])}]) ->
      let triggers =
        match term.tm with
        | FreeV(FV(token, _, _))
        | App(Var token, []) ->
          if BU.ends_with token "@tok"
          then [[token]; [BU.substring token 0 (String.length token - 4)]]
          else [[token]]
        | _ -> 
          []
      in
      aux triggers
    | App (Var "Valid", [term])
    | App (Var "HasType", [term; _])
    | App (Var "IsTotFun", [term])
    | App (Var "is-Tm_arrow", [term]) ->
      aux [elems (Term.free_top_level_names term)]
    | App (Eq, [ _; {tm=App (Var "Term_constr_id", [term])}]) ->
      aux [elems (Term.free_top_level_names term)]
    | App (And, tms) ->
    // | App (And, ({tm=App (Var "IsTotFun", [term])}::tms)) ->
    //   let t0 = elems (Term.free_top_level_names term) in
      let t1 = List.collect triggers_of_term tms in
      aux t1
    | App (Iff, [t0; t1])
    | App (Eq, [t0; t1]) ->
      let t0 = elems (Term.free_top_level_names t0) in
      let t1 = elems (Term.free_top_level_names t1) in
      aux [t0; t1]
    | App (TrueOp, _) -> p
    | _ ->
      { p with ambients = a.assumption_name::p.ambients }
  end

let add_assumption_to_triggers (a:assumption) (p:pruning_state) (trigs:triggers)
: pruning_state
= let p = { p with assumption_name_map = BU.psmap_add p.assumption_name_map a.assumption_name (Assume a) } in
  match trigs with
  | [] -> 
    maybe_add_ambient a p
  | _ ->
    { p with assumption_to_triggers = BU.psmap_add p.assumption_to_triggers a.assumption_name trigs }


let trigger_reached (p:pruning_state) (trig:string)
: pruning_state
= { p with trigger_to_assumption = BU.psmap_remove p.trigger_to_assumption trig }

let remove_trigger_for_assumption (p:pruning_state) (trig:string) (aname:string)
: pruning_state & bool
= 
  match BU.psmap_try_find p.assumption_to_triggers aname with
  | None ->
    debug (fun _ -> BU.print2 "Removing trigger %s for assumption %s---no assumption found\n" trig aname);
    p, false
  | Some l -> 
    let remaining_triggers =
      l |> List.map (fun disjunct ->
      disjunct |> List.filter (fun x -> x <> trig))
    in
    let eligible = BU.for_some Nil? remaining_triggers in
    debug (fun _ ->
      BU.print5 "Removing trigger %s for assumption %s---eligible? %s, original triggers %s, remaining triggers %s\n"
        trig aname (show eligible) (show l) (show remaining_triggers));
    { p with assumption_to_triggers = BU.psmap_add p.assumption_to_triggers aname remaining_triggers },
    eligible

let rec assumptions_of_decl (d:decl)
: list assumption
= match d with
  | Assume a -> [a]
  | Module (_, ds) -> List.collect assumptions_of_decl ds
  | d -> []

let rec add_decl (d:decl) (p:pruning_state)
: pruning_state
= match d with
  | Assume a ->
    let p = { p with assumptions = a::p.assumptions } in
    let triggers = triggers_of_term a.assumption_term in
    let p = List.fold_left (List.fold_left (add_trigger_to_assumption a)) p triggers in
    add_assumption_to_triggers a p triggers
  | Module (_, ds) -> List.fold_left (fun p d -> add_decl d p) p ds
  | DefineFun(macro, _, _, body, _) ->
    let free_names = elems (Term.free_top_level_names body) in
    let p = { p with macro_freenames = BU.psmap_add p.macro_freenames macro free_names } in
    p
  | _ -> p
    
let add_decls (ds:list decl) (p:pruning_state)
: pruning_state
= List.fold_left (fun p d -> add_decl d p) p ds

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
: st (list assumption)
= foldM_left
    (fun acc lid ->
      match! find_assumptions_waiting_on_trigger lid with
      | [] -> return acc
      | assumptions ->
        debug (fun _ -> BU.print2 "Found assumptions waiting on trigger %s: %s\n" lid (show <| List.map (fun a -> a.assumption_name) assumptions));
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
        return <| eligible_assumptions @ acc)
  []
  lids

let rec scan (ds:list assumption)
: st unit
= let! ctxt = get in
  let macro_expand (s:sym) : list sym =
    match BU.psmap_try_find ctxt.p.macro_freenames s with
    | None -> [s]
    | Some l -> s::l
  in
  let new_syms = List.collect (fun a -> List.collect macro_expand a.assumption_free_names) ds in
  debug (fun _ -> 
    BU.print1 ">>>Scanning %s\n"
      (ds |> List.map (fun a -> BU.format2 "%s -> [%s]" a.assumption_name (a.assumption_free_names |> show)) |> String.concat "\n\t"));

  // BU.print2 "Scanning %s; got terms %s\n" (show <| List.map (fun a -> a.assumption_name) ds) (show new_syms);
  match! trigger_pending_assumptions new_syms with
  | [] -> return ()
  | triggered ->
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
= debug (fun _ -> BU.print_string (show p));
  let roots = List.collect assumptions_of_decl roots in
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
  debug (fun _ ->
  BU.print2
    "Pruning:\n\tTotal assumptions %s\n\tRetained %s\n"
    (List.length p.assumptions |> show)
    (List.length reached_assumptions |> show));
  reached_assumptions