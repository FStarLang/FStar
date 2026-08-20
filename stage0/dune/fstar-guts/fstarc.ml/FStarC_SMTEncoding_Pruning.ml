open Prims
type triggers = Prims.string Prims.list Prims.list
type asum_kind =
  | Sum_triggers of triggers 
  | Sum_ambient of Prims.bool 
  | Sum_drop 
let uu___is_Sum_triggers (projectee : asum_kind) : Prims.bool=
  match projectee with | Sum_triggers _0 -> true | uu___ -> false
let __proj__Sum_triggers__item___0 (projectee : asum_kind) : triggers=
  match projectee with | Sum_triggers _0 -> _0
let uu___is_Sum_ambient (projectee : asum_kind) : Prims.bool=
  match projectee with | Sum_ambient _0 -> true | uu___ -> false
let __proj__Sum_ambient__item___0 (projectee : asum_kind) : Prims.bool=
  match projectee with | Sum_ambient _0 -> _0
let uu___is_Sum_drop (projectee : asum_kind) : Prims.bool=
  match projectee with | Sum_drop -> true | uu___ -> false
type assumption_summary =
  {
  asum_name: Prims.string ;
  asum_free_names: Prims.string Prims.list ;
  asum_pretyping: Prims.bool ;
  asum_kind: asum_kind }
let __proj__Mkassumption_summary__item__asum_name
  (projectee : assumption_summary) : Prims.string=
  match projectee with
  | { asum_name; asum_free_names; asum_pretyping; asum_kind = asum_kind1;_}
      -> asum_name
let __proj__Mkassumption_summary__item__asum_free_names
  (projectee : assumption_summary) : Prims.string Prims.list=
  match projectee with
  | { asum_name; asum_free_names; asum_pretyping; asum_kind = asum_kind1;_}
      -> asum_free_names
let __proj__Mkassumption_summary__item__asum_pretyping
  (projectee : assumption_summary) : Prims.bool=
  match projectee with
  | { asum_name; asum_free_names; asum_pretyping; asum_kind = asum_kind1;_}
      -> asum_pretyping
let __proj__Mkassumption_summary__item__asum_kind
  (projectee : assumption_summary) : asum_kind=
  match projectee with
  | { asum_name; asum_free_names; asum_pretyping; asum_kind = asum_kind1;_}
      -> asum_kind1
type decl_summary =
  | Sum_assume of assumption_summary 
  | Sum_declfun of Prims.string 
  | Sum_definefun of (Prims.string * Prims.string Prims.list) 
  | Sum_retain of Prims.string Prims.list 
  | Sum_ignored 
  | Sum_other of FStarC_SMTEncoding_Term.decl 
let uu___is_Sum_assume (projectee : decl_summary) : Prims.bool=
  match projectee with | Sum_assume _0 -> true | uu___ -> false
let __proj__Sum_assume__item___0 (projectee : decl_summary) :
  assumption_summary= match projectee with | Sum_assume _0 -> _0
let uu___is_Sum_declfun (projectee : decl_summary) : Prims.bool=
  match projectee with | Sum_declfun _0 -> true | uu___ -> false
let __proj__Sum_declfun__item___0 (projectee : decl_summary) : Prims.string=
  match projectee with | Sum_declfun _0 -> _0
let uu___is_Sum_definefun (projectee : decl_summary) : Prims.bool=
  match projectee with | Sum_definefun _0 -> true | uu___ -> false
let __proj__Sum_definefun__item___0 (projectee : decl_summary) :
  (Prims.string * Prims.string Prims.list)=
  match projectee with | Sum_definefun _0 -> _0
let uu___is_Sum_retain (projectee : decl_summary) : Prims.bool=
  match projectee with | Sum_retain _0 -> true | uu___ -> false
let __proj__Sum_retain__item___0 (projectee : decl_summary) :
  Prims.string Prims.list= match projectee with | Sum_retain _0 -> _0
let uu___is_Sum_ignored (projectee : decl_summary) : Prims.bool=
  match projectee with | Sum_ignored -> true | uu___ -> false
let uu___is_Sum_other (projectee : decl_summary) : Prims.bool=
  match projectee with | Sum_other _0 -> true | uu___ -> false
let __proj__Sum_other__item___0 (projectee : decl_summary) :
  FStarC_SMTEncoding_Term.decl= match projectee with | Sum_other _0 -> _0
type triggers_set = Prims.string FStarC_RBSet.t Prims.list
let showable_psmap (uu___ : 'a FStarC_Class_Show.showable) :
  'a FStarC_PSMap.t FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun s ->
         let uu___1 =
           FStarC_PSMap.fold s
             (fun key value out ->
                let uu___2 =
                  let uu___3 = FStarC_Class_Show.show uu___ value in
                  FStarC_Format.fmt2 "(%s -> %s)" key uu___3 in
                uu___2 :: out) [] in
         FStarC_Class_Show.show
           (FStarC_Class_Show.show_list FStarC_Class_Show.showable_string)
           uu___1)
  }
let triggers_as_triggers_set (ts : triggers) : triggers_set=
  FStarC_List.map
    (FStarC_Class_Setlike.from_list
       (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string)) ts
type assumption_name = Prims.string
type sym = {
  sym_name: Prims.string ;
  sym_provenance: assumption_name }
let __proj__Mksym__item__sym_name (projectee : sym) : Prims.string=
  match projectee with | { sym_name; sym_provenance;_} -> sym_name
let __proj__Mksym__item__sym_provenance (projectee : sym) : assumption_name=
  match projectee with | { sym_name; sym_provenance;_} -> sym_provenance
let showable_sym : sym FStarC_Class_Show.showable=
  {
    FStarC_Class_Show.show =
      (fun s -> FStarC_Format.fmt2 "%s {from %s}" s.sym_name s.sym_provenance)
  }
type assumption_remaining_triggers =
  {
  remaining_triggers: triggers_set ;
  already_triggered: sym Prims.list }
let __proj__Mkassumption_remaining_triggers__item__remaining_triggers
  (projectee : assumption_remaining_triggers) : triggers_set=
  match projectee with
  | { remaining_triggers; already_triggered;_} -> remaining_triggers
let __proj__Mkassumption_remaining_triggers__item__already_triggered
  (projectee : assumption_remaining_triggers) : sym Prims.list=
  match projectee with
  | { remaining_triggers; already_triggered;_} -> already_triggered
let mk_remaining_triggers (ts : triggers_set) :
  assumption_remaining_triggers=
  { remaining_triggers = ts; already_triggered = [] }
let no_ambients (uu___ : unit) : Prims.bool=
  FStarC_Options_Ext.enabled "context_pruning_no_ambients"
type passumption =
  {
  pa_name: Prims.string ;
  pa_free_names: Prims.string FStarC_RBSet.t ;
  pa_pretyping: Prims.bool ;
  pa_resolve:
    unit -> FStarC_SMTEncoding_Term.decl FStar_Pervasives_Native.option }
let __proj__Mkpassumption__item__pa_name (projectee : passumption) :
  Prims.string=
  match projectee with
  | { pa_name; pa_free_names; pa_pretyping; pa_resolve;_} -> pa_name
let __proj__Mkpassumption__item__pa_free_names (projectee : passumption) :
  Prims.string FStarC_RBSet.t=
  match projectee with
  | { pa_name; pa_free_names; pa_pretyping; pa_resolve;_} -> pa_free_names
let __proj__Mkpassumption__item__pa_pretyping (projectee : passumption) :
  Prims.bool=
  match projectee with
  | { pa_name; pa_free_names; pa_pretyping; pa_resolve;_} -> pa_pretyping
let __proj__Mkpassumption__item__pa_resolve (projectee : passumption) :
  unit -> FStarC_SMTEncoding_Term.decl FStar_Pervasives_Native.option=
  match projectee with
  | { pa_name; pa_free_names; pa_pretyping; pa_resolve;_} -> pa_resolve
type pdef =
  {
  pd_is_declfun: Prims.bool ;
  pd_resolve:
    unit -> FStarC_SMTEncoding_Term.decl FStar_Pervasives_Native.option }
let __proj__Mkpdef__item__pd_is_declfun (projectee : pdef) : Prims.bool=
  match projectee with | { pd_is_declfun; pd_resolve;_} -> pd_is_declfun
let __proj__Mkpdef__item__pd_resolve (projectee : pdef) :
  unit -> FStarC_SMTEncoding_Term.decl FStar_Pervasives_Native.option=
  match projectee with | { pd_is_declfun; pd_resolve;_} -> pd_resolve
let should_retain_assumption (a : passumption) : Prims.bool=
  if a.pa_pretyping
  then FStarC_Options_Ext.enabled "pretyping_axioms"
  else true
type pruning_state =
  {
  defs_and_decls_map: pdef FStarC_PSMap.t ;
  macro_freenames: Prims.string Prims.list FStarC_PSMap.t ;
  trigger_to_assumption: passumption Prims.list FStarC_PSMap.t ;
  assumption_to_triggers: assumption_remaining_triggers FStarC_PSMap.t ;
  assumption_name_map: passumption FStarC_PSMap.t ;
  ambients: Prims.string Prims.list ;
  extra_roots: passumption Prims.list ;
  pruned_ambients: Prims.string Prims.list }
let __proj__Mkpruning_state__item__defs_and_decls_map
  (projectee : pruning_state) : pdef FStarC_PSMap.t=
  match projectee with
  | { defs_and_decls_map; macro_freenames; trigger_to_assumption;
      assumption_to_triggers; assumption_name_map; ambients; extra_roots;
      pruned_ambients;_} -> defs_and_decls_map
let __proj__Mkpruning_state__item__macro_freenames
  (projectee : pruning_state) : Prims.string Prims.list FStarC_PSMap.t=
  match projectee with
  | { defs_and_decls_map; macro_freenames; trigger_to_assumption;
      assumption_to_triggers; assumption_name_map; ambients; extra_roots;
      pruned_ambients;_} -> macro_freenames
let __proj__Mkpruning_state__item__trigger_to_assumption
  (projectee : pruning_state) : passumption Prims.list FStarC_PSMap.t=
  match projectee with
  | { defs_and_decls_map; macro_freenames; trigger_to_assumption;
      assumption_to_triggers; assumption_name_map; ambients; extra_roots;
      pruned_ambients;_} -> trigger_to_assumption
let __proj__Mkpruning_state__item__assumption_to_triggers
  (projectee : pruning_state) : assumption_remaining_triggers FStarC_PSMap.t=
  match projectee with
  | { defs_and_decls_map; macro_freenames; trigger_to_assumption;
      assumption_to_triggers; assumption_name_map; ambients; extra_roots;
      pruned_ambients;_} -> assumption_to_triggers
let __proj__Mkpruning_state__item__assumption_name_map
  (projectee : pruning_state) : passumption FStarC_PSMap.t=
  match projectee with
  | { defs_and_decls_map; macro_freenames; trigger_to_assumption;
      assumption_to_triggers; assumption_name_map; ambients; extra_roots;
      pruned_ambients;_} -> assumption_name_map
let __proj__Mkpruning_state__item__ambients (projectee : pruning_state) :
  Prims.string Prims.list=
  match projectee with
  | { defs_and_decls_map; macro_freenames; trigger_to_assumption;
      assumption_to_triggers; assumption_name_map; ambients; extra_roots;
      pruned_ambients;_} -> ambients
let __proj__Mkpruning_state__item__extra_roots (projectee : pruning_state) :
  passumption Prims.list=
  match projectee with
  | { defs_and_decls_map; macro_freenames; trigger_to_assumption;
      assumption_to_triggers; assumption_name_map; ambients; extra_roots;
      pruned_ambients;_} -> extra_roots
let __proj__Mkpruning_state__item__pruned_ambients
  (projectee : pruning_state) : Prims.string Prims.list=
  match projectee with
  | { defs_and_decls_map; macro_freenames; trigger_to_assumption;
      assumption_to_triggers; assumption_name_map; ambients; extra_roots;
      pruned_ambients;_} -> pruned_ambients
let debug (f : unit -> unit) : unit=
  let uu___ = FStarC_Options_Ext.enabled "debug_context_pruning" in
  if uu___ then f () else ()
let print_pruning_state (p : pruning_state) : Prims.string=
  let t_to_a =
    FStarC_PSMap.fold p.trigger_to_assumption
      (fun k v acc -> (k, (FStarC_List.length v)) :: acc) [] in
  let t_to_a1 =
    FStarC_Util.sort_with
      (fun x y ->
         (FStar_Pervasives_Native.snd x) - (FStar_Pervasives_Native.snd y))
      t_to_a in
  let a_to_t =
    FStarC_PSMap.fold p.assumption_to_triggers
      (fun k v acc ->
         let uu___ =
           let uu___1 =
             FStarC_Class_Show.show
               (FStarC_Class_Show.show_list
                  (FStarC_RBSet.showable_rbset
                     FStarC_Class_Show.showable_string)) v.remaining_triggers in
           FStarC_Format.fmt2 "[%s -> %s]" k uu___1 in
         uu___ :: acc) [] in
  let macros =
    FStarC_PSMap.fold p.macro_freenames
      (fun k v acc ->
         let uu___ =
           let uu___1 =
             FStarC_Class_Show.show
               (FStarC_Class_Show.show_list FStarC_Class_Show.showable_string)
               v in
           FStarC_Format.fmt2 "[%s -> %s]" k uu___1 in
         uu___ :: acc) [] in
  let uu___ =
    let uu___1 =
      FStarC_List.map
        (FStarC_Class_Show.show
           (FStarC_Class_Show.show_tuple2 FStarC_Class_Show.showable_string
              FStarC_Class_Show.showable_int)) t_to_a1 in
    FStarC_String.concat "\n\t" uu___1 in
  FStarC_Format.fmt3
    "Pruning state:\n\tTriggers to assumptions:\n\t%s\nAssumptions to triggers:\n\t%s\nMacros:\n\t%s\n"
    uu___ (FStarC_String.concat "\n\t" a_to_t)
    (FStarC_String.concat "\n\t" macros)
let show_pruning_state : pruning_state FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = print_pruning_state }
let init_macro_freenames : Prims.string Prims.list FStarC_PSMap.t=
  FStarC_PSMap.of_list
    [("is-BoxBool", ["BoxBool"]);
    ("is-BoxInt", ["BoxInt"]);
    ("is-BoxString", ["BoxString"]);
    ("is-BoxReal", ["BoxReal"])]
let init : pruning_state=
  {
    defs_and_decls_map = (FStarC_PSMap.empty ());
    macro_freenames = init_macro_freenames;
    trigger_to_assumption = (FStarC_PSMap.empty ());
    assumption_to_triggers = (FStarC_PSMap.empty ());
    assumption_name_map = (FStarC_PSMap.empty ());
    ambients = [];
    extra_roots = [];
    pruned_ambients = []
  }
type elt_summary =
  {
  elts_key: Prims.string FStar_Pervasives_Native.option ;
  elts_a_names: Prims.string Prims.list ;
  elts_sums: decl_summary Prims.list }
let __proj__Mkelt_summary__item__elts_key (projectee : elt_summary) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with | { elts_key; elts_a_names; elts_sums;_} -> elts_key
let __proj__Mkelt_summary__item__elts_a_names (projectee : elt_summary) :
  Prims.string Prims.list=
  match projectee with
  | { elts_key; elts_a_names; elts_sums;_} -> elts_a_names
let __proj__Mkelt_summary__item__elts_sums (projectee : elt_summary) :
  decl_summary Prims.list=
  match projectee with | { elts_key; elts_a_names; elts_sums;_} -> elts_sums
let add_trigger_to_assumption (a : passumption) (p : pruning_state)
  (trig : Prims.string) : pruning_state=
  match FStarC_PSMap.try_find p.trigger_to_assumption trig with
  | FStar_Pervasives_Native.None ->
      {
        defs_and_decls_map = (p.defs_and_decls_map);
        macro_freenames = (p.macro_freenames);
        trigger_to_assumption =
          (FStarC_PSMap.add p.trigger_to_assumption trig [a]);
        assumption_to_triggers = (p.assumption_to_triggers);
        assumption_name_map = (p.assumption_name_map);
        ambients = (p.ambients);
        extra_roots = (p.extra_roots);
        pruned_ambients = (p.pruned_ambients)
      }
  | FStar_Pervasives_Native.Some l ->
      {
        defs_and_decls_map = (p.defs_and_decls_map);
        macro_freenames = (p.macro_freenames);
        trigger_to_assumption =
          (FStarC_PSMap.add p.trigger_to_assumption trig (a :: l));
        assumption_to_triggers = (p.assumption_to_triggers);
        assumption_name_map = (p.assumption_name_map);
        ambients = (p.ambients);
        extra_roots = (p.extra_roots);
        pruned_ambients = (p.pruned_ambients)
      }
let exclude_names : Prims.string FStarC_RBSet.t=
  FStarC_Class_Setlike.from_list
    (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string)
    ["SFuel";
    "ZFuel";
    "HasType";
    "HasTypeZ";
    "HasTypeFuel";
    "Valid";
    "ApplyTT";
    "ApplyTF";
    "Prims.lex_t"]
let free_top_level_names (t : FStarC_SMTEncoding_Term.term) :
  Prims.string FStarC_RBSet.t=
  let uu___ = FStarC_SMTEncoding_Term.free_top_level_names t in
  FStarC_Class_Setlike.diff
    (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string) uu___
    exclude_names
let assumption_free_names (a : FStarC_SMTEncoding_Term.assumption) :
  Prims.string FStarC_RBSet.t=
  free_top_level_names a.FStarC_SMTEncoding_Term.assumption_term
let triggers_of_term (t : FStarC_SMTEncoding_Term.term) : triggers_set=
  let rec aux t1 =
    match t1 with
    | FStarC_SMTEncoding_Term.Quant
        (FStarC_SMTEncoding_Term.Forall, triggers1, uu___, uu___1, uu___2,
         uu___3)
        ->
        FStarC_List.map
          (fun disjunct ->
             let uu___4 =
               FStarC_Class_Setlike.empty
                 (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string) () in
             FStarC_List.fold_left
               (fun out t2 ->
                  let uu___5 = free_top_level_names t2 in
                  FStarC_Class_Setlike.union
                    (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string)
                    out uu___5) uu___4 disjunct) triggers1
    | FStarC_SMTEncoding_Term.Labeled (t2, uu___, uu___1) -> aux t2
    | uu___ -> [] in
  aux t
let maybe_add_ambient (a : FStarC_SMTEncoding_Term.assumption) : asum_kind=
  let add_assumption_with_triggers triggers1 =
    let uu___ =
      FStarC_List.map
        (FStarC_Class_Setlike.elems
           (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string))
        triggers1 in
    Sum_triggers uu___ in
  let is_empty triggers1 =
    match triggers1 with
    | [] -> true
    | t::[] ->
        FStarC_Class_Setlike.is_empty
          (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string) t
    | uu___ -> false in
  let is_ambient_refinement ty =
    match ty with
    | FStarC_SMTEncoding_Term.App
        (FStarC_SMTEncoding_Term.Var "Prims.squash", uu___, uu___1) -> true
    | FStarC_SMTEncoding_Term.App
        (FStarC_SMTEncoding_Term.Var name, uu___, uu___1) ->
        FStarC_Util.starts_with name "Tm_refine_"
    | FStarC_SMTEncoding_Term.FreeV (FStarC_SMTEncoding_Term.FV
        (name, uu___, uu___1)) -> FStarC_Util.starts_with name "Tm_refine_"
    | uu___ -> false in
  let ambient_refinement_payload ty =
    match ty with
    | FStarC_SMTEncoding_Term.App
        (FStarC_SMTEncoding_Term.Var "Prims.squash", uu___::t::[], uu___1) ->
        t
    | uu___ -> ty in
  match a.FStarC_SMTEncoding_Term.assumption_term with
  | FStarC_SMTEncoding_Term.App
      (FStarC_SMTEncoding_Term.Iff, t0::t1::[], uu___) when
      FStarC_Util.starts_with a.FStarC_SMTEncoding_Term.assumption_name
        "l_quant_interp"
      ->
      let triggers_lhs = free_top_level_names t0 in
      add_assumption_with_triggers [triggers_lhs]
  | uu___ when
      FStarC_Util.starts_with a.FStarC_SMTEncoding_Term.assumption_name
        "assumption_"
      ->
      let triggers1 =
        triggers_of_term a.FStarC_SMTEncoding_Term.assumption_term in
      let uu___1 = is_empty triggers1 in
      if uu___1
      then
        let triggers2 =
          let uu___2 =
            free_top_level_names a.FStarC_SMTEncoding_Term.assumption_term in
          [uu___2] in
        add_assumption_with_triggers triggers2
      else add_assumption_with_triggers triggers1
  | FStarC_SMTEncoding_Term.App
      (FStarC_SMTEncoding_Term.Var "HasType", term::ty::[], uu___) when
      is_ambient_refinement ty ->
      let triggers1 = triggers_of_term (ambient_refinement_payload ty) in
      let uu___1 = is_empty triggers1 in
      if uu___1
      then Sum_ambient true
      else add_assumption_with_triggers triggers1
  | FStarC_SMTEncoding_Term.App
      (FStarC_SMTEncoding_Term.Var "Valid", (FStarC_SMTEncoding_Term.App
       (FStarC_SMTEncoding_Term.Var "ApplyTT", (FStarC_SMTEncoding_Term.FreeV
        (FStarC_SMTEncoding_Term.FV
        ("__uu__PartialApp", uu___, uu___1)))::term::[], uu___2))::[],
       uu___3)
      ->
      let triggers1 =
        match term with
        | FStarC_SMTEncoding_Term.FreeV (FStarC_SMTEncoding_Term.FV
            (token, uu___4, uu___5)) ->
            if FStarC_Util.ends_with token "@tok"
            then
              let uu___6 =
                FStarC_Class_Setlike.singleton
                  (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string)
                  token in
              let uu___7 =
                let uu___8 =
                  let uu___9 =
                    FStarC_Util.substring token Prims.int_zero
                      ((FStarC_String.length token) - (Prims.of_int 4)) in
                  FStarC_Class_Setlike.singleton
                    (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string)
                    uu___9 in
                [uu___8] in
              uu___6 :: uu___7
            else
              (let uu___6 =
                 FStarC_Class_Setlike.singleton
                   (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string)
                   token in
               [uu___6])
        | FStarC_SMTEncoding_Term.App
            (FStarC_SMTEncoding_Term.Var token, [], uu___4) ->
            if FStarC_Util.ends_with token "@tok"
            then
              let uu___5 =
                FStarC_Class_Setlike.singleton
                  (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string)
                  token in
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    FStarC_Util.substring token Prims.int_zero
                      ((FStarC_String.length token) - (Prims.of_int 4)) in
                  FStarC_Class_Setlike.singleton
                    (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string)
                    uu___8 in
                [uu___7] in
              uu___5 :: uu___6
            else
              (let uu___5 =
                 FStarC_Class_Setlike.singleton
                   (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string)
                   token in
               [uu___5])
        | uu___4 -> [] in
      add_assumption_with_triggers triggers1
  | FStarC_SMTEncoding_Term.App
      (FStarC_SMTEncoding_Term.Var "Valid", (FStarC_SMTEncoding_Term.App
       (FStarC_SMTEncoding_Term.Var "ApplyTT", (FStarC_SMTEncoding_Term.App
        (FStarC_SMTEncoding_Term.Var "__uu__PartialApp", uu___, uu___1))::term::[],
        uu___2))::[],
       uu___3)
      ->
      let triggers1 =
        match term with
        | FStarC_SMTEncoding_Term.FreeV (FStarC_SMTEncoding_Term.FV
            (token, uu___4, uu___5)) ->
            if FStarC_Util.ends_with token "@tok"
            then
              let uu___6 =
                FStarC_Class_Setlike.singleton
                  (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string)
                  token in
              let uu___7 =
                let uu___8 =
                  let uu___9 =
                    FStarC_Util.substring token Prims.int_zero
                      ((FStarC_String.length token) - (Prims.of_int 4)) in
                  FStarC_Class_Setlike.singleton
                    (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string)
                    uu___9 in
                [uu___8] in
              uu___6 :: uu___7
            else
              (let uu___6 =
                 FStarC_Class_Setlike.singleton
                   (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string)
                   token in
               [uu___6])
        | FStarC_SMTEncoding_Term.App
            (FStarC_SMTEncoding_Term.Var token, [], uu___4) ->
            if FStarC_Util.ends_with token "@tok"
            then
              let uu___5 =
                FStarC_Class_Setlike.singleton
                  (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string)
                  token in
              let uu___6 =
                let uu___7 =
                  let uu___8 =
                    FStarC_Util.substring token Prims.int_zero
                      ((FStarC_String.length token) - (Prims.of_int 4)) in
                  FStarC_Class_Setlike.singleton
                    (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string)
                    uu___8 in
                [uu___7] in
              uu___5 :: uu___6
            else
              (let uu___5 =
                 FStarC_Class_Setlike.singleton
                   (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string)
                   token in
               [uu___5])
        | uu___4 -> [] in
      add_assumption_with_triggers triggers1
  | FStarC_SMTEncoding_Term.App
      (FStarC_SMTEncoding_Term.Var "Valid", term::[], uu___) ->
      let uu___1 = let uu___2 = free_top_level_names term in [uu___2] in
      add_assumption_with_triggers uu___1
  | FStarC_SMTEncoding_Term.App
      (FStarC_SMTEncoding_Term.Var "HasType", term::uu___::[], uu___1) ->
      let uu___2 = let uu___3 = free_top_level_names term in [uu___3] in
      add_assumption_with_triggers uu___2
  | FStarC_SMTEncoding_Term.App
      (FStarC_SMTEncoding_Term.Var "IsTotFun", term::[], uu___) ->
      let uu___1 = let uu___2 = free_top_level_names term in [uu___2] in
      add_assumption_with_triggers uu___1
  | FStarC_SMTEncoding_Term.App
      (FStarC_SMTEncoding_Term.Var "is-Tm_arrow", term::[], uu___) ->
      let uu___1 = let uu___2 = free_top_level_names term in [uu___2] in
      add_assumption_with_triggers uu___1
  | FStarC_SMTEncoding_Term.App
      (FStarC_SMTEncoding_Term.Eq, uu___::(FStarC_SMTEncoding_Term.App
       (FStarC_SMTEncoding_Term.Var "Term_constr_id", term::[], uu___1))::[],
       uu___2)
      ->
      let uu___3 = let uu___4 = free_top_level_names term in [uu___4] in
      add_assumption_with_triggers uu___3
  | FStarC_SMTEncoding_Term.App (FStarC_SMTEncoding_Term.And, tms, uu___) ->
      let t1 = FStarC_List.collect triggers_of_term tms in
      add_assumption_with_triggers t1
  | FStarC_SMTEncoding_Term.App
      (FStarC_SMTEncoding_Term.Eq, t0::t1::[], uu___) when
      FStarC_Util.starts_with a.FStarC_SMTEncoding_Term.assumption_name
        "equation_"
      ->
      let t01 = free_top_level_names t0 in add_assumption_with_triggers [t01]
  | FStarC_SMTEncoding_Term.App
      (FStarC_SMTEncoding_Term.Iff, t0::t1::[], uu___) ->
      (match (t0, t1) with
       | (FStarC_SMTEncoding_Term.App
          (FStarC_SMTEncoding_Term.Var "Valid", (FStarC_SMTEncoding_Term.App
           (FStarC_SMTEncoding_Term.Var "Prims.hasEq", _u::lhs::[], uu___1))::[],
           uu___2),
          FStarC_SMTEncoding_Term.App
          (FStarC_SMTEncoding_Term.Var "Valid", (FStarC_SMTEncoding_Term.App
           (FStarC_SMTEncoding_Term.Var "Prims.hasEq", _v::rhs::[], uu___3))::[],
           uu___4)) ->
           let triggers1 = free_top_level_names lhs in
           add_assumption_with_triggers [triggers1]
       | uu___1 ->
           let t01 = free_top_level_names t0 in
           let t11 = free_top_level_names t1 in
           add_assumption_with_triggers [t01; t11])
  | FStarC_SMTEncoding_Term.App
      (FStarC_SMTEncoding_Term.Eq, t0::t1::[], uu___) ->
      let t01 = free_top_level_names t0 in
      let t11 = free_top_level_names t1 in
      add_assumption_with_triggers [t01; t11]
  | FStarC_SMTEncoding_Term.App
      (FStarC_SMTEncoding_Term.TrueOp, uu___, uu___1) -> Sum_drop
  | uu___ -> Sum_ambient false
let summarize_assumption (a : FStarC_SMTEncoding_Term.assumption) :
  assumption_summary=
  let kind =
    let uu___ = triggers_of_term a.FStarC_SMTEncoding_Term.assumption_term in
    match uu___ with
    | [] -> maybe_add_ambient a
    | ts ->
        let uu___1 =
          FStarC_List.map
            (FStarC_Class_Setlike.elems
               (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string)) ts in
        Sum_triggers uu___1 in
  let uu___ =
    let uu___1 = assumption_free_names a in
    FStarC_Class_Setlike.elems
      (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string) uu___1 in
  {
    asum_name = (a.FStarC_SMTEncoding_Term.assumption_name);
    asum_free_names = uu___;
    asum_pretyping =
      (a.FStarC_SMTEncoding_Term.assumption_caption =
         (FStar_Pervasives_Native.Some "pretyping"));
    asum_kind = kind
  }
let rec summarize_decl (d : FStarC_SMTEncoding_Term.decl) :
  decl_summary Prims.list=
  match d with
  | FStarC_SMTEncoding_Term.Assume a ->
      let uu___ = let uu___1 = summarize_assumption a in Sum_assume uu___1 in
      [uu___]
  | FStarC_SMTEncoding_Term.Module (uu___, ds) ->
      FStarC_List.collect summarize_decl ds
  | FStarC_SMTEncoding_Term.DefineFun (macro, uu___, uu___1, body, uu___2) ->
      let uu___3 =
        let uu___4 =
          let uu___5 =
            let uu___6 = free_top_level_names body in
            FStarC_Class_Setlike.elems
              (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string) uu___6 in
          (macro, uu___5) in
        Sum_definefun uu___4 in
      [uu___3]
  | FStarC_SMTEncoding_Term.DeclFun (name, uu___, uu___1, uu___2) ->
      [Sum_declfun name]
  | FStarC_SMTEncoding_Term.RetainAssumptions names -> [Sum_retain names]
  | FStarC_SMTEncoding_Term.Caption uu___ -> [Sum_ignored]
  | FStarC_SMTEncoding_Term.EmptyLine -> [Sum_ignored]
  | uu___ -> [Sum_other d]
let summarize_decls (ds : FStarC_SMTEncoding_Term.decl Prims.list) :
  decl_summary Prims.list= FStarC_List.collect summarize_decl ds
let summarize_elts (ds : FStarC_SMTEncoding_Term.decls_t) :
  elt_summary Prims.list=
  FStarC_List.map
    (fun elt ->
       let uu___ = summarize_decls elt.FStarC_SMTEncoding_Term.decls in
       {
         elts_key = (elt.FStarC_SMTEncoding_Term.key);
         elts_a_names = (elt.FStarC_SMTEncoding_Term.a_names);
         elts_sums = uu___
       }) ds
let add_assumption_summary (asum : assumption_summary)
  (resolve :
    Prims.string ->
      FStarC_SMTEncoding_Term.decl FStar_Pervasives_Native.option)
  (p : pruning_state) : pruning_state=
  let a =
    let uu___ =
      FStarC_Class_Setlike.from_list
        (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string)
        asum.asum_free_names in
    {
      pa_name = (asum.asum_name);
      pa_free_names = uu___;
      pa_pretyping = (asum.asum_pretyping);
      pa_resolve = (fun uu___1 -> resolve asum.asum_name)
    } in
  let p1 =
    {
      defs_and_decls_map = (p.defs_and_decls_map);
      macro_freenames = (p.macro_freenames);
      trigger_to_assumption = (p.trigger_to_assumption);
      assumption_to_triggers = (p.assumption_to_triggers);
      assumption_name_map =
        (FStarC_PSMap.add p.assumption_name_map a.pa_name a);
      ambients = (p.ambients);
      extra_roots = (p.extra_roots);
      pruned_ambients = (p.pruned_ambients)
    } in
  match asum.asum_kind with
  | Sum_drop -> p1
  | Sum_ambient is_root ->
      let p2 =
        if is_root
        then
          {
            defs_and_decls_map = (p1.defs_and_decls_map);
            macro_freenames = (p1.macro_freenames);
            trigger_to_assumption = (p1.trigger_to_assumption);
            assumption_to_triggers = (p1.assumption_to_triggers);
            assumption_name_map = (p1.assumption_name_map);
            ambients = (p1.ambients);
            extra_roots = (a :: (p1.extra_roots));
            pruned_ambients = (p1.pruned_ambients)
          }
        else p1 in
      let uu___ = no_ambients () in
      if uu___
      then
        {
          defs_and_decls_map = (p2.defs_and_decls_map);
          macro_freenames = (p2.macro_freenames);
          trigger_to_assumption = (p2.trigger_to_assumption);
          assumption_to_triggers = (p2.assumption_to_triggers);
          assumption_name_map = (p2.assumption_name_map);
          ambients = (p2.ambients);
          extra_roots = (p2.extra_roots);
          pruned_ambients = ((a.pa_name) :: (p2.pruned_ambients))
        }
      else
        {
          defs_and_decls_map = (p2.defs_and_decls_map);
          macro_freenames = (p2.macro_freenames);
          trigger_to_assumption = (p2.trigger_to_assumption);
          assumption_to_triggers = (p2.assumption_to_triggers);
          assumption_name_map = (p2.assumption_name_map);
          ambients = ((a.pa_name) :: (p2.ambients));
          extra_roots = (p2.extra_roots);
          pruned_ambients = (p2.pruned_ambients)
        }
  | Sum_triggers trigs ->
      let p2 =
        let uu___ =
          let uu___1 =
            let uu___2 = triggers_as_triggers_set trigs in
            mk_remaining_triggers uu___2 in
          FStarC_PSMap.add p1.assumption_to_triggers a.pa_name uu___1 in
        {
          defs_and_decls_map = (p1.defs_and_decls_map);
          macro_freenames = (p1.macro_freenames);
          trigger_to_assumption = (p1.trigger_to_assumption);
          assumption_to_triggers = uu___;
          assumption_name_map = (p1.assumption_name_map);
          ambients = (p1.ambients);
          extra_roots = (p1.extra_roots);
          pruned_ambients = (p1.pruned_ambients)
        } in
      FStarC_List.fold_left
        (FStarC_List.fold_left (add_trigger_to_assumption a)) p2 trigs
let trigger_reached (p : pruning_state) (trig : Prims.string) :
  pruning_state=
  {
    defs_and_decls_map = (p.defs_and_decls_map);
    macro_freenames = (p.macro_freenames);
    trigger_to_assumption =
      (FStarC_PSMap.remove p.trigger_to_assumption trig);
    assumption_to_triggers = (p.assumption_to_triggers);
    assumption_name_map = (p.assumption_name_map);
    ambients = (p.ambients);
    extra_roots = (p.extra_roots);
    pruned_ambients = (p.pruned_ambients)
  }
let remove_trigger_for_assumption (p : pruning_state) (trig : sym)
  (aname : Prims.string) : (pruning_state * Prims.bool * sym Prims.list)=
  match FStarC_PSMap.try_find p.assumption_to_triggers aname with
  | FStar_Pervasives_Native.None -> (p, false, [])
  | FStar_Pervasives_Native.Some l ->
      let l1 =
        let uu___ =
          FStarC_List.map
            (fun ts ->
               FStarC_Class_Setlike.remove
                 (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string)
                 trig.sym_name ts) l.remaining_triggers in
        {
          remaining_triggers = uu___;
          already_triggered = (trig :: (l.already_triggered))
        } in
      let eligible =
        FStarC_Util.for_some
          (FStarC_Class_Setlike.is_empty
             (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string))
          l1.remaining_triggers in
      ({
         defs_and_decls_map = (p.defs_and_decls_map);
         macro_freenames = (p.macro_freenames);
         trigger_to_assumption = (p.trigger_to_assumption);
         assumption_to_triggers =
           (FStarC_PSMap.add p.assumption_to_triggers aname l1);
         assumption_name_map = (p.assumption_name_map);
         ambients = (p.ambients);
         extra_roots = (p.extra_roots);
         pruned_ambients = (p.pruned_ambients)
       }, eligible, (l1.already_triggered))
let rec assumptions_of_decl (d : FStarC_SMTEncoding_Term.decl) :
  FStarC_SMTEncoding_Term.assumption Prims.list=
  match d with
  | FStarC_SMTEncoding_Term.Assume a -> [a]
  | FStarC_SMTEncoding_Term.Module (uu___, ds) ->
      FStarC_List.collect assumptions_of_decl ds
  | d1 -> []
let passumption_of_assumption (a : FStarC_SMTEncoding_Term.assumption) :
  passumption=
  let uu___ = assumption_free_names a in
  {
    pa_name = (a.FStarC_SMTEncoding_Term.assumption_name);
    pa_free_names = uu___;
    pa_pretyping =
      (a.FStarC_SMTEncoding_Term.assumption_caption =
         (FStar_Pervasives_Native.Some "pretyping"));
    pa_resolve =
      (fun uu___1 ->
         FStar_Pervasives_Native.Some (FStarC_SMTEncoding_Term.Assume a))
  }
let add_summaries (sums : decl_summary Prims.list)
  (resolve :
    Prims.string ->
      FStarC_SMTEncoding_Term.decl FStar_Pervasives_Native.option)
  (p : pruning_state) : pruning_state=
  FStarC_List.fold_left
    (fun p1 sum ->
       match sum with
       | Sum_assume asum -> add_assumption_summary asum resolve p1
       | Sum_definefun (macro, free_names) ->
           {
             defs_and_decls_map =
               (FStarC_PSMap.add p1.defs_and_decls_map macro
                  {
                    pd_is_declfun = false;
                    pd_resolve = (fun uu___ -> resolve macro)
                  });
             macro_freenames =
               (FStarC_PSMap.add p1.macro_freenames macro free_names);
             trigger_to_assumption = (p1.trigger_to_assumption);
             assumption_to_triggers = (p1.assumption_to_triggers);
             assumption_name_map = (p1.assumption_name_map);
             ambients = (p1.ambients);
             extra_roots = (p1.extra_roots);
             pruned_ambients = (p1.pruned_ambients)
           }
       | Sum_declfun name ->
           {
             defs_and_decls_map =
               (FStarC_PSMap.add p1.defs_and_decls_map name
                  {
                    pd_is_declfun = true;
                    pd_resolve = (fun uu___ -> resolve name)
                  });
             macro_freenames = (p1.macro_freenames);
             trigger_to_assumption = (p1.trigger_to_assumption);
             assumption_to_triggers = (p1.assumption_to_triggers);
             assumption_name_map = (p1.assumption_name_map);
             ambients = (p1.ambients);
             extra_roots = (p1.extra_roots);
             pruned_ambients = (p1.pruned_ambients)
           }
       | Sum_retain uu___ -> p1
       | Sum_ignored -> p1
       | Sum_other uu___ -> p1) p sums
let name_of_decl (d : FStarC_SMTEncoding_Term.decl) : Prims.string=
  match d with
  | FStarC_SMTEncoding_Term.Assume a ->
      a.FStarC_SMTEncoding_Term.assumption_name
  | FStarC_SMTEncoding_Term.DeclFun (a, uu___, uu___1, uu___2) -> a
  | FStarC_SMTEncoding_Term.DefineFun (a, uu___, uu___1, uu___2, uu___3) -> a
  | uu___ -> "<none>"
let add_decls (ds : FStarC_SMTEncoding_Term.decl Prims.list)
  (p : pruning_state) : pruning_state=
  let rec add m d =
    match d with
    | FStarC_SMTEncoding_Term.Module (uu___, ds1) ->
        FStarC_List.fold_left add m ds1
    | FStarC_SMTEncoding_Term.Assume uu___ ->
        let uu___1 = name_of_decl d in FStarC_PSMap.add m uu___1 d
    | FStarC_SMTEncoding_Term.DeclFun (uu___, uu___1, uu___2, uu___3) ->
        let uu___4 = name_of_decl d in FStarC_PSMap.add m uu___4 d
    | FStarC_SMTEncoding_Term.DefineFun
        (uu___, uu___1, uu___2, uu___3, uu___4) ->
        let uu___5 = name_of_decl d in FStarC_PSMap.add m uu___5 d
    | uu___ -> m in
  let map = FStarC_List.fold_left add (FStarC_PSMap.empty ()) ds in
  let uu___ = summarize_decls ds in
  add_summaries uu___ (FStarC_PSMap.try_find map) p
type triggered_assumption =
  {
  assumption: passumption ;
  triggered_by: sym Prims.list }
let __proj__Mktriggered_assumption__item__assumption
  (projectee : triggered_assumption) : passumption=
  match projectee with | { assumption; triggered_by;_} -> assumption
let __proj__Mktriggered_assumption__item__triggered_by
  (projectee : triggered_assumption) : sym Prims.list=
  match projectee with | { assumption; triggered_by;_} -> triggered_by
type reached_assumption_names = Prims.string FStarC_RBSet.rbset
type ctxt = {
  p: pruning_state ;
  reached: reached_assumption_names }
let __proj__Mkctxt__item__p (projectee : ctxt) : pruning_state=
  match projectee with | { p; reached;_} -> p
let __proj__Mkctxt__item__reached (projectee : ctxt) :
  reached_assumption_names= match projectee with | { p; reached;_} -> reached
type 'a st = ctxt -> ('a * ctxt)
let get : ctxt st= fun s -> (s, s)
let put (c : ctxt) : unit st= fun uu___ -> ((), c)
let st_monad : unit st FStarC_Class_Monad.monad=
  {
    FStarC_Class_Monad.return =
      (fun uu___1 uu___ -> (fun a x s -> Obj.magic (x, s)) uu___1 uu___);
    FStarC_Class_Monad.bind =
      (fun uu___3 uu___2 uu___1 uu___ ->
         (fun a b m ->
            let m = Obj.magic m in
            fun f ->
              let f = Obj.magic f in
              fun s ->
                let uu___ = m s in
                match uu___ with
                | (x, s1) -> let uu___1 = f x in Obj.magic (uu___1 s1))
           uu___3 uu___2 uu___1 uu___)
  }
let mark_trigger_reached (x : sym) : unit st=
  FStarC_Class_Monad.op_let_Bang st_monad () () (Obj.magic get)
    (fun uu___ ->
       (fun ctxt1 ->
          let ctxt1 = Obj.magic ctxt1 in
          Obj.magic
            (put
               {
                 p = (trigger_reached ctxt1.p x.sym_name);
                 reached = (ctxt1.reached)
               })) uu___)
let find_assumptions_waiting_on_trigger (uu___ : sym) :
  passumption Prims.list st=
  (fun x ->
     Obj.magic
       (FStarC_Class_Monad.op_let_Bang st_monad () () (Obj.magic get)
          (fun uu___ ->
             (fun ctxt1 ->
                let ctxt1 = Obj.magic ctxt1 in
                match FStarC_PSMap.try_find (ctxt1.p).trigger_to_assumption
                        x.sym_name
                with
                | FStar_Pervasives_Native.None ->
                    Obj.magic
                      (FStarC_Class_Monad.return st_monad () (Obj.magic []))
                | FStar_Pervasives_Native.Some l ->
                    Obj.magic
                      (FStarC_Class_Monad.return st_monad () (Obj.magic l)))
               uu___))) uu___
let reached_assumption (aname : Prims.string) : unit st=
  FStarC_Class_Monad.op_let_Bang st_monad () () (Obj.magic get)
    (fun uu___ ->
       (fun ctxt1 ->
          let ctxt1 = Obj.magic ctxt1 in
          let p =
            let uu___ = ctxt1.p in
            {
              defs_and_decls_map = (uu___.defs_and_decls_map);
              macro_freenames = (uu___.macro_freenames);
              trigger_to_assumption = (uu___.trigger_to_assumption);
              assumption_to_triggers =
                (FStarC_PSMap.remove (ctxt1.p).assumption_to_triggers aname);
              assumption_name_map = (uu___.assumption_name_map);
              ambients = (uu___.ambients);
              extra_roots = (uu___.extra_roots);
              pruned_ambients = (uu___.pruned_ambients)
            } in
          let uu___ =
            let uu___1 =
              FStarC_Class_Setlike.add
                (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string)
                aname ctxt1.reached in
            { p = (ctxt1.p); reached = uu___1 } in
          Obj.magic (put uu___)) uu___)
let remove_trigger_for (uu___1 : sym) (uu___ : passumption) :
  (Prims.bool * sym Prims.list) st=
  (fun trig a ->
     Obj.magic
       (FStarC_Class_Monad.op_let_Bang st_monad () () (Obj.magic get)
          (fun uu___ ->
             (fun ctxt1 ->
                let ctxt1 = Obj.magic ctxt1 in
                let uu___ =
                  remove_trigger_for_assumption ctxt1.p trig a.pa_name in
                match uu___ with
                | (p, eligible, already_triggered) ->
                    Obj.magic
                      (FStarC_Class_Monad.op_let_Bang st_monad () ()
                         (put { p; reached = (ctxt1.reached) })
                         (fun uu___1 ->
                            (fun uu___1 ->
                               let uu___1 = Obj.magic uu___1 in
                               Obj.magic
                                 (FStarC_Class_Monad.return st_monad ()
                                    (Obj.magic (eligible, already_triggered))))
                              uu___1))) uu___))) uu___1 uu___
let already_reached (uu___ : Prims.string) : Prims.bool st=
  (fun aname ->
     Obj.magic
       (FStarC_Class_Monad.op_let_Bang st_monad () () (Obj.magic get)
          (fun uu___ ->
             (fun ctxt1 ->
                let ctxt1 = Obj.magic ctxt1 in
                let uu___ =
                  FStarC_Class_Setlike.mem
                    (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string)
                    aname ctxt1.reached in
                Obj.magic
                  (FStarC_Class_Monad.return st_monad () (Obj.magic uu___)))
               uu___))) uu___
let trigger_pending_assumptions (uu___ : sym Prims.list) :
  triggered_assumption Prims.list st=
  (fun lids ->
     Obj.magic
       (FStarC_Class_Monad.foldM_left st_monad () ()
          (fun uu___1 uu___ ->
             (fun acc ->
                let acc = Obj.magic acc in
                fun lid ->
                  let lid = Obj.magic lid in
                  let uu___ = find_assumptions_waiting_on_trigger lid in
                  Obj.magic
                    (FStarC_Class_Monad.op_let_Bang st_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             let uu___1 = Obj.magic uu___1 in
                             match uu___1 with
                             | [] ->
                                 Obj.magic
                                   (FStarC_Class_Monad.return st_monad ()
                                      (Obj.magic acc))
                             | assumptions ->
                                 let uu___2 = mark_trigger_reached lid in
                                 Obj.magic
                                   (FStarC_Class_Monad.op_let_Bang st_monad
                                      () () uu___2
                                      (fun uu___3 ->
                                         (fun uu___3 ->
                                            let uu___3 = Obj.magic uu___3 in
                                            Obj.magic
                                              (FStarC_Class_Monad.foldM_left
                                                 st_monad () ()
                                                 (fun uu___5 uu___4 ->
                                                    (fun acc1 ->
                                                       let acc1 =
                                                         Obj.magic acc1 in
                                                       fun assumption ->
                                                         let assumption =
                                                           Obj.magic
                                                             assumption in
                                                         let uu___4 =
                                                           remove_trigger_for
                                                             lid assumption in
                                                         Obj.magic
                                                           (FStarC_Class_Monad.op_let_Bang
                                                              st_monad () ()
                                                              (Obj.magic
                                                                 uu___4)
                                                              (fun uu___5 ->
                                                                 (fun uu___5
                                                                    ->
                                                                    let uu___5
                                                                    =
                                                                    Obj.magic
                                                                    uu___5 in
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (eligible,
                                                                    triggered_by)
                                                                    ->
                                                                    if
                                                                    eligible
                                                                    then
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.return
                                                                    st_monad
                                                                    ()
                                                                    (Obj.magic
                                                                    ({
                                                                    assumption;
                                                                    triggered_by
                                                                    } ::
                                                                    acc1)))
                                                                    else
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.return
                                                                    st_monad
                                                                    ()
                                                                    (Obj.magic
                                                                    acc1)))
                                                                   uu___5)))
                                                      uu___5 uu___4)
                                                 (Obj.magic acc)
                                                 (Obj.magic assumptions)))
                                           uu___3))) uu___1))) uu___1 uu___)
          (Obj.magic []) (Obj.magic lids))) uu___
let rec scan (ds : passumption Prims.list) : unit st=
  FStarC_Class_Monad.op_let_Bang st_monad () () (Obj.magic get)
    (fun uu___ ->
       (fun ctxt1 ->
          let ctxt1 = Obj.magic ctxt1 in
          let mk_sym assumption_name1 l =
            { sym_name = l; sym_provenance = assumption_name1 } in
          let macro_expand s =
            match FStarC_PSMap.try_find (ctxt1.p).macro_freenames s.sym_name
            with
            | FStar_Pervasives_Native.None -> [s]
            | FStar_Pervasives_Native.Some l ->
                let uu___ = FStarC_List.map (mk_sym s.sym_provenance) l in s
                  :: uu___ in
          let new_syms =
            FStarC_List.collect
              (fun a ->
                 let uu___ =
                   let uu___1 =
                     FStarC_Class_Setlike.elems
                       (FStarC_RBSet.setlike_rbset
                          FStarC_Class_Ord.ord_string) a.pa_free_names in
                   FStarC_List.map (mk_sym a.pa_name) uu___1 in
                 FStarC_List.collect macro_expand uu___) ds in
          let uu___ = trigger_pending_assumptions new_syms in
          Obj.magic
            (FStarC_Class_Monad.op_let_Bang st_monad () () (Obj.magic uu___)
               (fun uu___1 ->
                  (fun uu___1 ->
                     let uu___1 = Obj.magic uu___1 in
                     match uu___1 with
                     | [] ->
                         Obj.magic
                           (FStarC_Class_Monad.return st_monad ()
                              (Obj.repr ()))
                     | triggered ->
                         let uu___2 =
                           Obj.magic
                             (FStarC_Class_Monad.foldM_left st_monad () ()
                                (fun uu___4 uu___3 ->
                                   (fun acc ->
                                      let acc = Obj.magic acc in
                                      fun triggered_assumption1 ->
                                        let triggered_assumption1 =
                                          Obj.magic triggered_assumption1 in
                                        let assumption =
                                          triggered_assumption1.assumption in
                                        let uu___3 =
                                          already_reached assumption.pa_name in
                                        Obj.magic
                                          (FStarC_Class_Monad.op_let_Bang
                                             st_monad () ()
                                             (Obj.magic uu___3)
                                             (fun uu___4 ->
                                                (fun uu___4 ->
                                                   let uu___4 =
                                                     Obj.magic uu___4 in
                                                   if uu___4
                                                   then
                                                     Obj.magic
                                                       (FStarC_Class_Monad.return
                                                          st_monad ()
                                                          (Obj.magic acc))
                                                   else
                                                     (let uu___5 =
                                                        let uu___6 =
                                                          should_retain_assumption
                                                            assumption in
                                                        Prims.not uu___6 in
                                                      if uu___5
                                                      then
                                                        Obj.magic
                                                          (FStarC_Class_Monad.return
                                                             st_monad ()
                                                             (Obj.magic acc))
                                                      else
                                                        (let uu___6 =
                                                           reached_assumption
                                                             assumption.pa_name in
                                                         Obj.magic
                                                           (FStarC_Class_Monad.op_let_Bang
                                                              st_monad () ()
                                                              uu___6
                                                              (fun uu___7 ->
                                                                 (fun uu___7
                                                                    ->
                                                                    let uu___7
                                                                    =
                                                                    Obj.magic
                                                                    uu___7 in
                                                                    Obj.magic
                                                                    (FStarC_Class_Monad.return
                                                                    st_monad
                                                                    ()
                                                                    (Obj.magic
                                                                    (assumption
                                                                    :: acc))))
                                                                   uu___7)))))
                                                  uu___4))) uu___4 uu___3)
                                (Obj.magic []) (Obj.magic triggered)) in
                         Obj.magic
                           (FStarC_Class_Monad.op_let_Bang st_monad () ()
                              (Obj.magic uu___2)
                              (fun uu___3 ->
                                 (fun to_scan ->
                                    let to_scan = Obj.magic to_scan in
                                    Obj.magic (scan to_scan)) uu___3)))
                    uu___1))) uu___)
let print_reached_names_and_reasons (ctxt1 : ctxt)
  (names : Prims.string Prims.list) : Prims.string=
  let print_one name =
    match FStarC_PSMap.try_find (ctxt1.p).assumption_to_triggers name with
    | FStar_Pervasives_Native.None ->
        FStarC_Format.fmt1 "%s (included but not found in map)" name
    | FStar_Pervasives_Native.Some l ->
        let uu___ =
          FStarC_Class_Show.show (FStarC_Class_Show.show_list showable_sym)
            l.already_triggered in
        FStarC_Format.fmt2 "%s {triggered by %s}" name uu___ in
  let uu___ = FStarC_List.map print_one names in
  FStarC_String.concat "\n\t" uu___
let prune (p : pruning_state)
  (roots0 : FStarC_SMTEncoding_Term.decl Prims.list) :
  FStarC_SMTEncoding_Term.decl Prims.list=
  let root_assumptions =
    let uu___ = FStarC_List.collect assumptions_of_decl roots0 in
    FStarC_List.map passumption_of_assumption uu___ in
  let init1 =
    let uu___ =
      FStarC_Class_Setlike.empty
        (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string) () in
    { p; reached = uu___ } in
  let roots =
    let uu___ = no_ambients () in
    if uu___
    then root_assumptions
    else FStar_List_Tot_Base.op_At root_assumptions p.extra_roots in
  let uu___ = let uu___1 = scan roots in uu___1 init1 in
  match uu___ with
  | (uu___1, ctxt1) ->
      let reached_names =
        FStarC_Class_Setlike.elems
          (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string)
          ctxt1.reached in
      ((let uu___3 = no_ambients () in
        if uu___3
        then
          debug
            (fun uu___4 ->
               let uu___5 =
                 let uu___6 =
                   scan (FStar_List_Tot_Base.op_At roots p.extra_roots) in
                 uu___6 init1 in
               match uu___5 with
               | (uu___6, ctxt') ->
                   let extra_reached =
                     let uu___7 =
                       FStarC_Class_Setlike.diff
                         (FStarC_RBSet.setlike_rbset
                            FStarC_Class_Ord.ord_string) ctxt'.reached
                         ctxt1.reached in
                     FStarC_Class_Setlike.elems
                       (FStarC_RBSet.setlike_rbset
                          FStarC_Class_Ord.ord_string) uu___7 in
                   let uu___7 =
                     FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                       (FStarC_List.length p.pruned_ambients) in
                   let uu___8 =
                     FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                       (FStarC_List.length extra_reached) in
                   let uu___9 =
                     FStarC_Class_Show.show
                       (FStarC_Class_Show.show_list
                          FStarC_Class_Show.showable_string)
                       p.pruned_ambients in
                   let uu___10 =
                     FStarC_Class_Show.show
                       (FStarC_Class_Show.show_list
                          FStarC_Class_Show.showable_string) extra_reached in
                   FStarC_Format.print4
                     "Debug context pruning: Excluded %s ambients resulted in pruning %s assumptions\nambients %s\npruned assumptions %s\n"
                     uu___7 uu___8 uu___9 uu___10)
        else ());
       (let reached_assumptions =
          FStarC_List.collect
            (fun name ->
               match FStarC_PSMap.try_find (ctxt1.p).assumption_name_map name
               with
               | FStar_Pervasives_Native.None -> []
               | FStar_Pervasives_Native.Some a -> [a])
            (FStar_List_Tot_Base.op_At reached_names p.ambients) in
        debug
          (fun uu___4 ->
             let uu___5 =
               FStarC_Class_Show.show FStarC_Class_Show.showable_nat
                 (FStarC_List.length reached_assumptions) in
             let uu___6 =
               print_reached_names_and_reasons ctxt1
                 (FStar_List_Tot_Base.op_At reached_names p.ambients) in
             FStarC_Format.print2
               "Debug context pruning: Retained %s assumptions\n%s\n" uu___5
               uu___6);
        (let decls_and_defs =
           let uu___4 =
             let uu___5 = FStarC_Options_Ext.enabled "prune_decls" in
             Prims.not uu___5 in
           if uu___4
           then []
           else
             (let uu___5 =
                let uu___6 =
                  let uu___7 =
                    FStarC_Class_Setlike.empty
                      (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string)
                      () in
                  (uu___7, []) in
                FStarC_List.fold_left
                  (fun uu___7 a ->
                     match uu___7 with
                     | (included_decl_names, defs_and_decls) ->
                         let uu___8 =
                           FStarC_Class_Setlike.elems
                             (FStarC_RBSet.setlike_rbset
                                FStarC_Class_Ord.ord_string) a.pa_free_names in
                         FStarC_List.fold_left
                           (fun uu___9 name ->
                              match uu___9 with
                              | (included_decl_names1, defs_and_decls1) ->
                                  let uu___10 =
                                    FStarC_Class_Setlike.mem
                                      (FStarC_RBSet.setlike_rbset
                                         FStarC_Class_Ord.ord_string) name
                                      included_decl_names1 in
                                  if uu___10
                                  then
                                    (included_decl_names1, defs_and_decls1)
                                  else
                                    (match FStarC_PSMap.try_find
                                             p.defs_and_decls_map name
                                     with
                                     | FStar_Pervasives_Native.None ->
                                         (included_decl_names1,
                                           defs_and_decls1)
                                     | FStar_Pervasives_Native.Some d ->
                                         let uu___11 =
                                           FStarC_Class_Setlike.add
                                             (FStarC_RBSet.setlike_rbset
                                                FStarC_Class_Ord.ord_string)
                                             name included_decl_names1 in
                                         (uu___11, (d :: defs_and_decls1))))
                           (included_decl_names, defs_and_decls) uu___8)
                  uu___6
                  (FStar_List_Tot_Base.op_At reached_assumptions
                     root_assumptions) in
              match uu___5 with
              | (uu___6, defs_and_decls) ->
                  let uu___7 =
                    FStarC_List.partition (fun d -> d.pd_is_declfun)
                      defs_and_decls in
                  (match uu___7 with
                   | (decls, defs) ->
                       FStarC_List.collect
                         (fun d ->
                            let uu___8 = d.pd_resolve () in
                            match uu___8 with
                            | FStar_Pervasives_Native.None -> []
                            | FStar_Pervasives_Native.Some d1 -> [d1])
                         (FStar_List_Tot_Base.op_At defs decls))) in
         let reached_decls =
           FStarC_List.collect
             (fun a ->
                let uu___4 = a.pa_resolve () in
                match uu___4 with
                | FStar_Pervasives_Native.None -> []
                | FStar_Pervasives_Native.Some d -> [d]) reached_assumptions in
         let print_assumption a =
           let uu___4 =
             FStarC_Class_Show.show FStarC_Class_Show.showable_string
               a.pa_name in
           let uu___5 =
             FStarC_Class_Show.show
               (FStarC_RBSet.showable_rbset FStarC_Class_Show.showable_string)
               a.pa_free_names in
           FStarC_Format.fmt2 "{name=%s; freevars={%s}}" uu___4 uu___5 in
         debug
           (fun uu___5 ->
              let uu___6 =
                let uu___7 = FStarC_List.map print_assumption roots in
                FStarC_Class_Show.show
                  (FStarC_Class_Show.show_list
                     FStarC_Class_Show.showable_string) uu___7 in
              let uu___7 =
                let uu___8 = FStarC_List.map name_of_decl decls_and_defs in
                FStarC_Class_Show.show
                  (FStarC_Class_Show.show_list
                     FStarC_Class_Show.showable_string) uu___8 in
              FStarC_Format.print2
                "Debug context pruning: roots %s, retained decls and defs %s\n"
                uu___6 uu___7);
         FStar_List_Tot_Base.op_At reached_decls decls_and_defs)))
