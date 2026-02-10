open Prims
type triggers = Prims.string Prims.list Prims.list
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
    (fun uu___ ->
       (Obj.magic
          (FStarC_Class_Setlike.from_list ()
             (Obj.magic
                (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string))))
         uu___) ts
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
type pruning_state =
  {
  defs_and_decls: FStarC_SMTEncoding_Term.decl Prims.list ;
  defs_and_decls_map: FStarC_SMTEncoding_Term.decl FStarC_PSMap.t ;
  macro_freenames: Prims.string Prims.list FStarC_PSMap.t ;
  trigger_to_assumption:
    FStarC_SMTEncoding_Term.assumption Prims.list FStarC_PSMap.t ;
  assumption_to_triggers: assumption_remaining_triggers FStarC_PSMap.t ;
  assumption_name_map: FStarC_SMTEncoding_Term.decl FStarC_PSMap.t ;
  ambients: Prims.string Prims.list ;
  extra_roots: FStarC_SMTEncoding_Term.assumption Prims.list ;
  pruned_ambients: Prims.string Prims.list }
let __proj__Mkpruning_state__item__defs_and_decls (projectee : pruning_state)
  : FStarC_SMTEncoding_Term.decl Prims.list=
  match projectee with
  | { defs_and_decls; defs_and_decls_map; macro_freenames;
      trigger_to_assumption; assumption_to_triggers; assumption_name_map;
      ambients; extra_roots; pruned_ambients;_} -> defs_and_decls
let __proj__Mkpruning_state__item__defs_and_decls_map
  (projectee : pruning_state) : FStarC_SMTEncoding_Term.decl FStarC_PSMap.t=
  match projectee with
  | { defs_and_decls; defs_and_decls_map; macro_freenames;
      trigger_to_assumption; assumption_to_triggers; assumption_name_map;
      ambients; extra_roots; pruned_ambients;_} -> defs_and_decls_map
let __proj__Mkpruning_state__item__macro_freenames
  (projectee : pruning_state) : Prims.string Prims.list FStarC_PSMap.t=
  match projectee with
  | { defs_and_decls; defs_and_decls_map; macro_freenames;
      trigger_to_assumption; assumption_to_triggers; assumption_name_map;
      ambients; extra_roots; pruned_ambients;_} -> macro_freenames
let __proj__Mkpruning_state__item__trigger_to_assumption
  (projectee : pruning_state) :
  FStarC_SMTEncoding_Term.assumption Prims.list FStarC_PSMap.t=
  match projectee with
  | { defs_and_decls; defs_and_decls_map; macro_freenames;
      trigger_to_assumption; assumption_to_triggers; assumption_name_map;
      ambients; extra_roots; pruned_ambients;_} -> trigger_to_assumption
let __proj__Mkpruning_state__item__assumption_to_triggers
  (projectee : pruning_state) : assumption_remaining_triggers FStarC_PSMap.t=
  match projectee with
  | { defs_and_decls; defs_and_decls_map; macro_freenames;
      trigger_to_assumption; assumption_to_triggers; assumption_name_map;
      ambients; extra_roots; pruned_ambients;_} -> assumption_to_triggers
let __proj__Mkpruning_state__item__assumption_name_map
  (projectee : pruning_state) : FStarC_SMTEncoding_Term.decl FStarC_PSMap.t=
  match projectee with
  | { defs_and_decls; defs_and_decls_map; macro_freenames;
      trigger_to_assumption; assumption_to_triggers; assumption_name_map;
      ambients; extra_roots; pruned_ambients;_} -> assumption_name_map
let __proj__Mkpruning_state__item__ambients (projectee : pruning_state) :
  Prims.string Prims.list=
  match projectee with
  | { defs_and_decls; defs_and_decls_map; macro_freenames;
      trigger_to_assumption; assumption_to_triggers; assumption_name_map;
      ambients; extra_roots; pruned_ambients;_} -> ambients
let __proj__Mkpruning_state__item__extra_roots (projectee : pruning_state) :
  FStarC_SMTEncoding_Term.assumption Prims.list=
  match projectee with
  | { defs_and_decls; defs_and_decls_map; macro_freenames;
      trigger_to_assumption; assumption_to_triggers; assumption_name_map;
      ambients; extra_roots; pruned_ambients;_} -> extra_roots
let __proj__Mkpruning_state__item__pruned_ambients
  (projectee : pruning_state) : Prims.string Prims.list=
  match projectee with
  | { defs_and_decls; defs_and_decls_map; macro_freenames;
      trigger_to_assumption; assumption_to_triggers; assumption_name_map;
      ambients; extra_roots; pruned_ambients;_} -> pruned_ambients
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
  let uu___ = FStarC_PSMap.empty () in
  let uu___1 = FStarC_PSMap.empty () in
  let uu___2 = FStarC_PSMap.empty () in
  let uu___3 = FStarC_PSMap.empty () in
  {
    defs_and_decls = [];
    defs_and_decls_map = uu___;
    macro_freenames = init_macro_freenames;
    trigger_to_assumption = uu___1;
    assumption_to_triggers = uu___2;
    assumption_name_map = uu___3;
    ambients = [];
    extra_roots = [];
    pruned_ambients = []
  }
let add_trigger_to_assumption (a : FStarC_SMTEncoding_Term.assumption)
  (p : pruning_state) (trig : Prims.string) : pruning_state=
  let uu___ = FStarC_PSMap.try_find p.trigger_to_assumption trig in
  match uu___ with
  | FStar_Pervasives_Native.None ->
      let uu___1 = FStarC_PSMap.add p.trigger_to_assumption trig [a] in
      {
        defs_and_decls = (p.defs_and_decls);
        defs_and_decls_map = (p.defs_and_decls_map);
        macro_freenames = (p.macro_freenames);
        trigger_to_assumption = uu___1;
        assumption_to_triggers = (p.assumption_to_triggers);
        assumption_name_map = (p.assumption_name_map);
        ambients = (p.ambients);
        extra_roots = (p.extra_roots);
        pruned_ambients = (p.pruned_ambients)
      }
  | FStar_Pervasives_Native.Some l ->
      let uu___1 = FStarC_PSMap.add p.trigger_to_assumption trig (a :: l) in
      {
        defs_and_decls = (p.defs_and_decls);
        defs_and_decls_map = (p.defs_and_decls_map);
        macro_freenames = (p.macro_freenames);
        trigger_to_assumption = uu___1;
        assumption_to_triggers = (p.assumption_to_triggers);
        assumption_name_map = (p.assumption_name_map);
        ambients = (p.ambients);
        extra_roots = (p.extra_roots);
        pruned_ambients = (p.pruned_ambients)
      }
let exclude_names : Prims.string FStarC_RBSet.t=
  Obj.magic
    (FStarC_Class_Setlike.from_list ()
       (Obj.magic (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string))
       ["SFuel";
       "ZFuel";
       "HasType";
       "HasTypeZ";
       "HasTypeFuel";
       "Valid";
       "ApplyTT";
       "ApplyTF";
       "Prims.lex_t"])
let free_top_level_names (uu___ : FStarC_SMTEncoding_Term.term) :
  Prims.string FStarC_RBSet.t=
  (fun t ->
     let uu___ = FStarC_SMTEncoding_Term.free_top_level_names t in
     Obj.magic
       (FStarC_Class_Setlike.diff ()
          (Obj.magic (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string))
          (Obj.magic uu___) (Obj.magic exclude_names))) uu___
let assumption_free_names (uu___ : FStarC_SMTEncoding_Term.assumption) :
  Prims.string FStarC_RBSet.t=
  (fun a ->
     Obj.magic
       (FStarC_Class_Setlike.diff ()
          (Obj.magic (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string))
          (Obj.magic a.FStarC_SMTEncoding_Term.assumption_free_names)
          (Obj.magic exclude_names))) uu___
let triggers_of_term (t : FStarC_SMTEncoding_Term.term) : triggers_set=
  let rec aux t1 =
    match t1.FStarC_SMTEncoding_Term.tm with
    | FStarC_SMTEncoding_Term.Quant
        (FStarC_SMTEncoding_Term.Forall, triggers1, uu___, uu___1, uu___2) ->
        FStarC_List.map
          (fun disjunct ->
             let uu___3 =
               Obj.magic
                 (FStarC_Class_Setlike.empty ()
                    (Obj.magic
                       (FStarC_RBSet.setlike_rbset
                          FStarC_Class_Ord.ord_string)) ()) in
             FStarC_List.fold_left
               (fun uu___5 uu___4 ->
                  (fun out t2 ->
                     let uu___4 = free_top_level_names t2 in
                     Obj.magic
                       (FStarC_Class_Setlike.union ()
                          (Obj.magic
                             (FStarC_RBSet.setlike_rbset
                                FStarC_Class_Ord.ord_string)) (Obj.magic out)
                          (Obj.magic uu___4))) uu___5 uu___4) uu___3 disjunct)
          triggers1
    | FStarC_SMTEncoding_Term.Labeled (t2, uu___, uu___1) -> aux t2
    | uu___ -> [] in
  aux t
let maybe_add_ambient (a : FStarC_SMTEncoding_Term.assumption)
  (p : pruning_state) : pruning_state=
  let add_assumption_with_triggers triggers1 =
    let p1 =
      let uu___ =
        FStarC_PSMap.add p.assumption_to_triggers
          a.FStarC_SMTEncoding_Term.assumption_name
          (mk_remaining_triggers triggers1) in
      {
        defs_and_decls = (p.defs_and_decls);
        defs_and_decls_map = (p.defs_and_decls_map);
        macro_freenames = (p.macro_freenames);
        trigger_to_assumption = (p.trigger_to_assumption);
        assumption_to_triggers = uu___;
        assumption_name_map = (p.assumption_name_map);
        ambients = (p.ambients);
        extra_roots = (p.extra_roots);
        pruned_ambients = (p.pruned_ambients)
      } in
    let uu___ =
      FStarC_List.map
        (fun uu___1 ->
           (Obj.magic
              (FStarC_Class_Setlike.elems ()
                 (Obj.magic
                    (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string))))
             uu___1) triggers1 in
    FStarC_List.fold_left
      (FStarC_List.fold_left (add_trigger_to_assumption a)) p1 uu___ in
  let is_empty triggers1 =
    match triggers1 with
    | [] -> true
    | t::[] ->
        FStarC_Class_Setlike.is_empty ()
          (Obj.magic (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string))
          (Obj.magic t)
    | uu___ -> false in
  let is_ambient_refinement ty =
    match ty.FStarC_SMTEncoding_Term.tm with
    | FStarC_SMTEncoding_Term.App
        (FStarC_SMTEncoding_Term.Var "Prims.squash", uu___) -> true
    | FStarC_SMTEncoding_Term.App (FStarC_SMTEncoding_Term.Var name, uu___)
        -> FStarC_Util.starts_with name "Tm_refine_"
    | FStarC_SMTEncoding_Term.FreeV (FStarC_SMTEncoding_Term.FV
        (name, uu___, uu___1)) -> FStarC_Util.starts_with name "Tm_refine_"
    | uu___ -> false in
  let ambient_refinement_payload ty =
    match ty.FStarC_SMTEncoding_Term.tm with
    | FStarC_SMTEncoding_Term.App
        (FStarC_SMTEncoding_Term.Var "Prims.squash", uu___::t::[]) -> t
    | uu___ -> ty in
  if
    a.FStarC_SMTEncoding_Term.assumption_name =
      "function_token_typing_Prims.__cache_version_number__"
  then
    {
      defs_and_decls = (p.defs_and_decls);
      defs_and_decls_map = (p.defs_and_decls_map);
      macro_freenames = (p.macro_freenames);
      trigger_to_assumption = (p.trigger_to_assumption);
      assumption_to_triggers = (p.assumption_to_triggers);
      assumption_name_map = (p.assumption_name_map);
      ambients = ((a.FStarC_SMTEncoding_Term.assumption_name) ::
        (p.ambients));
      extra_roots = (p.extra_roots);
      pruned_ambients = (p.pruned_ambients)
    }
  else
    (match (a.FStarC_SMTEncoding_Term.assumption_term).FStarC_SMTEncoding_Term.tm
     with
     | FStarC_SMTEncoding_Term.App (FStarC_SMTEncoding_Term.Iff, t0::t1::[])
         when
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
         (FStarC_SMTEncoding_Term.Var "HasType", term::ty::[]) when
         is_ambient_refinement ty ->
         let triggers1 = triggers_of_term (ambient_refinement_payload ty) in
         let uu___ = is_empty triggers1 in
         if uu___
         then
           let p1 =
             {
               defs_and_decls = (p.defs_and_decls);
               defs_and_decls_map = (p.defs_and_decls_map);
               macro_freenames = (p.macro_freenames);
               trigger_to_assumption = (p.trigger_to_assumption);
               assumption_to_triggers = (p.assumption_to_triggers);
               assumption_name_map = (p.assumption_name_map);
               ambients = (p.ambients);
               extra_roots = (a :: (p.extra_roots));
               pruned_ambients = (p.pruned_ambients)
             } in
           let uu___1 = no_ambients () in
           (if uu___1
            then
              {
                defs_and_decls = (p1.defs_and_decls);
                defs_and_decls_map = (p1.defs_and_decls_map);
                macro_freenames = (p1.macro_freenames);
                trigger_to_assumption = (p1.trigger_to_assumption);
                assumption_to_triggers = (p1.assumption_to_triggers);
                assumption_name_map = (p1.assumption_name_map);
                ambients = (p1.ambients);
                extra_roots = (p1.extra_roots);
                pruned_ambients =
                  ((a.FStarC_SMTEncoding_Term.assumption_name) ::
                  (p1.pruned_ambients))
              }
            else
              {
                defs_and_decls = (p1.defs_and_decls);
                defs_and_decls_map = (p1.defs_and_decls_map);
                macro_freenames = (p1.macro_freenames);
                trigger_to_assumption = (p1.trigger_to_assumption);
                assumption_to_triggers = (p1.assumption_to_triggers);
                assumption_name_map = (p1.assumption_name_map);
                ambients = ((a.FStarC_SMTEncoding_Term.assumption_name) ::
                  (p1.ambients));
                extra_roots = (p1.extra_roots);
                pruned_ambients = (p1.pruned_ambients)
              })
         else add_assumption_with_triggers triggers1
     | FStarC_SMTEncoding_Term.App
         (FStarC_SMTEncoding_Term.Var "Valid",
          {
            FStarC_SMTEncoding_Term.tm = FStarC_SMTEncoding_Term.App
              (FStarC_SMTEncoding_Term.Var "ApplyTT",
               {
                 FStarC_SMTEncoding_Term.tm = FStarC_SMTEncoding_Term.FreeV
                   (FStarC_SMTEncoding_Term.FV
                   ("__uu__PartialApp", uu___, uu___1));
                 FStarC_SMTEncoding_Term.freevars = uu___2;
                 FStarC_SMTEncoding_Term.rng = uu___3;_}::term::[]);
            FStarC_SMTEncoding_Term.freevars = uu___4;
            FStarC_SMTEncoding_Term.rng = uu___5;_}::[])
         ->
         let triggers1 =
           match term.FStarC_SMTEncoding_Term.tm with
           | FStarC_SMTEncoding_Term.FreeV (FStarC_SMTEncoding_Term.FV
               (token, uu___6, uu___7)) ->
               if FStarC_Util.ends_with token "@tok"
               then
                 let uu___8 =
                   Obj.magic
                     (FStarC_Class_Setlike.singleton ()
                        (Obj.magic
                           (FStarC_RBSet.setlike_rbset
                              FStarC_Class_Ord.ord_string)) token) in
                 let uu___9 =
                   let uu___10 =
                     let uu___11 =
                       FStarC_Util.substring token Prims.int_zero
                         ((FStarC_String.length token) - (Prims.of_int (4))) in
                     Obj.magic
                       (FStarC_Class_Setlike.singleton ()
                          (Obj.magic
                             (FStarC_RBSet.setlike_rbset
                                FStarC_Class_Ord.ord_string)) uu___11) in
                   [uu___10] in
                 uu___8 :: uu___9
               else
                 (let uu___9 =
                    Obj.magic
                      (FStarC_Class_Setlike.singleton ()
                         (Obj.magic
                            (FStarC_RBSet.setlike_rbset
                               FStarC_Class_Ord.ord_string)) token) in
                  [uu___9])
           | FStarC_SMTEncoding_Term.App
               (FStarC_SMTEncoding_Term.Var token, []) ->
               if FStarC_Util.ends_with token "@tok"
               then
                 let uu___6 =
                   Obj.magic
                     (FStarC_Class_Setlike.singleton ()
                        (Obj.magic
                           (FStarC_RBSet.setlike_rbset
                              FStarC_Class_Ord.ord_string)) token) in
                 let uu___7 =
                   let uu___8 =
                     let uu___9 =
                       FStarC_Util.substring token Prims.int_zero
                         ((FStarC_String.length token) - (Prims.of_int (4))) in
                     Obj.magic
                       (FStarC_Class_Setlike.singleton ()
                          (Obj.magic
                             (FStarC_RBSet.setlike_rbset
                                FStarC_Class_Ord.ord_string)) uu___9) in
                   [uu___8] in
                 uu___6 :: uu___7
               else
                 (let uu___7 =
                    Obj.magic
                      (FStarC_Class_Setlike.singleton ()
                         (Obj.magic
                            (FStarC_RBSet.setlike_rbset
                               FStarC_Class_Ord.ord_string)) token) in
                  [uu___7])
           | uu___6 -> [] in
         add_assumption_with_triggers triggers1
     | FStarC_SMTEncoding_Term.App
         (FStarC_SMTEncoding_Term.Var "Valid",
          {
            FStarC_SMTEncoding_Term.tm = FStarC_SMTEncoding_Term.App
              (FStarC_SMTEncoding_Term.Var "ApplyTT",
               {
                 FStarC_SMTEncoding_Term.tm = FStarC_SMTEncoding_Term.App
                   (FStarC_SMTEncoding_Term.Var "__uu__PartialApp", uu___);
                 FStarC_SMTEncoding_Term.freevars = uu___1;
                 FStarC_SMTEncoding_Term.rng = uu___2;_}::term::[]);
            FStarC_SMTEncoding_Term.freevars = uu___3;
            FStarC_SMTEncoding_Term.rng = uu___4;_}::[])
         ->
         let triggers1 =
           match term.FStarC_SMTEncoding_Term.tm with
           | FStarC_SMTEncoding_Term.FreeV (FStarC_SMTEncoding_Term.FV
               (token, uu___5, uu___6)) ->
               if FStarC_Util.ends_with token "@tok"
               then
                 let uu___7 =
                   Obj.magic
                     (FStarC_Class_Setlike.singleton ()
                        (Obj.magic
                           (FStarC_RBSet.setlike_rbset
                              FStarC_Class_Ord.ord_string)) token) in
                 let uu___8 =
                   let uu___9 =
                     let uu___10 =
                       FStarC_Util.substring token Prims.int_zero
                         ((FStarC_String.length token) - (Prims.of_int (4))) in
                     Obj.magic
                       (FStarC_Class_Setlike.singleton ()
                          (Obj.magic
                             (FStarC_RBSet.setlike_rbset
                                FStarC_Class_Ord.ord_string)) uu___10) in
                   [uu___9] in
                 uu___7 :: uu___8
               else
                 (let uu___8 =
                    Obj.magic
                      (FStarC_Class_Setlike.singleton ()
                         (Obj.magic
                            (FStarC_RBSet.setlike_rbset
                               FStarC_Class_Ord.ord_string)) token) in
                  [uu___8])
           | FStarC_SMTEncoding_Term.App
               (FStarC_SMTEncoding_Term.Var token, []) ->
               if FStarC_Util.ends_with token "@tok"
               then
                 let uu___5 =
                   Obj.magic
                     (FStarC_Class_Setlike.singleton ()
                        (Obj.magic
                           (FStarC_RBSet.setlike_rbset
                              FStarC_Class_Ord.ord_string)) token) in
                 let uu___6 =
                   let uu___7 =
                     let uu___8 =
                       FStarC_Util.substring token Prims.int_zero
                         ((FStarC_String.length token) - (Prims.of_int (4))) in
                     Obj.magic
                       (FStarC_Class_Setlike.singleton ()
                          (Obj.magic
                             (FStarC_RBSet.setlike_rbset
                                FStarC_Class_Ord.ord_string)) uu___8) in
                   [uu___7] in
                 uu___5 :: uu___6
               else
                 (let uu___6 =
                    Obj.magic
                      (FStarC_Class_Setlike.singleton ()
                         (Obj.magic
                            (FStarC_RBSet.setlike_rbset
                               FStarC_Class_Ord.ord_string)) token) in
                  [uu___6])
           | uu___5 -> [] in
         add_assumption_with_triggers triggers1
     | FStarC_SMTEncoding_Term.App
         (FStarC_SMTEncoding_Term.Var "Valid", term::[]) ->
         let uu___ = let uu___1 = free_top_level_names term in [uu___1] in
         add_assumption_with_triggers uu___
     | FStarC_SMTEncoding_Term.App
         (FStarC_SMTEncoding_Term.Var "HasType", term::uu___::[]) ->
         let uu___1 = let uu___2 = free_top_level_names term in [uu___2] in
         add_assumption_with_triggers uu___1
     | FStarC_SMTEncoding_Term.App
         (FStarC_SMTEncoding_Term.Var "IsTotFun", term::[]) ->
         let uu___ = let uu___1 = free_top_level_names term in [uu___1] in
         add_assumption_with_triggers uu___
     | FStarC_SMTEncoding_Term.App
         (FStarC_SMTEncoding_Term.Var "is-Tm_arrow", term::[]) ->
         let uu___ = let uu___1 = free_top_level_names term in [uu___1] in
         add_assumption_with_triggers uu___
     | FStarC_SMTEncoding_Term.App
         (FStarC_SMTEncoding_Term.Eq,
          uu___::{
                   FStarC_SMTEncoding_Term.tm = FStarC_SMTEncoding_Term.App
                     (FStarC_SMTEncoding_Term.Var "Term_constr_id", term::[]);
                   FStarC_SMTEncoding_Term.freevars = uu___1;
                   FStarC_SMTEncoding_Term.rng = uu___2;_}::[])
         ->
         let uu___3 = let uu___4 = free_top_level_names term in [uu___4] in
         add_assumption_with_triggers uu___3
     | FStarC_SMTEncoding_Term.App (FStarC_SMTEncoding_Term.And, tms) ->
         let t1 = FStarC_List.collect triggers_of_term tms in
         add_assumption_with_triggers t1
     | FStarC_SMTEncoding_Term.App (FStarC_SMTEncoding_Term.Eq, t0::t1::[])
         when
         FStarC_Util.starts_with a.FStarC_SMTEncoding_Term.assumption_name
           "equation_"
         ->
         let t01 = free_top_level_names t0 in
         add_assumption_with_triggers [t01]
     | FStarC_SMTEncoding_Term.App (FStarC_SMTEncoding_Term.Iff, t0::t1::[])
         ->
         (match ((t0.FStarC_SMTEncoding_Term.tm),
                  (t1.FStarC_SMTEncoding_Term.tm))
          with
          | (FStarC_SMTEncoding_Term.App
             (FStarC_SMTEncoding_Term.Var "Valid",
              {
                FStarC_SMTEncoding_Term.tm = FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.Var "Prims.hasEq", _u::lhs::[]);
                FStarC_SMTEncoding_Term.freevars = uu___;
                FStarC_SMTEncoding_Term.rng = uu___1;_}::[]),
             FStarC_SMTEncoding_Term.App
             (FStarC_SMTEncoding_Term.Var "Valid",
              {
                FStarC_SMTEncoding_Term.tm = FStarC_SMTEncoding_Term.App
                  (FStarC_SMTEncoding_Term.Var "Prims.hasEq", _v::rhs::[]);
                FStarC_SMTEncoding_Term.freevars = uu___2;
                FStarC_SMTEncoding_Term.rng = uu___3;_}::[]))
              ->
              let triggers1 = free_top_level_names lhs in
              add_assumption_with_triggers [triggers1]
          | uu___ ->
              let t01 = free_top_level_names t0 in
              let t11 = free_top_level_names t1 in
              add_assumption_with_triggers [t01; t11])
     | FStarC_SMTEncoding_Term.App (FStarC_SMTEncoding_Term.Eq, t0::t1::[])
         ->
         let t01 = free_top_level_names t0 in
         let t11 = free_top_level_names t1 in
         add_assumption_with_triggers [t01; t11]
     | FStarC_SMTEncoding_Term.App (FStarC_SMTEncoding_Term.TrueOp, uu___) ->
         p
     | uu___ ->
         let uu___1 = no_ambients () in
         if uu___1
         then
           {
             defs_and_decls = (p.defs_and_decls);
             defs_and_decls_map = (p.defs_and_decls_map);
             macro_freenames = (p.macro_freenames);
             trigger_to_assumption = (p.trigger_to_assumption);
             assumption_to_triggers = (p.assumption_to_triggers);
             assumption_name_map = (p.assumption_name_map);
             ambients = (p.ambients);
             extra_roots = (p.extra_roots);
             pruned_ambients = ((a.FStarC_SMTEncoding_Term.assumption_name)
               :: (p.pruned_ambients))
           }
         else
           {
             defs_and_decls = (p.defs_and_decls);
             defs_and_decls_map = (p.defs_and_decls_map);
             macro_freenames = (p.macro_freenames);
             trigger_to_assumption = (p.trigger_to_assumption);
             assumption_to_triggers = (p.assumption_to_triggers);
             assumption_name_map = (p.assumption_name_map);
             ambients = ((a.FStarC_SMTEncoding_Term.assumption_name) ::
               (p.ambients));
             extra_roots = (p.extra_roots);
             pruned_ambients = (p.pruned_ambients)
           })
let add_assumption_to_triggers (a : FStarC_SMTEncoding_Term.assumption)
  (p : pruning_state) (trigs : triggers_set) : pruning_state=
  let p1 =
    let uu___ =
      FStarC_PSMap.add p.assumption_name_map
        a.FStarC_SMTEncoding_Term.assumption_name
        (FStarC_SMTEncoding_Term.Assume a) in
    {
      defs_and_decls = (p.defs_and_decls);
      defs_and_decls_map = (p.defs_and_decls_map);
      macro_freenames = (p.macro_freenames);
      trigger_to_assumption = (p.trigger_to_assumption);
      assumption_to_triggers = (p.assumption_to_triggers);
      assumption_name_map = uu___;
      ambients = (p.ambients);
      extra_roots = (p.extra_roots);
      pruned_ambients = (p.pruned_ambients)
    } in
  match trigs with
  | [] -> maybe_add_ambient a p1
  | uu___ ->
      let uu___1 =
        FStarC_PSMap.add p1.assumption_to_triggers
          a.FStarC_SMTEncoding_Term.assumption_name
          (mk_remaining_triggers trigs) in
      {
        defs_and_decls = (p1.defs_and_decls);
        defs_and_decls_map = (p1.defs_and_decls_map);
        macro_freenames = (p1.macro_freenames);
        trigger_to_assumption = (p1.trigger_to_assumption);
        assumption_to_triggers = uu___1;
        assumption_name_map = (p1.assumption_name_map);
        ambients = (p1.ambients);
        extra_roots = (p1.extra_roots);
        pruned_ambients = (p1.pruned_ambients)
      }
let trigger_reached (p : pruning_state) (trig : Prims.string) :
  pruning_state=
  let uu___ = FStarC_PSMap.remove p.trigger_to_assumption trig in
  {
    defs_and_decls = (p.defs_and_decls);
    defs_and_decls_map = (p.defs_and_decls_map);
    macro_freenames = (p.macro_freenames);
    trigger_to_assumption = uu___;
    assumption_to_triggers = (p.assumption_to_triggers);
    assumption_name_map = (p.assumption_name_map);
    ambients = (p.ambients);
    extra_roots = (p.extra_roots);
    pruned_ambients = (p.pruned_ambients)
  }
let remove_trigger_for_assumption (p : pruning_state) (trig : sym)
  (aname : Prims.string) : (pruning_state * Prims.bool * sym Prims.list)=
  let uu___ = FStarC_PSMap.try_find p.assumption_to_triggers aname in
  match uu___ with
  | FStar_Pervasives_Native.None -> (p, false, [])
  | FStar_Pervasives_Native.Some l ->
      let l1 =
        let uu___1 =
          FStarC_List.map
            (fun uu___2 ->
               (fun ts ->
                  Obj.magic
                    (FStarC_Class_Setlike.remove ()
                       (Obj.magic
                          (FStarC_RBSet.setlike_rbset
                             FStarC_Class_Ord.ord_string)) trig.sym_name
                       (Obj.magic ts))) uu___2) l.remaining_triggers in
        {
          remaining_triggers = uu___1;
          already_triggered = (trig :: (l.already_triggered))
        } in
      let eligible =
        FStarC_Util.for_some
          (fun uu___1 ->
             (Obj.magic
                (FStarC_Class_Setlike.is_empty ()
                   (Obj.magic
                      (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string))))
               uu___1) l1.remaining_triggers in
      let uu___1 =
        let uu___2 = FStarC_PSMap.add p.assumption_to_triggers aname l1 in
        {
          defs_and_decls = (p.defs_and_decls);
          defs_and_decls_map = (p.defs_and_decls_map);
          macro_freenames = (p.macro_freenames);
          trigger_to_assumption = (p.trigger_to_assumption);
          assumption_to_triggers = uu___2;
          assumption_name_map = (p.assumption_name_map);
          ambients = (p.ambients);
          extra_roots = (p.extra_roots);
          pruned_ambients = (p.pruned_ambients)
        } in
      (uu___1, eligible, (l1.already_triggered))
let rec assumptions_of_decl (d : FStarC_SMTEncoding_Term.decl) :
  FStarC_SMTEncoding_Term.assumption Prims.list=
  match d with
  | FStarC_SMTEncoding_Term.Assume a -> [a]
  | FStarC_SMTEncoding_Term.Module (uu___, ds) ->
      FStarC_List.collect assumptions_of_decl ds
  | d1 -> []
let rec add_decl (d : FStarC_SMTEncoding_Term.decl) (p : pruning_state) :
  pruning_state=
  match d with
  | FStarC_SMTEncoding_Term.Assume a ->
      let triggers1 =
        triggers_of_term a.FStarC_SMTEncoding_Term.assumption_term in
      let p1 =
        let uu___ =
          FStarC_List.map
            (fun uu___1 ->
               (Obj.magic
                  (FStarC_Class_Setlike.elems ()
                     (Obj.magic
                        (FStarC_RBSet.setlike_rbset
                           FStarC_Class_Ord.ord_string)))) uu___1) triggers1 in
        FStarC_List.fold_left
          (FStarC_List.fold_left (add_trigger_to_assumption a)) p uu___ in
      add_assumption_to_triggers a p1 triggers1
  | FStarC_SMTEncoding_Term.Module (uu___, ds) ->
      FStarC_List.fold_left (fun p1 d1 -> add_decl d1 p1) p ds
  | FStarC_SMTEncoding_Term.DefineFun (macro, uu___, uu___1, body, uu___2) ->
      let free_names =
        let uu___3 = free_top_level_names body in
        FStarC_Class_Setlike.elems ()
          (Obj.magic (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string))
          (Obj.magic uu___3) in
      let uu___3 = FStarC_PSMap.add p.defs_and_decls_map macro d in
      let uu___4 = FStarC_PSMap.add p.macro_freenames macro free_names in
      {
        defs_and_decls = (d :: (p.defs_and_decls));
        defs_and_decls_map = uu___3;
        macro_freenames = uu___4;
        trigger_to_assumption = (p.trigger_to_assumption);
        assumption_to_triggers = (p.assumption_to_triggers);
        assumption_name_map = (p.assumption_name_map);
        ambients = (p.ambients);
        extra_roots = (p.extra_roots);
        pruned_ambients = (p.pruned_ambients)
      }
  | FStarC_SMTEncoding_Term.DeclFun (name, uu___, uu___1, uu___2) ->
      let uu___3 = FStarC_PSMap.add p.defs_and_decls_map name d in
      {
        defs_and_decls = (d :: (p.defs_and_decls));
        defs_and_decls_map = uu___3;
        macro_freenames = (p.macro_freenames);
        trigger_to_assumption = (p.trigger_to_assumption);
        assumption_to_triggers = (p.assumption_to_triggers);
        assumption_name_map = (p.assumption_name_map);
        ambients = (p.ambients);
        extra_roots = (p.extra_roots);
        pruned_ambients = (p.pruned_ambients)
      }
  | uu___ -> p
let add_decls (ds : FStarC_SMTEncoding_Term.decl Prims.list)
  (p : pruning_state) : pruning_state=
  FStarC_List.fold_left (fun p1 d -> add_decl d p1) p ds
type triggered_assumption =
  {
  assumption: FStarC_SMTEncoding_Term.assumption ;
  triggered_by: sym Prims.list }
let __proj__Mktriggered_assumption__item__assumption
  (projectee : triggered_assumption) : FStarC_SMTEncoding_Term.assumption=
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
          let uu___ =
            let uu___1 = trigger_reached ctxt1.p x.sym_name in
            { p = uu___1; reached = (ctxt1.reached) } in
          Obj.magic (put uu___)) uu___)
let find_assumptions_waiting_on_trigger (uu___ : sym) :
  FStarC_SMTEncoding_Term.assumption Prims.list st=
  (fun x ->
     Obj.magic
       (FStarC_Class_Monad.op_let_Bang st_monad () () (Obj.magic get)
          (fun uu___ ->
             (fun ctxt1 ->
                let ctxt1 = Obj.magic ctxt1 in
                let uu___ =
                  FStarC_PSMap.try_find (ctxt1.p).trigger_to_assumption
                    x.sym_name in
                match uu___ with
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
            let uu___1 =
              FStarC_PSMap.remove (ctxt1.p).assumption_to_triggers aname in
            {
              defs_and_decls = (uu___.defs_and_decls);
              defs_and_decls_map = (uu___.defs_and_decls_map);
              macro_freenames = (uu___.macro_freenames);
              trigger_to_assumption = (uu___.trigger_to_assumption);
              assumption_to_triggers = uu___1;
              assumption_name_map = (uu___.assumption_name_map);
              ambients = (uu___.ambients);
              extra_roots = (uu___.extra_roots);
              pruned_ambients = (uu___.pruned_ambients)
            } in
          let uu___ =
            let uu___1 =
              Obj.magic
                (FStarC_Class_Setlike.add ()
                   (Obj.magic
                      (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string))
                   aname (Obj.magic ctxt1.reached)) in
            { p = (ctxt1.p); reached = uu___1 } in
          Obj.magic (put uu___)) uu___)
let remove_trigger_for (uu___1 : sym)
  (uu___ : FStarC_SMTEncoding_Term.assumption) :
  (Prims.bool * sym Prims.list) st=
  (fun trig a ->
     Obj.magic
       (FStarC_Class_Monad.op_let_Bang st_monad () () (Obj.magic get)
          (fun uu___ ->
             (fun ctxt1 ->
                let ctxt1 = Obj.magic ctxt1 in
                let uu___ =
                  remove_trigger_for_assumption ctxt1.p trig
                    a.FStarC_SMTEncoding_Term.assumption_name in
                match uu___ with
                | (p, eligible, already_triggered) ->
                    let uu___1 = put { p; reached = (ctxt1.reached) } in
                    Obj.magic
                      (FStarC_Class_Monad.op_let_Bang st_monad () () uu___1
                         (fun uu___2 ->
                            (fun uu___2 ->
                               let uu___2 = Obj.magic uu___2 in
                               Obj.magic
                                 (FStarC_Class_Monad.return st_monad ()
                                    (Obj.magic (eligible, already_triggered))))
                              uu___2))) uu___))) uu___1 uu___
let already_reached (uu___ : Prims.string) : Prims.bool st=
  (fun aname ->
     Obj.magic
       (FStarC_Class_Monad.op_let_Bang st_monad () () (Obj.magic get)
          (fun uu___ ->
             (fun ctxt1 ->
                let ctxt1 = Obj.magic ctxt1 in
                let uu___ =
                  FStarC_Class_Setlike.mem ()
                    (Obj.magic
                       (FStarC_RBSet.setlike_rbset
                          FStarC_Class_Ord.ord_string)) aname
                    (Obj.magic ctxt1.reached) in
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
let rec scan (ds : FStarC_SMTEncoding_Term.assumption Prims.list) : unit st=
  FStarC_Class_Monad.op_let_Bang st_monad () () (Obj.magic get)
    (fun uu___ ->
       (fun ctxt1 ->
          let ctxt1 = Obj.magic ctxt1 in
          let mk_sym assumption_name1 l =
            { sym_name = l; sym_provenance = assumption_name1 } in
          let macro_expand s =
            let uu___ =
              FStarC_PSMap.try_find (ctxt1.p).macro_freenames s.sym_name in
            match uu___ with
            | FStar_Pervasives_Native.None -> [s]
            | FStar_Pervasives_Native.Some l ->
                let uu___1 = FStarC_List.map (mk_sym s.sym_provenance) l in s
                  :: uu___1 in
          let new_syms =
            FStarC_List.collect
              (fun a ->
                 let uu___ =
                   let uu___1 =
                     let uu___2 = assumption_free_names a in
                     FStarC_Class_Setlike.elems ()
                       (Obj.magic
                          (FStarC_RBSet.setlike_rbset
                             FStarC_Class_Ord.ord_string)) (Obj.magic uu___2) in
                   FStarC_List.map
                     (mk_sym a.FStarC_SMTEncoding_Term.assumption_name)
                     uu___1 in
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
                                          already_reached
                                            assumption.FStarC_SMTEncoding_Term.assumption_name in
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
                                                     (let uu___6 =
                                                        reached_assumption
                                                          assumption.FStarC_SMTEncoding_Term.assumption_name in
                                                      Obj.magic
                                                        (FStarC_Class_Monad.op_let_Bang
                                                           st_monad () ()
                                                           uu___6
                                                           (fun uu___7 ->
                                                              (fun uu___7 ->
                                                                 let uu___7 =
                                                                   Obj.magic
                                                                    uu___7 in
                                                                 Obj.magic
                                                                   (FStarC_Class_Monad.return
                                                                    st_monad
                                                                    ()
                                                                    (Obj.magic
                                                                    (assumption
                                                                    :: acc))))
                                                                uu___7))))
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
    let uu___ = FStarC_PSMap.try_find (ctxt1.p).assumption_to_triggers name in
    match uu___ with
    | FStar_Pervasives_Native.None ->
        FStarC_Format.fmt1 "%s (included but not found in map)" name
    | FStar_Pervasives_Native.Some l ->
        let uu___1 =
          FStarC_Class_Show.show (FStarC_Class_Show.show_list showable_sym)
            l.already_triggered in
        FStarC_Format.fmt2 "%s {triggered by %s}" name uu___1 in
  let uu___ = FStarC_List.map print_one names in
  FStarC_String.concat "\n\t" uu___
let name_of_decl (d : FStarC_SMTEncoding_Term.decl) : Prims.string=
  match d with
  | FStarC_SMTEncoding_Term.Assume a ->
      a.FStarC_SMTEncoding_Term.assumption_name
  | FStarC_SMTEncoding_Term.DeclFun (a, uu___, uu___1, uu___2) -> a
  | FStarC_SMTEncoding_Term.DefineFun (a, uu___, uu___1, uu___2, uu___3) -> a
  | uu___ -> "<none>"
let prune (p : pruning_state)
  (roots0 : FStarC_SMTEncoding_Term.decl Prims.list) :
  FStarC_SMTEncoding_Term.decl Prims.list=
  let roots = FStarC_List.collect assumptions_of_decl roots0 in
  let init1 =
    let uu___ =
      Obj.magic
        (FStarC_Class_Setlike.empty ()
           (Obj.magic
              (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string)) ()) in
    { p; reached = uu___ } in
  let roots1 =
    let uu___ = no_ambients () in
    if uu___ then roots else FStar_List_Tot_Base.op_At roots p.extra_roots in
  let mk_triggered_assumption assumption = { assumption; triggered_by = [] } in
  let uu___ = let uu___1 = scan roots1 in uu___1 init1 in
  match uu___ with
  | (uu___1, ctxt1) ->
      let reached_names =
        FStarC_Class_Setlike.elems ()
          (Obj.magic (FStarC_RBSet.setlike_rbset FStarC_Class_Ord.ord_string))
          (Obj.magic ctxt1.reached) in
      ((let uu___3 = no_ambients () in
        if uu___3
        then
          debug
            (fun uu___4 ->
               let uu___5 =
                 let uu___6 =
                   scan (FStar_List_Tot_Base.op_At roots1 p.extra_roots) in
                 uu___6 init1 in
               match uu___5 with
               | (uu___6, ctxt') ->
                   let extra_reached =
                     let uu___7 =
                       Obj.magic
                         (FStarC_Class_Setlike.diff ()
                            (Obj.magic
                               (FStarC_RBSet.setlike_rbset
                                  FStarC_Class_Ord.ord_string))
                            (Obj.magic ctxt'.reached)
                            (Obj.magic ctxt1.reached)) in
                     FStarC_Class_Setlike.elems ()
                       (Obj.magic
                          (FStarC_RBSet.setlike_rbset
                             FStarC_Class_Ord.ord_string)) (Obj.magic uu___7) in
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
               let uu___3 =
                 FStarC_PSMap.try_find (ctxt1.p).assumption_name_map name in
               match uu___3 with
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
             Prims.op_Negation uu___5 in
           if uu___4
           then []
           else
             (let uu___6 =
                let uu___7 =
                  let uu___8 =
                    Obj.magic
                      (FStarC_Class_Setlike.empty ()
                         (Obj.magic
                            (FStarC_RBSet.setlike_rbset
                               FStarC_Class_Ord.ord_string)) ()) in
                  (uu___8, []) in
                FStarC_List.fold_left
                  (fun uu___8 a ->
                     match uu___8 with
                     | (included_decl_names, defs_and_decls) ->
                         (match a with
                          | FStarC_SMTEncoding_Term.Assume a1 ->
                              let free_names = assumption_free_names a1 in
                              let uu___9 =
                                FStarC_Class_Setlike.elems ()
                                  (Obj.magic
                                     (FStarC_RBSet.setlike_rbset
                                        FStarC_Class_Ord.ord_string))
                                  (Obj.magic free_names) in
                              FStarC_List.fold_left
                                (fun uu___10 name ->
                                   match uu___10 with
                                   | (included_decl_names1, defs_and_decls1)
                                       ->
                                       let uu___11 =
                                         FStarC_Class_Setlike.mem ()
                                           (Obj.magic
                                              (FStarC_RBSet.setlike_rbset
                                                 FStarC_Class_Ord.ord_string))
                                           name
                                           (Obj.magic included_decl_names1) in
                                       if uu___11
                                       then
                                         (included_decl_names1,
                                           defs_and_decls1)
                                       else
                                         (let uu___13 =
                                            FStarC_PSMap.try_find
                                              p.defs_and_decls_map name in
                                          match uu___13 with
                                          | FStar_Pervasives_Native.None ->
                                              (included_decl_names1,
                                                defs_and_decls1)
                                          | FStar_Pervasives_Native.Some d ->
                                              let uu___14 =
                                                Obj.magic
                                                  (FStarC_Class_Setlike.add
                                                     ()
                                                     (Obj.magic
                                                        (FStarC_RBSet.setlike_rbset
                                                           FStarC_Class_Ord.ord_string))
                                                     name
                                                     (Obj.magic
                                                        included_decl_names1)) in
                                              (uu___14, (d ::
                                                defs_and_decls1))))
                                (included_decl_names, defs_and_decls) uu___9
                          | uu___9 -> (included_decl_names, defs_and_decls)))
                  uu___7
                  (FStar_List_Tot_Base.op_At reached_assumptions roots0) in
              match uu___6 with
              | (uu___7, defs_and_decls) ->
                  let uu___8 =
                    FStarC_List.partition
                      FStarC_SMTEncoding_Term.uu___is_DeclFun defs_and_decls in
                  (match uu___8 with
                   | (decls, defs) -> FStar_List_Tot_Base.op_At defs decls)) in
         let print_assumption a =
           let uu___4 =
             FStarC_Class_Show.show FStarC_Class_Show.showable_string
               a.FStarC_SMTEncoding_Term.assumption_name in
           let uu___5 =
             let uu___6 = assumption_free_names a in
             FStarC_Class_Show.show
               (FStarC_RBSet.showable_rbset FStarC_Class_Show.showable_string)
               uu___6 in
           FStarC_Format.fmt2 "{name=%s; freevars={%s}}" uu___4 uu___5 in
         debug
           (fun uu___5 ->
              let uu___6 =
                let uu___7 = FStarC_List.map print_assumption roots1 in
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
         FStar_List_Tot_Base.op_At reached_assumptions decls_and_defs)))
