open Prims
type using_facts_from_setting =
  (Prims.string Prims.list * Prims.bool) Prims.list
type lazy_decls =
  {
  ld_sums: FStarC_SMTEncoding_Pruning.decl_summary Prims.list ;
  ld_resolve:
    Prims.string ->
      FStarC_SMTEncoding_Term.decl FStar_Pervasives_Native.option
    ;
  ld_force: unit -> FStarC_SMTEncoding_Term.decl Prims.list }
let __proj__Mklazy_decls__item__ld_sums (projectee : lazy_decls) :
  FStarC_SMTEncoding_Pruning.decl_summary Prims.list=
  match projectee with | { ld_sums; ld_resolve; ld_force;_} -> ld_sums
let __proj__Mklazy_decls__item__ld_resolve (projectee : lazy_decls) :
  Prims.string -> FStarC_SMTEncoding_Term.decl FStar_Pervasives_Native.option=
  match projectee with | { ld_sums; ld_resolve; ld_force;_} -> ld_resolve
let __proj__Mklazy_decls__item__ld_force (projectee : lazy_decls) :
  unit -> FStarC_SMTEncoding_Term.decl Prims.list=
  match projectee with | { ld_sums; ld_resolve; ld_force;_} -> ld_force
type decl_name_set = Prims.bool FStarC_PSMap.t
let empty_decl_names : Prims.bool FStarC_PSMap.t= FStarC_PSMap.empty ()
let decl_names_contains (x : Prims.string) (s : decl_name_set) : Prims.bool=
  match FStarC_PSMap.try_find s x with
  | FStar_Pervasives_Native.Some v -> true
  | uu___ -> false
let add_name (x : Prims.string) (s : decl_name_set) :
  Prims.bool FStarC_PSMap.t= FStarC_PSMap.add s x true
type given_decls =
  | Given of FStarC_SMTEncoding_Term.decl Prims.list 
  | Given_lazy of lazy_decls 
let uu___is_Given (projectee : given_decls) : Prims.bool=
  match projectee with | Given _0 -> true | uu___ -> false
let __proj__Given__item___0 (projectee : given_decls) :
  FStarC_SMTEncoding_Term.decl Prims.list=
  match projectee with | Given _0 -> _0
let uu___is_Given_lazy (projectee : given_decls) : Prims.bool=
  match projectee with | Given_lazy _0 -> true | uu___ -> false
let __proj__Given_lazy__item___0 (projectee : given_decls) : lazy_decls=
  match projectee with | Given_lazy _0 -> _0
let force_given (g : given_decls) : FStarC_SMTEncoding_Term.decl Prims.list=
  match g with | Given ds -> ds | Given_lazy ld -> ld.ld_force ()
type decls_at_level =
  {
  pruning_state: FStarC_SMTEncoding_Pruning.pruning_state ;
  given_decl_names: decl_name_set ;
  all_decls_at_level_rev: given_decls Prims.list ;
  given_some_decls: Prims.bool ;
  to_flush_rev: FStarC_SMTEncoding_Term.decl Prims.list Prims.list ;
  pruning_roots:
    FStarC_SMTEncoding_Term.decl Prims.list FStar_Pervasives_Native.option }
let __proj__Mkdecls_at_level__item__pruning_state
  (projectee : decls_at_level) : FStarC_SMTEncoding_Pruning.pruning_state=
  match projectee with
  | { pruning_state; given_decl_names; all_decls_at_level_rev;
      given_some_decls; to_flush_rev; pruning_roots;_} -> pruning_state
let __proj__Mkdecls_at_level__item__given_decl_names
  (projectee : decls_at_level) : decl_name_set=
  match projectee with
  | { pruning_state; given_decl_names; all_decls_at_level_rev;
      given_some_decls; to_flush_rev; pruning_roots;_} -> given_decl_names
let __proj__Mkdecls_at_level__item__all_decls_at_level_rev
  (projectee : decls_at_level) : given_decls Prims.list=
  match projectee with
  | { pruning_state; given_decl_names; all_decls_at_level_rev;
      given_some_decls; to_flush_rev; pruning_roots;_} ->
      all_decls_at_level_rev
let __proj__Mkdecls_at_level__item__given_some_decls
  (projectee : decls_at_level) : Prims.bool=
  match projectee with
  | { pruning_state; given_decl_names; all_decls_at_level_rev;
      given_some_decls; to_flush_rev; pruning_roots;_} -> given_some_decls
let __proj__Mkdecls_at_level__item__to_flush_rev (projectee : decls_at_level)
  : FStarC_SMTEncoding_Term.decl Prims.list Prims.list=
  match projectee with
  | { pruning_state; given_decl_names; all_decls_at_level_rev;
      given_some_decls; to_flush_rev; pruning_roots;_} -> to_flush_rev
let __proj__Mkdecls_at_level__item__pruning_roots
  (projectee : decls_at_level) :
  FStarC_SMTEncoding_Term.decl Prims.list FStar_Pervasives_Native.option=
  match projectee with
  | { pruning_state; given_decl_names; all_decls_at_level_rev;
      given_some_decls; to_flush_rev; pruning_roots;_} -> pruning_roots
let init_given_decls_at_level : decls_at_level=
  {
    pruning_state = FStarC_SMTEncoding_Pruning.init;
    given_decl_names = empty_decl_names;
    all_decls_at_level_rev = [];
    given_some_decls = false;
    to_flush_rev = [];
    pruning_roots = FStar_Pervasives_Native.None
  }
type solver_state =
  {
  levels: decls_at_level Prims.list ;
  pending_flushes_rev: FStarC_SMTEncoding_Term.decl Prims.list ;
  using_facts_from: using_facts_from_setting FStar_Pervasives_Native.option ;
  retain_assumptions: decl_name_set }
let __proj__Mksolver_state__item__levels (projectee : solver_state) :
  decls_at_level Prims.list=
  match projectee with
  | { levels; pending_flushes_rev; using_facts_from; retain_assumptions;_} ->
      levels
let __proj__Mksolver_state__item__pending_flushes_rev
  (projectee : solver_state) : FStarC_SMTEncoding_Term.decl Prims.list=
  match projectee with
  | { levels; pending_flushes_rev; using_facts_from; retain_assumptions;_} ->
      pending_flushes_rev
let __proj__Mksolver_state__item__using_facts_from (projectee : solver_state)
  : using_facts_from_setting FStar_Pervasives_Native.option=
  match projectee with
  | { levels; pending_flushes_rev; using_facts_from; retain_assumptions;_} ->
      using_facts_from
let __proj__Mksolver_state__item__retain_assumptions
  (projectee : solver_state) : decl_name_set=
  match projectee with
  | { levels; pending_flushes_rev; using_facts_from; retain_assumptions;_} ->
      retain_assumptions
let depth (s : solver_state) : Prims.int= FStarC_List.length s.levels
let solver_state_to_string (s : solver_state) : Prims.string=
  let levels =
    FStarC_List.map
      (fun level ->
         let uu___ =
           FStarC_Class_Show.show FStarC_Class_Show.showable_nat
             (FStarC_List.length level.all_decls_at_level_rev) in
         let uu___1 =
           FStarC_Class_Show.show FStarC_Class_Show.showable_bool
             level.given_some_decls in
         let uu___2 =
           FStarC_Class_Show.show FStarC_Class_Show.showable_nat
             (FStarC_List.length level.to_flush_rev) in
         FStarC_Format.fmt3
           "Level { all_decls=%s; given_decls=%s; to_flush=%s }" uu___ uu___1
           uu___2) s.levels in
  let uu___ =
    FStarC_Class_Show.show
      (FStarC_Class_Show.show_list FStarC_Class_Show.showable_string) levels in
  let uu___1 =
    FStarC_Class_Show.show FStarC_Class_Show.showable_nat
      (FStarC_List.length s.pending_flushes_rev) in
  FStarC_Format.fmt2 "Solver state { levels=%s; pending_flushes=%s }" uu___
    uu___1
let showable_solver_state : solver_state FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = solver_state_to_string }
let debug (msg : Prims.string) (s0 : solver_state) (s1 : solver_state) :
  unit=
  let uu___ = FStarC_Options_Ext.enabled "debug_solver_state" in
  if uu___
  then
    let uu___1 = solver_state_to_string s0 in
    let uu___2 = solver_state_to_string s1 in
    FStarC_Format.print3 "Debug (%s):{\n\t before=%s\n\t after=%s\n}" msg
      uu___1 uu___2
  else ()
let peek (s : solver_state) : (decls_at_level * decls_at_level Prims.list)=
  match s.levels with
  | [] -> FStarC_Effect.failwith "Solver state cannot have an empty stack"
  | hd::tl -> (hd, tl)
let replace_head (hd : decls_at_level) (s : solver_state) : solver_state=
  {
    levels = (hd :: (FStarC_List.tl s.levels));
    pending_flushes_rev = (s.pending_flushes_rev);
    using_facts_from = (s.using_facts_from);
    retain_assumptions = (s.retain_assumptions)
  }
let init (uu___ : unit) : solver_state=
  let uu___1 =
    let uu___2 = FStarC_Options.using_facts_from () in
    FStar_Pervasives_Native.Some uu___2 in
  {
    levels = [init_given_decls_at_level];
    pending_flushes_rev = [];
    using_facts_from = uu___1;
    retain_assumptions = empty_decl_names
  }
let push (s : solver_state) : solver_state=
  let uu___ = peek s in
  match uu___ with
  | (hd, uu___1) ->
      let push1 = FStarC_SMTEncoding_Term.Push (FStarC_List.length s.levels) in
      let next =
        {
          pruning_state = (hd.pruning_state);
          given_decl_names = (hd.given_decl_names);
          all_decls_at_level_rev = [];
          given_some_decls = false;
          to_flush_rev = [[push1]];
          pruning_roots = FStar_Pervasives_Native.None
        } in
      {
        levels = (next :: (s.levels));
        pending_flushes_rev = (s.pending_flushes_rev);
        using_facts_from = (s.using_facts_from);
        retain_assumptions = (s.retain_assumptions)
      }
let pop (s : solver_state) : solver_state=
  let uu___ = peek s in
  match uu___ with
  | (hd, tl) ->
      (if (match tl with | [] -> true | uu___2 -> false)
       then FStarC_Effect.failwith "Solver state cannot have an empty stack"
       else ();
       (let s1 =
          if Prims.not hd.given_some_decls
          then
            {
              levels = tl;
              pending_flushes_rev = (s.pending_flushes_rev);
              using_facts_from = (s.using_facts_from);
              retain_assumptions = (s.retain_assumptions)
            }
          else
            {
              levels = tl;
              pending_flushes_rev =
                ((FStarC_SMTEncoding_Term.Pop (FStarC_List.length tl)) ::
                (s.pending_flushes_rev));
              using_facts_from = (s.using_facts_from);
              retain_assumptions = (s.retain_assumptions)
            } in
        s1))
let filter_using_facts_from
  (using_facts_from :
    using_facts_from_setting FStar_Pervasives_Native.option)
  (retain_assumptions : decl_name_set)
  (already_given_decl : Prims.string -> Prims.bool)
  (ds : FStarC_SMTEncoding_Term.decl Prims.list) :
  FStarC_SMTEncoding_Term.decl Prims.list=
  match using_facts_from with
  | FStar_Pervasives_Native.None -> ds
  | FStar_Pervasives_Native.Some (([], true)::[]) -> ds
  | FStar_Pervasives_Native.Some using_facts_from1 ->
      let keep_assumption a =
        match a.FStarC_SMTEncoding_Term.assumption_fact_ids with
        | [] -> true
        | uu___ ->
            if
              decl_names_contains a.FStarC_SMTEncoding_Term.assumption_name
                retain_assumptions
            then true
            else
              FStarC_Util.for_some
                (fun uu___1 ->
                   match uu___1 with
                   | FStarC_SMTEncoding_Term.Name lid ->
                       FStarC_TypeChecker_Env.should_enc_lid
                         using_facts_from1 lid
                   | uu___2 -> false)
                a.FStarC_SMTEncoding_Term.assumption_fact_ids in
      let already_given_map = FStarC_SMap.create (Prims.of_int 1000) in
      let add_assumption a =
        FStarC_SMap.add already_given_map
          a.FStarC_SMTEncoding_Term.assumption_name true in
      let already_given a =
        let uu___ =
          let uu___1 =
            FStarC_SMap.try_find already_given_map
              a.FStarC_SMTEncoding_Term.assumption_name in
          match uu___1 with
          | FStar_Pervasives_Native.Some v -> true
          | uu___2 -> false in
        if uu___
        then true
        else already_given_decl a.FStarC_SMTEncoding_Term.assumption_name in
      let map_decl d =
        match d with
        | FStarC_SMTEncoding_Term.Assume a ->
            let uu___ =
              let uu___1 = keep_assumption a in
              if uu___1
              then let uu___2 = already_given a in Prims.not uu___2
              else false in
            if uu___ then (add_assumption a; [d]) else []
        | uu___ -> [d] in
      let ds' = FStarC_List.collect map_decl ds in
      ((let uu___1 =
          let uu___2 = FStarC_Options_Ext.get "debug_using_facts_from" in
          uu___2 <> "" in
        if uu___1
        then
          let orig_n = FStarC_List.length ds in
          let new_n = FStarC_List.length ds' in
          (if orig_n <> new_n
           then
             let uu___2 =
               FStarC_Class_Show.show FStarC_Class_Show.showable_nat orig_n in
             let uu___3 =
               let uu___4 =
                 FStarC_List.map FStarC_SMTEncoding_Term.decl_to_string_short
                   ds in
               FStarC_Class_Show.show
                 (FStarC_Class_Show.show_list
                    FStarC_Class_Show.showable_string) uu___4 in
             let uu___4 =
               FStarC_Class_Show.show FStarC_Class_Show.showable_nat new_n in
             let uu___5 =
               let uu___6 =
                 FStarC_List.map FStarC_SMTEncoding_Term.decl_to_string_short
                   ds' in
               FStarC_Class_Show.show
                 (FStarC_Class_Show.show_list
                    FStarC_Class_Show.showable_string) uu___6 in
             FStarC_Format.print4
               "Pruned using facts from:\n\tOriginal (%s): [%s];\n\tPruned (%s): [%s]\n"
               uu___2 uu___3 uu___4 uu___5
           else ())
        else ());
       ds')
let already_given_decl (s : solver_state) (aname : Prims.string) :
  Prims.bool=
  FStarC_Util.for_some
    (fun level -> decl_names_contains aname level.given_decl_names) s.levels
let rec flatten (d : FStarC_SMTEncoding_Term.decl) :
  FStarC_SMTEncoding_Term.decl Prims.list=
  match d with
  | FStarC_SMTEncoding_Term.Module (uu___, ds) ->
      FStarC_List.collect flatten ds
  | uu___ -> [d]
let add_retain_names (names : Prims.string Prims.list Prims.list)
  (s : solver_state) : solver_state=
  let ra =
    FStarC_List.fold_left
      (FStarC_List.fold_left (fun ra1 name -> add_name name ra1))
      s.retain_assumptions names in
  {
    levels = (s.levels);
    pending_flushes_rev = (s.pending_flushes_rev);
    using_facts_from = (s.using_facts_from);
    retain_assumptions = ra
  }
let add_retain_assumptions (ds : FStarC_SMTEncoding_Term.decl Prims.list)
  (s : solver_state) : solver_state=
  let uu___ =
    FStarC_List.collect
      (fun uu___1 ->
         match uu___1 with
         | FStarC_SMTEncoding_Term.RetainAssumptions names -> [names]
         | uu___2 -> []) ds in
  add_retain_names uu___ s
let give_delay_assumptions (resetting : Prims.bool) (g : given_decls)
  (s : solver_state) : solver_state=
  match g with
  | Given_lazy ld when FStarC_Options_Ext.enabled "prune_decls" ->
      let rest =
        FStarC_List.collect
          (fun uu___ ->
             match uu___ with
             | FStarC_SMTEncoding_Pruning.Sum_other d -> [d]
             | uu___1 -> []) ld.ld_sums in
      let uu___ = peek s in
      (match uu___ with
       | (hd, tl) ->
           let hd1 =
             {
               pruning_state = (hd.pruning_state);
               given_decl_names = (hd.given_decl_names);
               all_decls_at_level_rev = (g :: (hd.all_decls_at_level_rev));
               given_some_decls = (hd.given_some_decls);
               to_flush_rev = (rest :: (hd.to_flush_rev));
               pruning_roots = (hd.pruning_roots)
             } in
           if resetting
           then
             {
               levels = (hd1 :: tl);
               pending_flushes_rev = (s.pending_flushes_rev);
               using_facts_from = (s.using_facts_from);
               retain_assumptions = (s.retain_assumptions)
             }
           else
             (let hd2 =
                let uu___1 =
                  FStarC_SMTEncoding_Pruning.add_summaries ld.ld_sums
                    ld.ld_resolve hd1.pruning_state in
                {
                  pruning_state = uu___1;
                  given_decl_names = (hd1.given_decl_names);
                  all_decls_at_level_rev = (hd1.all_decls_at_level_rev);
                  given_some_decls = (hd1.given_some_decls);
                  to_flush_rev = (hd1.to_flush_rev);
                  pruning_roots = (hd1.pruning_roots)
                } in
              let uu___1 =
                FStarC_List.collect
                  (fun uu___2 ->
                     match uu___2 with
                     | FStarC_SMTEncoding_Pruning.Sum_retain names -> [names]
                     | uu___3 -> []) ld.ld_sums in
              add_retain_names uu___1
                {
                  levels = (hd2 :: tl);
                  pending_flushes_rev = (s.pending_flushes_rev);
                  using_facts_from = (s.using_facts_from);
                  retain_assumptions = (s.retain_assumptions)
                }))
  | uu___ ->
      let ds = force_given g in
      let decls = FStarC_List.collect flatten ds in
      let uu___1 =
        FStarC_List.partition FStarC_SMTEncoding_Term.uu___is_Assume decls in
      (match uu___1 with
       | (assumptions, rest) ->
           let uu___2 =
             let uu___3 = FStarC_Options_Ext.enabled "prune_decls" in
             if uu___3
             then
               let uu___4 =
                 FStarC_List.partition
                   (fun d ->
                      (match d with
                       | FStarC_SMTEncoding_Term.DeclFun (_0, _1, _2, _3) ->
                           true
                       | uu___5 -> false) ||
                        (match d with
                         | FStarC_SMTEncoding_Term.DefineFun
                             (_0, _1, _2, _3, _4) -> true
                         | uu___5 -> false)) rest in
               match uu___4 with
               | (decls_and_defs, rest1) ->
                   let uu___5 =
                     FStarC_List.filter
                       (fun d ->
                          Prims.not
                            (((match d with
                               | FStarC_SMTEncoding_Term.Caption _0 -> true
                               | uu___6 -> false) ||
                                (match d with
                                 | FStarC_SMTEncoding_Term.EmptyLine -> true
                                 | uu___6 -> false))
                               ||
                               (match d with
                                | FStarC_SMTEncoding_Term.RetainAssumptions
                                    _0 -> true
                                | uu___6 -> false))) rest1 in
                   (decls_and_defs, uu___5)
             else ([], rest) in
           (match uu___2 with
            | (decls_and_defs, rest1) ->
                let uu___3 = peek s in
                (match uu___3 with
                 | (hd, tl) ->
                     let hd1 =
                       {
                         pruning_state = (hd.pruning_state);
                         given_decl_names = (hd.given_decl_names);
                         all_decls_at_level_rev = (g ::
                           (hd.all_decls_at_level_rev));
                         given_some_decls = (hd.given_some_decls);
                         to_flush_rev = (rest1 :: (hd.to_flush_rev));
                         pruning_roots = (hd.pruning_roots)
                       } in
                     if resetting
                     then
                       {
                         levels = (hd1 :: tl);
                         pending_flushes_rev = (s.pending_flushes_rev);
                         using_facts_from = (s.using_facts_from);
                         retain_assumptions = (s.retain_assumptions)
                       }
                     else
                       (let hd2 =
                          let uu___4 =
                            FStarC_SMTEncoding_Pruning.add_decls decls
                              hd1.pruning_state in
                          {
                            pruning_state = uu___4;
                            given_decl_names = (hd1.given_decl_names);
                            all_decls_at_level_rev =
                              (hd1.all_decls_at_level_rev);
                            given_some_decls = (hd1.given_some_decls);
                            to_flush_rev = (hd1.to_flush_rev);
                            pruning_roots = (hd1.pruning_roots)
                          } in
                        add_retain_assumptions decls
                          {
                            levels = (hd2 :: tl);
                            pending_flushes_rev = (s.pending_flushes_rev);
                            using_facts_from = (s.using_facts_from);
                            retain_assumptions = (s.retain_assumptions)
                          }))))
let give_now (resetting : Prims.bool) (g : given_decls) (s : solver_state) :
  solver_state=
  let ds = force_given g in
  let decls = FStarC_List.collect flatten ds in
  let uu___ = peek s in
  match uu___ with
  | (hd, tl) ->
      let ds_to_flush =
        filter_using_facts_from s.using_facts_from s.retain_assumptions
          (already_given_decl s) decls in
      let given =
        FStarC_List.fold_left
          (fun given1 d ->
             match d with
             | FStarC_SMTEncoding_Term.Assume a ->
                 add_name a.FStarC_SMTEncoding_Term.assumption_name given1
             | uu___1 -> given1) hd.given_decl_names ds_to_flush in
      let hd1 =
        {
          pruning_state = (hd.pruning_state);
          given_decl_names = given;
          all_decls_at_level_rev = (g :: (hd.all_decls_at_level_rev));
          given_some_decls = (hd.given_some_decls);
          to_flush_rev = (ds_to_flush :: (hd.to_flush_rev));
          pruning_roots = (hd.pruning_roots)
        } in
      if resetting
      then
        {
          levels = (hd1 :: tl);
          pending_flushes_rev = (s.pending_flushes_rev);
          using_facts_from = (s.using_facts_from);
          retain_assumptions = (s.retain_assumptions)
        }
      else
        (let hd2 =
           let uu___1 =
             FStarC_SMTEncoding_Pruning.add_decls decls hd1.pruning_state in
           {
             pruning_state = uu___1;
             given_decl_names = (hd1.given_decl_names);
             all_decls_at_level_rev = (hd1.all_decls_at_level_rev);
             given_some_decls = (hd1.given_some_decls);
             to_flush_rev = (hd1.to_flush_rev);
             pruning_roots = (hd1.pruning_roots)
           } in
         add_retain_assumptions decls
           {
             levels = (hd2 :: tl);
             pending_flushes_rev = (s.pending_flushes_rev);
             using_facts_from = (s.using_facts_from);
             retain_assumptions = (s.retain_assumptions)
           })
let give_aux (resetting : Prims.bool) (g : given_decls) (s : solver_state) :
  solver_state=
  let uu___ = FStarC_Options_Ext.enabled "context_pruning" in
  if uu___
  then give_delay_assumptions resetting g s
  else give_now resetting g s
let give (ds : FStarC_SMTEncoding_Term.decl Prims.list) (s : solver_state) :
  solver_state= give_aux false (Given ds) s
let give_lazy (ld : lazy_decls) (s : solver_state) : solver_state=
  give_aux false (Given_lazy ld) s
let reset
  (using_facts_from :
    using_facts_from_setting FStar_Pervasives_Native.option)
  (s : solver_state) : solver_state=
  let s_new = init () in
  let s_new1 =
    {
      levels = (s_new.levels);
      pending_flushes_rev = (s_new.pending_flushes_rev);
      using_facts_from;
      retain_assumptions = (s.retain_assumptions)
    } in
  let set_pruning_roots level s1 =
    let uu___ = peek s1 in
    match uu___ with
    | (hd, tl) ->
        let hd1 =
          {
            pruning_state = (hd.pruning_state);
            given_decl_names = (hd.given_decl_names);
            all_decls_at_level_rev = (hd.all_decls_at_level_rev);
            given_some_decls = (hd.given_some_decls);
            to_flush_rev = (hd.to_flush_rev);
            pruning_roots = (level.pruning_roots)
          } in
        {
          levels = (hd1 :: tl);
          pending_flushes_rev = (s1.pending_flushes_rev);
          using_facts_from = (s1.using_facts_from);
          retain_assumptions = (s1.retain_assumptions)
        } in
  let rebuild_level now level s_new2 =
    let uu___ = peek s_new2 in
    match uu___ with
    | (hd, tl) ->
        let hd1 =
          {
            pruning_state = (level.pruning_state);
            given_decl_names = (hd.given_decl_names);
            all_decls_at_level_rev = (hd.all_decls_at_level_rev);
            given_some_decls = (hd.given_some_decls);
            to_flush_rev = (hd.to_flush_rev);
            pruning_roots = (hd.pruning_roots)
          } in
        let s_new3 =
          {
            levels = (hd1 :: tl);
            pending_flushes_rev = (s_new2.pending_flushes_rev);
            using_facts_from = (s_new2.using_facts_from);
            retain_assumptions = (s_new2.retain_assumptions)
          } in
        let s1 =
          FStarC_List.fold_right
            (if now then give_now true else give_aux true)
            level.all_decls_at_level_rev s_new3 in
        let uu___1 = set_pruning_roots level s1 in
        (uu___1,
          ((match level.pruning_roots with
            | FStar_Pervasives_Native.Some v -> true
            | uu___2 -> false))) in
  let rec rebuild levels s_new2 =
    match levels with
    | last::[] -> rebuild_level false last s_new2
    | level::levels1 ->
        let uu___ = rebuild levels1 s_new2 in
        (match uu___ with
         | (s_new3, now) ->
             let s_new4 = push s_new3 in rebuild_level now level s_new4) in
  let uu___ = rebuild s.levels s_new1 in FStar_Pervasives_Native.fst uu___
let name_of_decl (d : FStarC_SMTEncoding_Term.decl) : Prims.string=
  match d with
  | FStarC_SMTEncoding_Term.Assume a ->
      a.FStarC_SMTEncoding_Term.assumption_name
  | FStarC_SMTEncoding_Term.DeclFun (a, uu___, uu___1, uu___2) -> a
  | FStarC_SMTEncoding_Term.DefineFun (a, uu___, uu___1, uu___2, uu___3) -> a
  | uu___ -> FStarC_Effect.failwith "Expected an assumption"
let decl_rank (d : FStarC_SMTEncoding_Term.decl) : Prims.int=
  match d with
  | FStarC_SMTEncoding_Term.DeclFun (uu___, uu___1, uu___2, uu___3) ->
      Prims.int_zero
  | FStarC_SMTEncoding_Term.DefineFun (uu___, uu___1, uu___2, uu___3, uu___4)
      -> Prims.int_one
  | uu___ -> Prims.of_int 2
let compare_decls (d0 : FStarC_SMTEncoding_Term.decl)
  (d1 : FStarC_SMTEncoding_Term.decl) : Prims.int=
  let r = (decl_rank d0) - (decl_rank d1) in
  if r <> Prims.int_zero
  then r
  else
    (match (d0, d1) with
     | (FStarC_SMTEncoding_Term.DeclFun (a0, uu___, uu___1, uu___2),
        FStarC_SMTEncoding_Term.DeclFun (a1, uu___3, uu___4, uu___5)) ->
         FStarC_Util.compare a0 a1
     | (FStarC_SMTEncoding_Term.DefineFun
        (a0, uu___, uu___1, uu___2, uu___3),
        FStarC_SMTEncoding_Term.DefineFun
        (a1, uu___4, uu___5, uu___6, uu___7)) -> FStarC_Util.compare a0 a1
     | (FStarC_SMTEncoding_Term.Assume
        { FStarC_SMTEncoding_Term.assumption_term = uu___;
          FStarC_SMTEncoding_Term.assumption_caption = uu___1;
          FStarC_SMTEncoding_Term.assumption_name = a0;
          FStarC_SMTEncoding_Term.assumption_fact_ids = uu___2;_},
        FStarC_SMTEncoding_Term.Assume
        { FStarC_SMTEncoding_Term.assumption_term = uu___3;
          FStarC_SMTEncoding_Term.assumption_caption = uu___4;
          FStarC_SMTEncoding_Term.assumption_name = a1;
          FStarC_SMTEncoding_Term.assumption_fact_ids = uu___5;_})
         -> FStarC_Util.compare a0 a1
     | uu___ -> Prims.int_zero)
let prune_level (roots : FStarC_SMTEncoding_Term.decl Prims.list)
  (hd : decls_at_level) (s : solver_state) : decls_at_level=
  let to_give = FStarC_SMTEncoding_Pruning.prune hd.pruning_state roots in
  let uu___ =
    FStarC_List.fold_left
      (fun uu___1 to_give1 ->
         match uu___1 with
         | (decl_name_set1, can_give) ->
             let name = name_of_decl to_give1 in
             if Prims.not (decl_names_contains name decl_name_set1)
             then ((add_name name decl_name_set1), (to_give1 :: can_give))
             else (decl_name_set1, can_give)) ((hd.given_decl_names), [])
      to_give in
  match uu___ with
  | (given_decl_names, can_give) ->
      let can_give1 =
        filter_using_facts_from s.using_facts_from s.retain_assumptions
          (already_given_decl s) can_give in
      let can_give2 = FStarC_List.sortWith compare_decls can_give1 in
      let hd1 =
        {
          pruning_state = (hd.pruning_state);
          given_decl_names;
          all_decls_at_level_rev = (hd.all_decls_at_level_rev);
          given_some_decls = (hd.given_some_decls);
          to_flush_rev = (can_give2 :: (hd.to_flush_rev));
          pruning_roots = (hd.pruning_roots)
        } in
      hd1
let prune_sim (roots : FStarC_SMTEncoding_Term.decl Prims.list)
  (s : solver_state) : Prims.string Prims.list=
  let uu___ = peek s in
  match uu___ with
  | (hd, tl) ->
      let to_give = FStarC_SMTEncoding_Pruning.prune hd.pruning_state roots in
      let can_give =
        filter_using_facts_from s.using_facts_from s.retain_assumptions
          (already_given_decl s) to_give in
      let uu___1 =
        let uu___2 =
          FStarC_List.filter FStarC_SMTEncoding_Term.uu___is_Assume roots in
        FStar_List_Tot_Base.op_At uu___2 can_give in
      FStarC_List.map name_of_decl uu___1
let start_query (msg : Prims.string)
  (roots_to_push : FStarC_SMTEncoding_Term.decl Prims.list)
  (qry : FStarC_SMTEncoding_Term.decl Prims.list) (s : solver_state) :
  solver_state=
  let uu___ = peek s in
  match uu___ with
  | (hd, tl) ->
      let s1 =
        {
          levels =
            ({
               pruning_state = (hd.pruning_state);
               given_decl_names = (hd.given_decl_names);
               all_decls_at_level_rev = (hd.all_decls_at_level_rev);
               given_some_decls = (hd.given_some_decls);
               to_flush_rev = (hd.to_flush_rev);
               pruning_roots =
                 (FStar_Pervasives_Native.Some
                    (FStar_List_Tot_Base.op_At qry roots_to_push))
             } :: tl);
          pending_flushes_rev = (s.pending_flushes_rev);
          using_facts_from = (s.using_facts_from);
          retain_assumptions = (s.retain_assumptions)
        } in
      let s2 = push s1 in
      let s3 = give [FStarC_SMTEncoding_Term.Caption msg] s2 in
      give_now false (Given roots_to_push) s3
let finish_query (msg : Prims.string) (s : solver_state) : solver_state=
  let s1 = give [FStarC_SMTEncoding_Term.Caption msg] s in
  let s2 = pop s1 in
  let uu___ = peek s2 in
  match uu___ with
  | (hd, tl) ->
      {
        levels =
          ({
             pruning_state = (hd.pruning_state);
             given_decl_names = (hd.given_decl_names);
             all_decls_at_level_rev = (hd.all_decls_at_level_rev);
             given_some_decls = (hd.given_some_decls);
             to_flush_rev = (hd.to_flush_rev);
             pruning_roots = FStar_Pervasives_Native.None
           } :: tl);
        pending_flushes_rev = (s2.pending_flushes_rev);
        using_facts_from = (s2.using_facts_from);
        retain_assumptions = (s2.retain_assumptions)
      }
let would_have_pruned (s : solver_state) :
  Prims.string Prims.list FStar_Pervasives_Native.option=
  let uu___ =
    let uu___1 = FStarC_Options_Ext.enabled "context_pruning_sim" in
    Prims.not uu___1 in
  if uu___
  then FStar_Pervasives_Native.None
  else
    (let rec aux levels =
       match levels with
       | [] -> FStar_Pervasives_Native.None
       | level::levels1 ->
           (match level.pruning_roots with
            | FStar_Pervasives_Native.Some roots ->
                let uu___1 = prune_sim roots s in
                FStar_Pervasives_Native.Some uu___1
            | FStar_Pervasives_Native.None -> aux levels1) in
     aux s.levels)
let flush (s : solver_state) :
  (FStarC_SMTEncoding_Term.decl Prims.list * solver_state)=
  let s1 =
    let uu___ = FStarC_Options_Ext.enabled "context_pruning" in
    if uu___
    then
      let rec aux levels =
        match levels with
        | [] -> []
        | level::levels1 ->
            (match level.pruning_roots with
             | FStar_Pervasives_Native.Some roots ->
                 let hd = prune_level roots level s in hd :: levels1
             | FStar_Pervasives_Native.None ->
                 let uu___1 = aux levels1 in level :: uu___1) in
      let uu___1 = aux s.levels in
      {
        levels = uu___1;
        pending_flushes_rev = (s.pending_flushes_rev);
        using_facts_from = (s.using_facts_from);
        retain_assumptions = (s.retain_assumptions)
      }
    else s in
  let to_flush =
    let uu___ =
      let uu___1 =
        FStarC_List.collect (fun level -> level.to_flush_rev) s1.levels in
      FStarC_List.rev uu___1 in
    FStarC_List.flatten uu___ in
  let levels =
    FStarC_List.map
      (fun level ->
         {
           pruning_state = (level.pruning_state);
           given_decl_names = (level.given_decl_names);
           all_decls_at_level_rev = (level.all_decls_at_level_rev);
           given_some_decls =
             (level.given_some_decls ||
                (match level.to_flush_rev with
                 | hd::tl -> true
                 | uu___ -> false));
           to_flush_rev = [];
           pruning_roots = (level.pruning_roots)
         }) s1.levels in
  let s11 =
    {
      levels;
      pending_flushes_rev = [];
      using_facts_from = (s1.using_facts_from);
      retain_assumptions = (s1.retain_assumptions)
    } in
  let flushed =
    FStar_List_Tot_Base.op_At (FStarC_List.rev s1.pending_flushes_rev)
      to_flush in
  (flushed, s11)
let all_decls (s : solver_state) : FStarC_SMTEncoding_Term.decl Prims.list=
  let s1 = reset s.using_facts_from s in
  let uu___ = flush s1 in match uu___ with | (flushed, uu___1) -> flushed
