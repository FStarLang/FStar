open Prims
type using_facts_from_setting =
  (Prims.string Prims.list * Prims.bool) Prims.list
type decl_name_set = Prims.bool FStarC_Compiler_Util.psmap
let (empty_decl_names : Prims.bool FStarC_Compiler_Util.psmap) =
  FStarC_Compiler_Util.psmap_empty ()
let (decl_names_contains : Prims.string -> decl_name_set -> Prims.bool) =
  fun x ->
    fun s ->
      let uu___ = FStarC_Compiler_Util.psmap_try_find s x in
      FStar_Pervasives_Native.uu___is_Some uu___
let (add_name :
  Prims.string -> decl_name_set -> Prims.bool FStarC_Compiler_Util.psmap) =
  fun x -> fun s -> FStarC_Compiler_Util.psmap_add s x true
type decls_at_level =
  {
  pruning_state: FStarC_SMTEncoding_Pruning.pruning_state ;
  given_decl_names: decl_name_set ;
  all_decls_at_level_rev: FStarC_SMTEncoding_Term.decl Prims.list Prims.list ;
  given_some_decls: Prims.bool ;
  to_flush_rev: FStarC_SMTEncoding_Term.decl Prims.list Prims.list ;
  named_assumptions:
    FStarC_SMTEncoding_Term.assumption FStarC_Compiler_Util.psmap ;
  pruning_roots:
    FStarC_SMTEncoding_Term.decl Prims.list FStar_Pervasives_Native.option }
let (__proj__Mkdecls_at_level__item__pruning_state :
  decls_at_level -> FStarC_SMTEncoding_Pruning.pruning_state) =
  fun projectee ->
    match projectee with
    | { pruning_state; given_decl_names; all_decls_at_level_rev;
        given_some_decls; to_flush_rev; named_assumptions; pruning_roots;_}
        -> pruning_state
let (__proj__Mkdecls_at_level__item__given_decl_names :
  decls_at_level -> decl_name_set) =
  fun projectee ->
    match projectee with
    | { pruning_state; given_decl_names; all_decls_at_level_rev;
        given_some_decls; to_flush_rev; named_assumptions; pruning_roots;_}
        -> given_decl_names
let (__proj__Mkdecls_at_level__item__all_decls_at_level_rev :
  decls_at_level -> FStarC_SMTEncoding_Term.decl Prims.list Prims.list) =
  fun projectee ->
    match projectee with
    | { pruning_state; given_decl_names; all_decls_at_level_rev;
        given_some_decls; to_flush_rev; named_assumptions; pruning_roots;_}
        -> all_decls_at_level_rev
let (__proj__Mkdecls_at_level__item__given_some_decls :
  decls_at_level -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { pruning_state; given_decl_names; all_decls_at_level_rev;
        given_some_decls; to_flush_rev; named_assumptions; pruning_roots;_}
        -> given_some_decls
let (__proj__Mkdecls_at_level__item__to_flush_rev :
  decls_at_level -> FStarC_SMTEncoding_Term.decl Prims.list Prims.list) =
  fun projectee ->
    match projectee with
    | { pruning_state; given_decl_names; all_decls_at_level_rev;
        given_some_decls; to_flush_rev; named_assumptions; pruning_roots;_}
        -> to_flush_rev
let (__proj__Mkdecls_at_level__item__named_assumptions :
  decls_at_level ->
    FStarC_SMTEncoding_Term.assumption FStarC_Compiler_Util.psmap)
  =
  fun projectee ->
    match projectee with
    | { pruning_state; given_decl_names; all_decls_at_level_rev;
        given_some_decls; to_flush_rev; named_assumptions; pruning_roots;_}
        -> named_assumptions
let (__proj__Mkdecls_at_level__item__pruning_roots :
  decls_at_level ->
    FStarC_SMTEncoding_Term.decl Prims.list FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { pruning_state; given_decl_names; all_decls_at_level_rev;
        given_some_decls; to_flush_rev; named_assumptions; pruning_roots;_}
        -> pruning_roots
let (init_given_decls_at_level : decls_at_level) =
  let uu___ = FStarC_Compiler_Util.psmap_empty () in
  {
    pruning_state = FStarC_SMTEncoding_Pruning.init;
    given_decl_names = empty_decl_names;
    all_decls_at_level_rev = [];
    given_some_decls = false;
    to_flush_rev = [];
    named_assumptions = uu___;
    pruning_roots = FStar_Pervasives_Native.None
  }
type solver_state =
  {
  levels: decls_at_level Prims.list ;
  pending_flushes_rev: FStarC_SMTEncoding_Term.decl Prims.list ;
  using_facts_from: using_facts_from_setting FStar_Pervasives_Native.option ;
  retain_assumptions: decl_name_set }
let (__proj__Mksolver_state__item__levels :
  solver_state -> decls_at_level Prims.list) =
  fun projectee ->
    match projectee with
    | { levels; pending_flushes_rev; using_facts_from; retain_assumptions;_}
        -> levels
let (__proj__Mksolver_state__item__pending_flushes_rev :
  solver_state -> FStarC_SMTEncoding_Term.decl Prims.list) =
  fun projectee ->
    match projectee with
    | { levels; pending_flushes_rev; using_facts_from; retain_assumptions;_}
        -> pending_flushes_rev
let (__proj__Mksolver_state__item__using_facts_from :
  solver_state -> using_facts_from_setting FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { levels; pending_flushes_rev; using_facts_from; retain_assumptions;_}
        -> using_facts_from
let (__proj__Mksolver_state__item__retain_assumptions :
  solver_state -> decl_name_set) =
  fun projectee ->
    match projectee with
    | { levels; pending_flushes_rev; using_facts_from; retain_assumptions;_}
        -> retain_assumptions
let (depth : solver_state -> Prims.int) =
  fun s -> FStarC_Compiler_List.length s.levels
let (solver_state_to_string : solver_state -> Prims.string) =
  fun s ->
    let levels =
      FStarC_Compiler_List.map
        (fun level ->
           let uu___ =
             FStarC_Class_Show.show FStarC_Class_Show.showable_nat
               (FStarC_Compiler_List.length level.all_decls_at_level_rev) in
           let uu___1 =
             FStarC_Class_Show.show FStarC_Class_Show.showable_bool
               level.given_some_decls in
           let uu___2 =
             FStarC_Class_Show.show FStarC_Class_Show.showable_nat
               (FStarC_Compiler_List.length level.to_flush_rev) in
           FStarC_Compiler_Util.format3
             "Level { all_decls=%s; given_decls=%s; to_flush=%s }" uu___
             uu___1 uu___2) s.levels in
    let uu___ =
      FStarC_Class_Show.show
        (FStarC_Class_Show.show_list FStarC_Class_Show.showable_string)
        levels in
    let uu___1 =
      FStarC_Class_Show.show FStarC_Class_Show.showable_nat
        (FStarC_Compiler_List.length s.pending_flushes_rev) in
    FStarC_Compiler_Util.format2
      "Solver state { levels=%s; pending_flushes=%s }" uu___ uu___1
let (showable_solver_state : solver_state FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = solver_state_to_string }
let (debug : Prims.string -> solver_state -> solver_state -> unit) =
  fun msg ->
    fun s0 ->
      fun s1 ->
        let uu___ =
          let uu___1 = FStarC_Options_Ext.get "debug_solver_state" in
          uu___1 <> "" in
        if uu___
        then
          let uu___1 = solver_state_to_string s0 in
          let uu___2 = solver_state_to_string s1 in
          FStarC_Compiler_Util.print3
            "Debug (%s):{\n\t before=%s\n\t after=%s\n}" msg uu___1 uu___2
        else ()
let (peek : solver_state -> (decls_at_level * decls_at_level Prims.list)) =
  fun s ->
    match s.levels with
    | [] -> failwith "Solver state cannot have an empty stack"
    | hd::tl -> (hd, tl)
let (replace_head : decls_at_level -> solver_state -> solver_state) =
  fun hd ->
    fun s ->
      let uu___ =
        let uu___1 = FStarC_Compiler_List.tl s.levels in hd :: uu___1 in
      {
        levels = uu___;
        pending_flushes_rev = (s.pending_flushes_rev);
        using_facts_from = (s.using_facts_from);
        retain_assumptions = (s.retain_assumptions)
      }
let (init : unit -> solver_state) =
  fun uu___ ->
    let uu___1 =
      let uu___2 = FStarC_Options.using_facts_from () in
      FStar_Pervasives_Native.Some uu___2 in
    {
      levels = [init_given_decls_at_level];
      pending_flushes_rev = [];
      using_facts_from = uu___1;
      retain_assumptions = empty_decl_names
    }
let (push : solver_state -> solver_state) =
  fun s ->
    let uu___ = peek s in
    match uu___ with
    | (hd, uu___1) ->
        let push1 =
          FStarC_SMTEncoding_Term.Push (FStarC_Compiler_List.length s.levels) in
        let next =
          {
            pruning_state = (hd.pruning_state);
            given_decl_names = (hd.given_decl_names);
            all_decls_at_level_rev = [];
            given_some_decls = false;
            to_flush_rev = [[push1]];
            named_assumptions = (hd.named_assumptions);
            pruning_roots = FStar_Pervasives_Native.None
          } in
        {
          levels = (next :: (s.levels));
          pending_flushes_rev = (s.pending_flushes_rev);
          using_facts_from = (s.using_facts_from);
          retain_assumptions = (s.retain_assumptions)
        }
let (pop : solver_state -> solver_state) =
  fun s ->
    let uu___ = peek s in
    match uu___ with
    | (hd, tl) ->
        (if Prims.uu___is_Nil tl
         then failwith "Solver state cannot have an empty stack"
         else ();
         (let s1 =
            if Prims.op_Negation hd.given_some_decls
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
                  ((FStarC_SMTEncoding_Term.Pop
                      (FStarC_Compiler_List.length tl)) ::
                  (s.pending_flushes_rev));
                using_facts_from = (s.using_facts_from);
                retain_assumptions = (s.retain_assumptions)
              } in
          s1))
let (filter_using_facts_from :
  using_facts_from_setting FStar_Pervasives_Native.option ->
    FStarC_SMTEncoding_Term.assumption FStarC_Compiler_Util.psmap ->
      decl_name_set ->
        (Prims.string -> Prims.bool) ->
          FStarC_SMTEncoding_Term.decl Prims.list ->
            FStarC_SMTEncoding_Term.decl Prims.list)
  =
  fun using_facts_from ->
    fun named_assumptions ->
      fun retain_assumptions ->
        fun already_given_decl ->
          fun ds ->
            match using_facts_from with
            | FStar_Pervasives_Native.None -> ds
            | FStar_Pervasives_Native.Some (([], true)::[]) -> ds
            | FStar_Pervasives_Native.Some using_facts_from1 ->
                let keep_assumption a =
                  match a.FStarC_SMTEncoding_Term.assumption_fact_ids with
                  | [] -> true
                  | uu___ ->
                      (decl_names_contains
                         a.FStarC_SMTEncoding_Term.assumption_name
                         retain_assumptions)
                        ||
                        (FStarC_Compiler_Util.for_some
                           (fun uu___1 ->
                              match uu___1 with
                              | FStarC_SMTEncoding_Term.Name lid ->
                                  FStarC_TypeChecker_Env.should_enc_lid
                                    using_facts_from1 lid
                              | uu___2 -> false)
                           a.FStarC_SMTEncoding_Term.assumption_fact_ids) in
                let already_given_map =
                  FStarC_Compiler_Util.smap_create (Prims.of_int (1000)) in
                let add_assumption a =
                  FStarC_Compiler_Util.smap_add already_given_map
                    a.FStarC_SMTEncoding_Term.assumption_name true in
                let already_given a =
                  (let uu___ =
                     FStarC_Compiler_Util.smap_try_find already_given_map
                       a.FStarC_SMTEncoding_Term.assumption_name in
                   FStar_Pervasives_Native.uu___is_Some uu___) ||
                    (already_given_decl
                       a.FStarC_SMTEncoding_Term.assumption_name) in
                let map_decl d =
                  match d with
                  | FStarC_SMTEncoding_Term.Assume a ->
                      let uu___ =
                        (keep_assumption a) &&
                          (let uu___1 = already_given a in
                           Prims.op_Negation uu___1) in
                      if uu___ then (add_assumption a; [d]) else []
                  | FStarC_SMTEncoding_Term.RetainAssumptions names ->
                      let assumptions =
                        FStarC_Compiler_List.collect
                          (fun name ->
                             let uu___ =
                               FStarC_Compiler_Util.psmap_try_find
                                 named_assumptions name in
                             match uu___ with
                             | FStar_Pervasives_Native.None -> []
                             | FStar_Pervasives_Native.Some a ->
                                 let uu___1 = already_given a in
                                 if uu___1
                                 then []
                                 else
                                   (add_assumption a;
                                    [FStarC_SMTEncoding_Term.Assume a]))
                          names in
                      assumptions
                  | uu___ -> [d] in
                let ds1 = FStarC_Compiler_List.collect map_decl ds in ds1
let (already_given_decl : solver_state -> Prims.string -> Prims.bool) =
  fun s ->
    fun aname ->
      FStarC_Compiler_Util.for_some
        (fun level -> decl_names_contains aname level.given_decl_names)
        s.levels
let rec (flatten :
  FStarC_SMTEncoding_Term.decl -> FStarC_SMTEncoding_Term.decl Prims.list) =
  fun d ->
    match d with
    | FStarC_SMTEncoding_Term.Module (uu___, ds) ->
        FStarC_Compiler_List.collect flatten ds
    | uu___ -> [d]
let (add_named_assumptions :
  FStarC_SMTEncoding_Term.assumption FStarC_Compiler_Util.psmap ->
    FStarC_SMTEncoding_Term.decl Prims.list ->
      FStarC_SMTEncoding_Term.assumption FStarC_Compiler_Util.psmap)
  =
  fun named_assumptions ->
    fun ds ->
      FStarC_Compiler_List.fold_left
        (fun named_assumptions1 ->
           fun d ->
             match d with
             | FStarC_SMTEncoding_Term.Assume a ->
                 FStarC_Compiler_Util.psmap_add named_assumptions1
                   a.FStarC_SMTEncoding_Term.assumption_name a
             | uu___ -> named_assumptions1) named_assumptions ds
let (add_retain_assumptions :
  FStarC_SMTEncoding_Term.decl Prims.list -> solver_state -> solver_state) =
  fun ds ->
    fun s ->
      let ra =
        FStarC_Compiler_List.fold_left
          (fun ra1 ->
             fun d ->
               match d with
               | FStarC_SMTEncoding_Term.RetainAssumptions names ->
                   FStarC_Compiler_List.fold_left
                     (fun ra2 -> fun name -> add_name name ra2) ra1 names
               | uu___ -> ra1) s.retain_assumptions ds in
      {
        levels = (s.levels);
        pending_flushes_rev = (s.pending_flushes_rev);
        using_facts_from = (s.using_facts_from);
        retain_assumptions = ra
      }
let (give_delay_assumptions :
  Prims.bool ->
    FStarC_SMTEncoding_Term.decl Prims.list -> solver_state -> solver_state)
  =
  fun resetting ->
    fun ds ->
      fun s ->
        let decls = FStarC_Compiler_List.collect flatten ds in
        let uu___ =
          FStarC_Compiler_List.partition
            FStarC_SMTEncoding_Term.uu___is_Assume decls in
        match uu___ with
        | (assumptions, rest) ->
            let uu___1 = peek s in
            (match uu___1 with
             | (hd, tl) ->
                 let hd1 =
                   {
                     pruning_state = (hd.pruning_state);
                     given_decl_names = (hd.given_decl_names);
                     all_decls_at_level_rev = (ds ::
                       (hd.all_decls_at_level_rev));
                     given_some_decls = (hd.given_some_decls);
                     to_flush_rev = (rest :: (hd.to_flush_rev));
                     named_assumptions = (hd.named_assumptions);
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
                      let uu___3 =
                        FStarC_SMTEncoding_Pruning.add_decls decls
                          hd1.pruning_state in
                      let uu___4 =
                        add_named_assumptions hd1.named_assumptions
                          assumptions in
                      {
                        pruning_state = uu___3;
                        given_decl_names = (hd1.given_decl_names);
                        all_decls_at_level_rev = (hd1.all_decls_at_level_rev);
                        given_some_decls = (hd1.given_some_decls);
                        to_flush_rev = (hd1.to_flush_rev);
                        named_assumptions = uu___4;
                        pruning_roots = (hd1.pruning_roots)
                      } in
                    add_retain_assumptions decls
                      {
                        levels = (hd2 :: tl);
                        pending_flushes_rev = (s.pending_flushes_rev);
                        using_facts_from = (s.using_facts_from);
                        retain_assumptions = (s.retain_assumptions)
                      }))
let (give_now :
  Prims.bool ->
    FStarC_SMTEncoding_Term.decl Prims.list -> solver_state -> solver_state)
  =
  fun resetting ->
    fun ds ->
      fun s ->
        let decls = FStarC_Compiler_List.collect flatten ds in
        let uu___ =
          FStarC_Compiler_List.partition
            FStarC_SMTEncoding_Term.uu___is_Assume decls in
        match uu___ with
        | (assumptions, uu___1) ->
            let uu___2 = peek s in
            (match uu___2 with
             | (hd, tl) ->
                 let named_assumptions =
                   if resetting
                   then hd.named_assumptions
                   else
                     add_named_assumptions hd.named_assumptions assumptions in
                 let ds_to_flush =
                   filter_using_facts_from s.using_facts_from
                     named_assumptions s.retain_assumptions
                     (already_given_decl s) decls in
                 let given =
                   FStarC_Compiler_List.fold_left
                     (fun given1 ->
                        fun d ->
                          match d with
                          | FStarC_SMTEncoding_Term.Assume a ->
                              add_name
                                a.FStarC_SMTEncoding_Term.assumption_name
                                given1
                          | uu___3 -> given1) hd.given_decl_names ds_to_flush in
                 let hd1 =
                   {
                     pruning_state = (hd.pruning_state);
                     given_decl_names = given;
                     all_decls_at_level_rev = (ds ::
                       (hd.all_decls_at_level_rev));
                     given_some_decls = (hd.given_some_decls);
                     to_flush_rev = (ds_to_flush :: (hd.to_flush_rev));
                     named_assumptions = (hd.named_assumptions);
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
                        all_decls_at_level_rev = (hd1.all_decls_at_level_rev);
                        given_some_decls = (hd1.given_some_decls);
                        to_flush_rev = (hd1.to_flush_rev);
                        named_assumptions;
                        pruning_roots = (hd1.pruning_roots)
                      } in
                    add_retain_assumptions decls
                      {
                        levels = (hd2 :: tl);
                        pending_flushes_rev = (s.pending_flushes_rev);
                        using_facts_from = (s.using_facts_from);
                        retain_assumptions = (s.retain_assumptions)
                      }))
let (give_aux :
  Prims.bool ->
    FStarC_SMTEncoding_Term.decl Prims.list -> solver_state -> solver_state)
  =
  fun resetting ->
    fun ds ->
      fun s ->
        let uu___ =
          let uu___1 = FStarC_Options_Ext.get "context_pruning" in
          uu___1 <> "" in
        if uu___
        then give_delay_assumptions resetting ds s
        else give_now resetting ds s
let (give :
  FStarC_SMTEncoding_Term.decl Prims.list -> solver_state -> solver_state) =
  give_aux false
let (reset :
  using_facts_from_setting FStar_Pervasives_Native.option ->
    solver_state -> solver_state)
  =
  fun using_facts_from ->
    fun s ->
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
                named_assumptions = (hd.named_assumptions);
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
                named_assumptions = (level.named_assumptions);
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
              FStarC_Compiler_List.fold_right
                (if now then give_now true else give_aux true)
                level.all_decls_at_level_rev s_new3 in
            let uu___1 = set_pruning_roots level s1 in
            (uu___1,
              (FStar_Pervasives_Native.uu___is_Some level.pruning_roots)) in
      let rec rebuild levels s_new2 =
        match levels with
        | last::[] -> rebuild_level false last s_new2
        | level::levels1 ->
            let uu___ = rebuild levels1 s_new2 in
            (match uu___ with
             | (s_new3, now) ->
                 let s_new4 = push s_new3 in rebuild_level now level s_new4) in
      let uu___ = rebuild s.levels s_new1 in
      FStar_Pervasives_Native.fst uu___
let (name_of_assumption : FStarC_SMTEncoding_Term.decl -> Prims.string) =
  fun d ->
    match d with
    | FStarC_SMTEncoding_Term.Assume a ->
        a.FStarC_SMTEncoding_Term.assumption_name
    | uu___ -> failwith "Expected an assumption"
let (prune_level :
  FStarC_SMTEncoding_Term.decl Prims.list ->
    decls_at_level -> solver_state -> decls_at_level)
  =
  fun roots ->
    fun hd ->
      fun s ->
        let to_give = FStarC_SMTEncoding_Pruning.prune hd.pruning_state roots in
        let uu___ =
          FStarC_Compiler_List.fold_left
            (fun uu___1 ->
               fun to_give1 ->
                 match uu___1 with
                 | (decl_name_set1, can_give) ->
                     let name = name_of_assumption to_give1 in
                     let uu___2 =
                       let uu___3 = decl_names_contains name decl_name_set1 in
                       Prims.op_Negation uu___3 in
                     if uu___2
                     then
                       let uu___3 = add_name name decl_name_set1 in
                       (uu___3, (to_give1 :: can_give))
                     else (decl_name_set1, can_give))
            ((hd.given_decl_names), []) to_give in
        match uu___ with
        | (given_decl_names, can_give) ->
            let can_give1 =
              filter_using_facts_from s.using_facts_from hd.named_assumptions
                s.retain_assumptions (already_given_decl s) can_give in
            let hd1 =
              {
                pruning_state = (hd.pruning_state);
                given_decl_names;
                all_decls_at_level_rev = (hd.all_decls_at_level_rev);
                given_some_decls = (hd.given_some_decls);
                to_flush_rev = (can_give1 :: (hd.to_flush_rev));
                named_assumptions = (hd.named_assumptions);
                pruning_roots = (hd.pruning_roots)
              } in
            hd1
let (prune_sim :
  FStarC_SMTEncoding_Term.decl Prims.list ->
    solver_state -> Prims.string Prims.list)
  =
  fun roots ->
    fun s ->
      let uu___ = peek s in
      match uu___ with
      | (hd, tl) ->
          let to_give =
            FStarC_SMTEncoding_Pruning.prune hd.pruning_state roots in
          let can_give =
            filter_using_facts_from s.using_facts_from hd.named_assumptions
              s.retain_assumptions (already_given_decl s) to_give in
          let uu___1 =
            let uu___2 =
              FStarC_Compiler_List.filter
                FStarC_SMTEncoding_Term.uu___is_Assume roots in
            FStar_List_Tot_Base.op_At uu___2 can_give in
          FStarC_Compiler_List.map name_of_assumption uu___1
let (start_query :
  Prims.string ->
    FStarC_SMTEncoding_Term.decl Prims.list ->
      FStarC_SMTEncoding_Term.decl -> solver_state -> solver_state)
  =
  fun msg ->
    fun roots_to_push ->
      fun qry ->
        fun s ->
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
                       named_assumptions = (hd.named_assumptions);
                       pruning_roots =
                         (FStar_Pervasives_Native.Some (qry :: roots_to_push))
                     } :: tl);
                  pending_flushes_rev = (s.pending_flushes_rev);
                  using_facts_from = (s.using_facts_from);
                  retain_assumptions = (s.retain_assumptions)
                } in
              let s2 = push s1 in
              let s3 = give [FStarC_SMTEncoding_Term.Caption msg] s2 in
              give_now false roots_to_push s3
let (finish_query : Prims.string -> solver_state -> solver_state) =
  fun msg ->
    fun s ->
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
                 named_assumptions = (hd.named_assumptions);
                 pruning_roots = FStar_Pervasives_Native.None
               } :: tl);
            pending_flushes_rev = (s2.pending_flushes_rev);
            using_facts_from = (s2.using_facts_from);
            retain_assumptions = (s2.retain_assumptions)
          }
let (filter_with_unsat_core :
  Prims.string ->
    FStarC_SMTEncoding_UnsatCore.unsat_core ->
      solver_state -> FStarC_SMTEncoding_Term.decl Prims.list)
  =
  fun queryid ->
    fun core ->
      fun s ->
        let rec all_decls levels =
          match levels with
          | last::[] -> last.all_decls_at_level_rev
          | level::levels1 ->
              let uu___ =
                let uu___1 = all_decls levels1 in
                [FStarC_SMTEncoding_Term.Push
                   (FStarC_Compiler_List.length levels1)]
                  :: uu___1 in
              FStar_List_Tot_Base.op_At level.all_decls_at_level_rev uu___ in
        let all_decls1 = all_decls s.levels in
        let all_decls2 =
          FStarC_Compiler_List.flatten (FStarC_Compiler_List.rev all_decls1) in
        FStarC_SMTEncoding_UnsatCore.filter core all_decls2
let (would_have_pruned :
  solver_state -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun s ->
    let uu___ =
      let uu___1 = FStarC_Options_Ext.get "context_pruning_sim" in
      uu___1 = "" in
    if uu___
    then FStar_Pervasives_Native.None
    else
      (let rec aux levels =
         match levels with
         | [] -> FStar_Pervasives_Native.None
         | level::levels1 ->
             (match level.pruning_roots with
              | FStar_Pervasives_Native.Some roots ->
                  let uu___2 = prune_sim roots s in
                  FStar_Pervasives_Native.Some uu___2
              | FStar_Pervasives_Native.None -> aux levels1) in
       aux s.levels)
let (flush :
  solver_state -> (FStarC_SMTEncoding_Term.decl Prims.list * solver_state)) =
  fun s ->
    let s1 =
      let uu___ =
        let uu___1 = FStarC_Options_Ext.get "context_pruning" in uu___1 <> "" in
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
          FStarC_Compiler_List.collect (fun level -> level.to_flush_rev)
            s1.levels in
        FStarC_Compiler_List.rev uu___1 in
      FStarC_Compiler_List.flatten uu___ in
    let levels =
      FStarC_Compiler_List.map
        (fun level ->
           {
             pruning_state = (level.pruning_state);
             given_decl_names = (level.given_decl_names);
             all_decls_at_level_rev = (level.all_decls_at_level_rev);
             given_some_decls =
               (level.given_some_decls ||
                  (Prims.uu___is_Cons level.to_flush_rev));
             to_flush_rev = [];
             named_assumptions = (level.named_assumptions);
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
      FStar_List_Tot_Base.op_At
        (FStarC_Compiler_List.rev s1.pending_flushes_rev) to_flush in
    (flushed, s11)