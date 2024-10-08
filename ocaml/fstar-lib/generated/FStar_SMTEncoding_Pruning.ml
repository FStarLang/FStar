open Prims
type triggers = Prims.string Prims.list Prims.list
type triggers_set = Prims.string FStar_Compiler_RBSet.t Prims.list
let (triggers_as_triggers_set : triggers -> triggers_set) =
  fun ts ->
    FStar_Compiler_List.map
      (fun uu___ ->
         (Obj.magic
            (FStar_Class_Setlike.from_list ()
               (Obj.magic
                  (FStar_Compiler_RBSet.setlike_rbset
                     FStar_Class_Ord.ord_string)))) uu___) ts
type pruning_state =
  {
  macro_freenames: Prims.string Prims.list FStar_Compiler_Util.psmap ;
  trigger_to_assumption:
    FStar_SMTEncoding_Term.assumption Prims.list FStar_Compiler_Util.psmap ;
  assumption_to_triggers: triggers_set FStar_Compiler_Util.psmap ;
  assumption_name_map: FStar_SMTEncoding_Term.decl FStar_Compiler_Util.psmap ;
  ambients: Prims.string Prims.list ;
  extra_roots: FStar_SMTEncoding_Term.assumption Prims.list }
let (__proj__Mkpruning_state__item__macro_freenames :
  pruning_state -> Prims.string Prims.list FStar_Compiler_Util.psmap) =
  fun projectee ->
    match projectee with
    | { macro_freenames; trigger_to_assumption; assumption_to_triggers;
        assumption_name_map; ambients; extra_roots;_} -> macro_freenames
let (__proj__Mkpruning_state__item__trigger_to_assumption :
  pruning_state ->
    FStar_SMTEncoding_Term.assumption Prims.list FStar_Compiler_Util.psmap)
  =
  fun projectee ->
    match projectee with
    | { macro_freenames; trigger_to_assumption; assumption_to_triggers;
        assumption_name_map; ambients; extra_roots;_} ->
        trigger_to_assumption
let (__proj__Mkpruning_state__item__assumption_to_triggers :
  pruning_state -> triggers_set FStar_Compiler_Util.psmap) =
  fun projectee ->
    match projectee with
    | { macro_freenames; trigger_to_assumption; assumption_to_triggers;
        assumption_name_map; ambients; extra_roots;_} ->
        assumption_to_triggers
let (__proj__Mkpruning_state__item__assumption_name_map :
  pruning_state -> FStar_SMTEncoding_Term.decl FStar_Compiler_Util.psmap) =
  fun projectee ->
    match projectee with
    | { macro_freenames; trigger_to_assumption; assumption_to_triggers;
        assumption_name_map; ambients; extra_roots;_} -> assumption_name_map
let (__proj__Mkpruning_state__item__ambients :
  pruning_state -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { macro_freenames; trigger_to_assumption; assumption_to_triggers;
        assumption_name_map; ambients; extra_roots;_} -> ambients
let (__proj__Mkpruning_state__item__extra_roots :
  pruning_state -> FStar_SMTEncoding_Term.assumption Prims.list) =
  fun projectee ->
    match projectee with
    | { macro_freenames; trigger_to_assumption; assumption_to_triggers;
        assumption_name_map; ambients; extra_roots;_} -> extra_roots
let (debug : (unit -> unit) -> unit) =
  fun f ->
    let uu___ =
      let uu___1 = FStar_Options_Ext.get "debug_context_pruning" in
      uu___1 <> "" in
    if uu___ then f () else ()
let (print_pruning_state : pruning_state -> Prims.string) =
  fun p ->
    let t_to_a =
      FStar_Compiler_Util.psmap_fold p.trigger_to_assumption
        (fun k ->
           fun v -> fun acc -> (k, (FStar_Compiler_List.length v)) :: acc) [] in
    let t_to_a1 =
      FStar_Compiler_Util.sort_with
        (fun x ->
           fun y ->
             (FStar_Pervasives_Native.snd x) -
               (FStar_Pervasives_Native.snd y)) t_to_a in
    let a_to_t =
      FStar_Compiler_Util.psmap_fold p.assumption_to_triggers
        (fun k ->
           fun v ->
             fun acc ->
               let uu___ =
                 let uu___1 =
                   FStar_Class_Show.show
                     (FStar_Class_Show.show_list
                        (FStar_Compiler_RBSet.showable_rbset
                           (FStar_Class_Show.printableshow
                              FStar_Class_Printable.printable_string))) v in
                 FStar_Compiler_Util.format2 "[%s -> %s]" k uu___1 in
               uu___ :: acc) [] in
    let macros =
      FStar_Compiler_Util.psmap_fold p.macro_freenames
        (fun k ->
           fun v ->
             fun acc ->
               let uu___ =
                 let uu___1 =
                   FStar_Class_Show.show
                     (FStar_Class_Show.show_list
                        (FStar_Class_Show.printableshow
                           FStar_Class_Printable.printable_string)) v in
                 FStar_Compiler_Util.format2 "[%s -> %s]" k uu___1 in
               uu___ :: acc) [] in
    let uu___ =
      let uu___1 =
        FStar_Compiler_List.map
          (FStar_Class_Show.show
             (FStar_Class_Show.show_tuple2
                (FStar_Class_Show.printableshow
                   FStar_Class_Printable.printable_string)
                (FStar_Class_Show.printableshow
                   FStar_Class_Printable.printable_int))) t_to_a1 in
      FStar_Compiler_String.concat "\n\t" uu___1 in
    FStar_Compiler_Util.format3
      "Pruning state:\n\tTriggers to assumptions:\n\t%s\nAssumptions to triggers:\n\t%s\nMacros:\n\t%s\n"
      uu___ (FStar_Compiler_String.concat "\n\t" a_to_t)
      (FStar_Compiler_String.concat "\n\t" macros)
let (show_pruning_state : pruning_state FStar_Class_Show.showable) =
  { FStar_Class_Show.show = print_pruning_state }
let (init : pruning_state) =
  let uu___ = FStar_Compiler_Util.psmap_empty () in
  let uu___1 = FStar_Compiler_Util.psmap_empty () in
  let uu___2 = FStar_Compiler_Util.psmap_empty () in
  let uu___3 = FStar_Compiler_Util.psmap_empty () in
  {
    macro_freenames = uu___;
    trigger_to_assumption = uu___1;
    assumption_to_triggers = uu___2;
    assumption_name_map = uu___3;
    ambients = [];
    extra_roots = []
  }
let (add_trigger_to_assumption :
  FStar_SMTEncoding_Term.assumption ->
    pruning_state -> Prims.string -> pruning_state)
  =
  fun a ->
    fun p ->
      fun trig ->
        let uu___ =
          FStar_Compiler_Util.psmap_try_find p.trigger_to_assumption trig in
        match uu___ with
        | FStar_Pervasives_Native.None ->
            let uu___1 =
              FStar_Compiler_Util.psmap_add p.trigger_to_assumption trig [a] in
            {
              macro_freenames = (p.macro_freenames);
              trigger_to_assumption = uu___1;
              assumption_to_triggers = (p.assumption_to_triggers);
              assumption_name_map = (p.assumption_name_map);
              ambients = (p.ambients);
              extra_roots = (p.extra_roots)
            }
        | FStar_Pervasives_Native.Some l ->
            let uu___1 =
              FStar_Compiler_Util.psmap_add p.trigger_to_assumption trig (a
                :: l) in
            {
              macro_freenames = (p.macro_freenames);
              trigger_to_assumption = uu___1;
              assumption_to_triggers = (p.assumption_to_triggers);
              assumption_name_map = (p.assumption_name_map);
              ambients = (p.ambients);
              extra_roots = (p.extra_roots)
            }
let (exclude_names : Prims.string FStar_Compiler_RBSet.t) =
  Obj.magic
    (FStar_Class_Setlike.from_list ()
       (Obj.magic
          (FStar_Compiler_RBSet.setlike_rbset FStar_Class_Ord.ord_string))
       ["SFuel";
       "ZFuel";
       "HasType";
       "HasTypeZ";
       "HasTypeFuel";
       "Valid";
       "ApplyTT";
       "ApplyTF";
       "Prims.lex_t"])
let (free_top_level_names :
  FStar_SMTEncoding_Term.term -> Prims.string FStar_Compiler_RBSet.t) =
  fun uu___ ->
    (fun t ->
       let uu___ = FStar_SMTEncoding_Term.free_top_level_names t in
       Obj.magic
         (FStar_Class_Setlike.diff ()
            (Obj.magic
               (FStar_Compiler_RBSet.setlike_rbset FStar_Class_Ord.ord_string))
            (Obj.magic uu___) (Obj.magic exclude_names))) uu___
let (assumption_free_names :
  FStar_SMTEncoding_Term.assumption -> Prims.string FStar_Compiler_RBSet.t) =
  fun uu___ ->
    (fun a ->
       Obj.magic
         (FStar_Class_Setlike.diff ()
            (Obj.magic
               (FStar_Compiler_RBSet.setlike_rbset FStar_Class_Ord.ord_string))
            (Obj.magic a.FStar_SMTEncoding_Term.assumption_free_names)
            (Obj.magic exclude_names))) uu___
let (triggers_of_term : FStar_SMTEncoding_Term.term -> triggers_set) =
  fun t ->
    let rec aux t1 =
      match t1.FStar_SMTEncoding_Term.tm with
      | FStar_SMTEncoding_Term.Quant
          (FStar_SMTEncoding_Term.Forall, triggers1, uu___, uu___1, uu___2)
          ->
          FStar_Compiler_List.map
            (fun disjunct ->
               let uu___3 =
                 Obj.magic
                   (FStar_Class_Setlike.empty ()
                      (Obj.magic
                         (FStar_Compiler_RBSet.setlike_rbset
                            FStar_Class_Ord.ord_string)) ()) in
               FStar_Compiler_List.fold_left
                 (fun uu___5 ->
                    fun uu___4 ->
                      (fun out ->
                         fun t2 ->
                           let uu___4 = free_top_level_names t2 in
                           Obj.magic
                             (FStar_Class_Setlike.union ()
                                (Obj.magic
                                   (FStar_Compiler_RBSet.setlike_rbset
                                      FStar_Class_Ord.ord_string))
                                (Obj.magic out) (Obj.magic uu___4))) uu___5
                        uu___4) uu___3 disjunct) triggers1
      | FStar_SMTEncoding_Term.Labeled (t2, uu___, uu___1) -> aux t2
      | FStar_SMTEncoding_Term.LblPos (t2, uu___) -> aux t2
      | uu___ -> [] in
    aux t
let (maybe_add_ambient :
  FStar_SMTEncoding_Term.assumption -> pruning_state -> pruning_state) =
  fun a ->
    fun p ->
      let add_assumption_with_triggers triggers1 =
        let p1 =
          let uu___ =
            FStar_Compiler_Util.psmap_add p.assumption_to_triggers
              a.FStar_SMTEncoding_Term.assumption_name triggers1 in
          {
            macro_freenames = (p.macro_freenames);
            trigger_to_assumption = (p.trigger_to_assumption);
            assumption_to_triggers = uu___;
            assumption_name_map = (p.assumption_name_map);
            ambients = (p.ambients);
            extra_roots = (p.extra_roots)
          } in
        let uu___ =
          FStar_Compiler_List.map
            (fun uu___1 ->
               (Obj.magic
                  (FStar_Class_Setlike.elems ()
                     (Obj.magic
                        (FStar_Compiler_RBSet.setlike_rbset
                           FStar_Class_Ord.ord_string)))) uu___1) triggers1 in
        FStar_Compiler_List.fold_left
          (FStar_Compiler_List.fold_left (add_trigger_to_assumption a)) p1
          uu___ in
      let is_empty triggers1 =
        match triggers1 with
        | [] -> true
        | t::[] ->
            FStar_Class_Setlike.is_empty ()
              (Obj.magic
                 (FStar_Compiler_RBSet.setlike_rbset
                    FStar_Class_Ord.ord_string)) (Obj.magic t)
        | uu___ -> false in
      let is_ambient_refinement ty =
        match ty.FStar_SMTEncoding_Term.tm with
        | FStar_SMTEncoding_Term.App
            (FStar_SMTEncoding_Term.Var "Prims.squash", uu___) -> true
        | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var name, uu___)
            -> FStar_Compiler_Util.starts_with name "Tm_refine_"
        | FStar_SMTEncoding_Term.FreeV (FStar_SMTEncoding_Term.FV
            (name, uu___, uu___1)) ->
            FStar_Compiler_Util.starts_with name "Tm_refine_"
        | uu___ -> false in
      let ambient_refinement_payload ty =
        match ty.FStar_SMTEncoding_Term.tm with
        | FStar_SMTEncoding_Term.App
            (FStar_SMTEncoding_Term.Var "Prims.squash", t::[]) -> t
        | uu___ -> ty in
      if
        a.FStar_SMTEncoding_Term.assumption_name =
          "function_token_typing_Prims.__cache_version_number__"
      then
        {
          macro_freenames = (p.macro_freenames);
          trigger_to_assumption = (p.trigger_to_assumption);
          assumption_to_triggers = (p.assumption_to_triggers);
          assumption_name_map = (p.assumption_name_map);
          ambients = ((a.FStar_SMTEncoding_Term.assumption_name) ::
            (p.ambients));
          extra_roots = (p.extra_roots)
        }
      else
        (match (a.FStar_SMTEncoding_Term.assumption_term).FStar_SMTEncoding_Term.tm
         with
         | FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Iff, t0::t1::[]) when
             FStar_Compiler_Util.starts_with
               a.FStar_SMTEncoding_Term.assumption_name "l_quant_interp"
             ->
             let triggers_lhs = free_top_level_names t0 in
             add_assumption_with_triggers [triggers_lhs]
         | uu___ when
             FStar_Compiler_Util.starts_with
               a.FStar_SMTEncoding_Term.assumption_name "assumption_"
             ->
             let triggers1 =
               triggers_of_term a.FStar_SMTEncoding_Term.assumption_term in
             let uu___1 = is_empty triggers1 in
             if uu___1
             then
               let triggers2 =
                 let uu___2 =
                   free_top_level_names
                     a.FStar_SMTEncoding_Term.assumption_term in
                 [uu___2] in
               add_assumption_with_triggers triggers2
             else add_assumption_with_triggers triggers1
         | FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "HasType", term::ty::[]) when
             is_ambient_refinement ty ->
             let triggers1 = triggers_of_term (ambient_refinement_payload ty) in
             let uu___ = is_empty triggers1 in
             if uu___
             then
               {
                 macro_freenames = (p.macro_freenames);
                 trigger_to_assumption = (p.trigger_to_assumption);
                 assumption_to_triggers = (p.assumption_to_triggers);
                 assumption_name_map = (p.assumption_name_map);
                 ambients = ((a.FStar_SMTEncoding_Term.assumption_name) ::
                   (p.ambients));
                 extra_roots = (a :: (p.extra_roots))
               }
             else add_assumption_with_triggers triggers1
         | FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "Valid",
              {
                FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var "ApplyTT",
                   {
                     FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
                       (FStar_SMTEncoding_Term.FV
                       ("__uu__PartialApp", uu___, uu___1));
                     FStar_SMTEncoding_Term.freevars = uu___2;
                     FStar_SMTEncoding_Term.rng = uu___3;_}::term::[]);
                FStar_SMTEncoding_Term.freevars = uu___4;
                FStar_SMTEncoding_Term.rng = uu___5;_}::[])
             ->
             let triggers1 =
               match term.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.FreeV (FStar_SMTEncoding_Term.FV
                   (token, uu___6, uu___7)) ->
                   if FStar_Compiler_Util.ends_with token "@tok"
                   then
                     let uu___8 =
                       Obj.magic
                         (FStar_Class_Setlike.singleton ()
                            (Obj.magic
                               (FStar_Compiler_RBSet.setlike_rbset
                                  FStar_Class_Ord.ord_string)) token) in
                     let uu___9 =
                       let uu___10 =
                         let uu___11 =
                           FStar_Compiler_Util.substring token Prims.int_zero
                             ((FStar_Compiler_String.length token) -
                                (Prims.of_int (4))) in
                         Obj.magic
                           (FStar_Class_Setlike.singleton ()
                              (Obj.magic
                                 (FStar_Compiler_RBSet.setlike_rbset
                                    FStar_Class_Ord.ord_string)) uu___11) in
                       [uu___10] in
                     uu___8 :: uu___9
                   else
                     (let uu___9 =
                        Obj.magic
                          (FStar_Class_Setlike.singleton ()
                             (Obj.magic
                                (FStar_Compiler_RBSet.setlike_rbset
                                   FStar_Class_Ord.ord_string)) token) in
                      [uu___9])
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Var token, []) ->
                   if FStar_Compiler_Util.ends_with token "@tok"
                   then
                     let uu___6 =
                       Obj.magic
                         (FStar_Class_Setlike.singleton ()
                            (Obj.magic
                               (FStar_Compiler_RBSet.setlike_rbset
                                  FStar_Class_Ord.ord_string)) token) in
                     let uu___7 =
                       let uu___8 =
                         let uu___9 =
                           FStar_Compiler_Util.substring token Prims.int_zero
                             ((FStar_Compiler_String.length token) -
                                (Prims.of_int (4))) in
                         Obj.magic
                           (FStar_Class_Setlike.singleton ()
                              (Obj.magic
                                 (FStar_Compiler_RBSet.setlike_rbset
                                    FStar_Class_Ord.ord_string)) uu___9) in
                       [uu___8] in
                     uu___6 :: uu___7
                   else
                     (let uu___7 =
                        Obj.magic
                          (FStar_Class_Setlike.singleton ()
                             (Obj.magic
                                (FStar_Compiler_RBSet.setlike_rbset
                                   FStar_Class_Ord.ord_string)) token) in
                      [uu___7])
               | uu___6 -> [] in
             add_assumption_with_triggers triggers1
         | FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "Valid",
              {
                FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                  (FStar_SMTEncoding_Term.Var "ApplyTT",
                   {
                     FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                       (FStar_SMTEncoding_Term.Var "__uu__PartialApp", uu___);
                     FStar_SMTEncoding_Term.freevars = uu___1;
                     FStar_SMTEncoding_Term.rng = uu___2;_}::term::[]);
                FStar_SMTEncoding_Term.freevars = uu___3;
                FStar_SMTEncoding_Term.rng = uu___4;_}::[])
             ->
             let triggers1 =
               match term.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.FreeV (FStar_SMTEncoding_Term.FV
                   (token, uu___5, uu___6)) ->
                   if FStar_Compiler_Util.ends_with token "@tok"
                   then
                     let uu___7 =
                       Obj.magic
                         (FStar_Class_Setlike.singleton ()
                            (Obj.magic
                               (FStar_Compiler_RBSet.setlike_rbset
                                  FStar_Class_Ord.ord_string)) token) in
                     let uu___8 =
                       let uu___9 =
                         let uu___10 =
                           FStar_Compiler_Util.substring token Prims.int_zero
                             ((FStar_Compiler_String.length token) -
                                (Prims.of_int (4))) in
                         Obj.magic
                           (FStar_Class_Setlike.singleton ()
                              (Obj.magic
                                 (FStar_Compiler_RBSet.setlike_rbset
                                    FStar_Class_Ord.ord_string)) uu___10) in
                       [uu___9] in
                     uu___7 :: uu___8
                   else
                     (let uu___8 =
                        Obj.magic
                          (FStar_Class_Setlike.singleton ()
                             (Obj.magic
                                (FStar_Compiler_RBSet.setlike_rbset
                                   FStar_Class_Ord.ord_string)) token) in
                      [uu___8])
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Var token, []) ->
                   if FStar_Compiler_Util.ends_with token "@tok"
                   then
                     let uu___5 =
                       Obj.magic
                         (FStar_Class_Setlike.singleton ()
                            (Obj.magic
                               (FStar_Compiler_RBSet.setlike_rbset
                                  FStar_Class_Ord.ord_string)) token) in
                     let uu___6 =
                       let uu___7 =
                         let uu___8 =
                           FStar_Compiler_Util.substring token Prims.int_zero
                             ((FStar_Compiler_String.length token) -
                                (Prims.of_int (4))) in
                         Obj.magic
                           (FStar_Class_Setlike.singleton ()
                              (Obj.magic
                                 (FStar_Compiler_RBSet.setlike_rbset
                                    FStar_Class_Ord.ord_string)) uu___8) in
                       [uu___7] in
                     uu___5 :: uu___6
                   else
                     (let uu___6 =
                        Obj.magic
                          (FStar_Class_Setlike.singleton ()
                             (Obj.magic
                                (FStar_Compiler_RBSet.setlike_rbset
                                   FStar_Class_Ord.ord_string)) token) in
                      [uu___6])
               | uu___5 -> [] in
             add_assumption_with_triggers triggers1
         | FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "Valid", term::[]) ->
             let uu___ = let uu___1 = free_top_level_names term in [uu___1] in
             add_assumption_with_triggers uu___
         | FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "HasType", term::uu___::[]) ->
             let uu___1 = let uu___2 = free_top_level_names term in [uu___2] in
             add_assumption_with_triggers uu___1
         | FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "IsTotFun", term::[]) ->
             let uu___ = let uu___1 = free_top_level_names term in [uu___1] in
             add_assumption_with_triggers uu___
         | FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var "is-Tm_arrow", term::[]) ->
             let uu___ = let uu___1 = free_top_level_names term in [uu___1] in
             add_assumption_with_triggers uu___
         | FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Eq,
              uu___::{
                       FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.Var "Term_constr_id",
                          term::[]);
                       FStar_SMTEncoding_Term.freevars = uu___1;
                       FStar_SMTEncoding_Term.rng = uu___2;_}::[])
             ->
             let uu___3 = let uu___4 = free_top_level_names term in [uu___4] in
             add_assumption_with_triggers uu___3
         | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.And, tms) ->
             let t1 = FStar_Compiler_List.collect triggers_of_term tms in
             add_assumption_with_triggers t1
         | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Eq, t0::t1::[])
             when
             FStar_Compiler_Util.starts_with
               a.FStar_SMTEncoding_Term.assumption_name "equation_"
             ->
             let t01 = free_top_level_names t0 in
             add_assumption_with_triggers [t01]
         | FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Iff, t0::t1::[]) ->
             let t01 = free_top_level_names t0 in
             let t11 = free_top_level_names t1 in
             add_assumption_with_triggers [t01; t11]
         | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Eq, t0::t1::[])
             ->
             let t01 = free_top_level_names t0 in
             let t11 = free_top_level_names t1 in
             add_assumption_with_triggers [t01; t11]
         | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.TrueOp, uu___)
             -> p
         | uu___ ->
             {
               macro_freenames = (p.macro_freenames);
               trigger_to_assumption = (p.trigger_to_assumption);
               assumption_to_triggers = (p.assumption_to_triggers);
               assumption_name_map = (p.assumption_name_map);
               ambients = ((a.FStar_SMTEncoding_Term.assumption_name) ::
                 (p.ambients));
               extra_roots = (p.extra_roots)
             })
let (add_assumption_to_triggers :
  FStar_SMTEncoding_Term.assumption ->
    pruning_state -> triggers_set -> pruning_state)
  =
  fun a ->
    fun p ->
      fun trigs ->
        let p1 =
          let uu___ =
            FStar_Compiler_Util.psmap_add p.assumption_name_map
              a.FStar_SMTEncoding_Term.assumption_name
              (FStar_SMTEncoding_Term.Assume a) in
          {
            macro_freenames = (p.macro_freenames);
            trigger_to_assumption = (p.trigger_to_assumption);
            assumption_to_triggers = (p.assumption_to_triggers);
            assumption_name_map = uu___;
            ambients = (p.ambients);
            extra_roots = (p.extra_roots)
          } in
        match trigs with
        | [] -> maybe_add_ambient a p1
        | uu___ ->
            let uu___1 =
              FStar_Compiler_Util.psmap_add p1.assumption_to_triggers
                a.FStar_SMTEncoding_Term.assumption_name trigs in
            {
              macro_freenames = (p1.macro_freenames);
              trigger_to_assumption = (p1.trigger_to_assumption);
              assumption_to_triggers = uu___1;
              assumption_name_map = (p1.assumption_name_map);
              ambients = (p1.ambients);
              extra_roots = (p1.extra_roots)
            }
let (trigger_reached : pruning_state -> Prims.string -> pruning_state) =
  fun p ->
    fun trig ->
      let uu___ =
        FStar_Compiler_Util.psmap_remove p.trigger_to_assumption trig in
      {
        macro_freenames = (p.macro_freenames);
        trigger_to_assumption = uu___;
        assumption_to_triggers = (p.assumption_to_triggers);
        assumption_name_map = (p.assumption_name_map);
        ambients = (p.ambients);
        extra_roots = (p.extra_roots)
      }
let (remove_trigger_for_assumption :
  pruning_state ->
    Prims.string -> Prims.string -> (pruning_state * Prims.bool))
  =
  fun p ->
    fun trig ->
      fun aname ->
        let uu___ =
          FStar_Compiler_Util.psmap_try_find p.assumption_to_triggers aname in
        match uu___ with
        | FStar_Pervasives_Native.None -> (p, false)
        | FStar_Pervasives_Native.Some l ->
            let remaining_triggers =
              FStar_Compiler_List.map
                (fun uu___1 ->
                   (fun ts ->
                      Obj.magic
                        (FStar_Class_Setlike.remove ()
                           (Obj.magic
                              (FStar_Compiler_RBSet.setlike_rbset
                                 FStar_Class_Ord.ord_string)) trig
                           (Obj.magic ts))) uu___1) l in
            let eligible =
              FStar_Compiler_Util.for_some
                (fun uu___1 ->
                   (Obj.magic
                      (FStar_Class_Setlike.is_empty ()
                         (Obj.magic
                            (FStar_Compiler_RBSet.setlike_rbset
                               FStar_Class_Ord.ord_string)))) uu___1)
                remaining_triggers in
            let uu___1 =
              let uu___2 =
                FStar_Compiler_Util.psmap_add p.assumption_to_triggers aname
                  remaining_triggers in
              {
                macro_freenames = (p.macro_freenames);
                trigger_to_assumption = (p.trigger_to_assumption);
                assumption_to_triggers = uu___2;
                assumption_name_map = (p.assumption_name_map);
                ambients = (p.ambients);
                extra_roots = (p.extra_roots)
              } in
            (uu___1, eligible)
let rec (assumptions_of_decl :
  FStar_SMTEncoding_Term.decl -> FStar_SMTEncoding_Term.assumption Prims.list)
  =
  fun d ->
    match d with
    | FStar_SMTEncoding_Term.Assume a -> [a]
    | FStar_SMTEncoding_Term.Module (uu___, ds) ->
        FStar_Compiler_List.collect assumptions_of_decl ds
    | d1 -> []
let rec (add_decl :
  FStar_SMTEncoding_Term.decl -> pruning_state -> pruning_state) =
  fun d ->
    fun p ->
      match d with
      | FStar_SMTEncoding_Term.Assume a ->
          let triggers1 =
            triggers_of_term a.FStar_SMTEncoding_Term.assumption_term in
          let p1 =
            let uu___ =
              FStar_Compiler_List.map
                (fun uu___1 ->
                   (Obj.magic
                      (FStar_Class_Setlike.elems ()
                         (Obj.magic
                            (FStar_Compiler_RBSet.setlike_rbset
                               FStar_Class_Ord.ord_string)))) uu___1)
                triggers1 in
            FStar_Compiler_List.fold_left
              (FStar_Compiler_List.fold_left (add_trigger_to_assumption a)) p
              uu___ in
          add_assumption_to_triggers a p1 triggers1
      | FStar_SMTEncoding_Term.Module (uu___, ds) ->
          FStar_Compiler_List.fold_left (fun p1 -> fun d1 -> add_decl d1 p1)
            p ds
      | FStar_SMTEncoding_Term.DefineFun (macro, uu___, uu___1, body, uu___2)
          ->
          let free_names =
            let uu___3 = free_top_level_names body in
            FStar_Class_Setlike.elems ()
              (Obj.magic
                 (FStar_Compiler_RBSet.setlike_rbset
                    FStar_Class_Ord.ord_string)) (Obj.magic uu___3) in
          let p1 =
            let uu___3 =
              FStar_Compiler_Util.psmap_add p.macro_freenames macro
                free_names in
            {
              macro_freenames = uu___3;
              trigger_to_assumption = (p.trigger_to_assumption);
              assumption_to_triggers = (p.assumption_to_triggers);
              assumption_name_map = (p.assumption_name_map);
              ambients = (p.ambients);
              extra_roots = (p.extra_roots)
            } in
          p1
      | uu___ -> p
let (add_decls :
  FStar_SMTEncoding_Term.decl Prims.list -> pruning_state -> pruning_state) =
  fun ds ->
    fun p ->
      FStar_Compiler_List.fold_left (fun p1 -> fun d -> add_decl d p1) p ds
type sym = Prims.string
type reached_assumption_names = Prims.string FStar_Compiler_RBSet.rbset
type ctxt = {
  p: pruning_state ;
  reached: reached_assumption_names }
let (__proj__Mkctxt__item__p : ctxt -> pruning_state) =
  fun projectee -> match projectee with | { p; reached;_} -> p
let (__proj__Mkctxt__item__reached : ctxt -> reached_assumption_names) =
  fun projectee -> match projectee with | { p; reached;_} -> reached
type 'a st = ctxt -> ('a * ctxt)
let (get : ctxt st) = fun s -> (s, s)
let (put : ctxt -> unit st) = fun c -> fun uu___ -> ((), c)
let (st_monad : unit st FStar_Class_Monad.monad) =
  {
    FStar_Class_Monad.return =
      (fun uu___1 ->
         fun uu___ ->
           (fun a -> fun x -> fun s -> Obj.magic (x, s)) uu___1 uu___);
    FStar_Class_Monad.op_let_Bang =
      (fun uu___3 ->
         fun uu___2 ->
           fun uu___1 ->
             fun uu___ ->
               (fun a ->
                  fun b ->
                    fun m ->
                      let m = Obj.magic m in
                      fun f ->
                        let f = Obj.magic f in
                        fun s ->
                          let uu___ = m s in
                          match uu___ with
                          | (x, s1) ->
                              let uu___1 = f x in Obj.magic (uu___1 s1))
                 uu___3 uu___2 uu___1 uu___)
  }
let (mark_trigger_reached : sym -> unit st) =
  fun x ->
    FStar_Class_Monad.op_let_Bang st_monad () () (Obj.magic get)
      (fun uu___ ->
         (fun ctxt1 ->
            let ctxt1 = Obj.magic ctxt1 in
            let uu___ =
              let uu___1 = trigger_reached ctxt1.p x in
              { p = uu___1; reached = (ctxt1.reached) } in
            Obj.magic (put uu___)) uu___)
let (find_assumptions_waiting_on_trigger :
  sym -> FStar_SMTEncoding_Term.assumption Prims.list st) =
  fun uu___ ->
    (fun x ->
       Obj.magic
         (FStar_Class_Monad.op_let_Bang st_monad () () (Obj.magic get)
            (fun uu___ ->
               (fun ctxt1 ->
                  let ctxt1 = Obj.magic ctxt1 in
                  let uu___ =
                    FStar_Compiler_Util.psmap_try_find
                      (ctxt1.p).trigger_to_assumption x in
                  match uu___ with
                  | FStar_Pervasives_Native.None ->
                      Obj.magic
                        (FStar_Class_Monad.return st_monad () (Obj.magic []))
                  | FStar_Pervasives_Native.Some l ->
                      Obj.magic
                        (FStar_Class_Monad.return st_monad () (Obj.magic l)))
                 uu___))) uu___
let (reached_assumption : Prims.string -> unit st) =
  fun aname ->
    FStar_Class_Monad.op_let_Bang st_monad () () (Obj.magic get)
      (fun uu___ ->
         (fun ctxt1 ->
            let ctxt1 = Obj.magic ctxt1 in
            let p =
              let uu___ = ctxt1.p in
              let uu___1 =
                FStar_Compiler_Util.psmap_remove
                  (ctxt1.p).assumption_to_triggers aname in
              {
                macro_freenames = (uu___.macro_freenames);
                trigger_to_assumption = (uu___.trigger_to_assumption);
                assumption_to_triggers = uu___1;
                assumption_name_map = (uu___.assumption_name_map);
                ambients = (uu___.ambients);
                extra_roots = (uu___.extra_roots)
              } in
            let uu___ =
              let uu___1 =
                Obj.magic
                  (FStar_Class_Setlike.add ()
                     (Obj.magic
                        (FStar_Compiler_RBSet.setlike_rbset
                           FStar_Class_Ord.ord_string)) aname
                     (Obj.magic ctxt1.reached)) in
              { p = (ctxt1.p); reached = uu___1 } in
            Obj.magic (put uu___)) uu___)
let (remove_trigger_for :
  sym -> FStar_SMTEncoding_Term.assumption -> Prims.bool st) =
  fun uu___1 ->
    fun uu___ ->
      (fun trig ->
         fun a ->
           Obj.magic
             (FStar_Class_Monad.op_let_Bang st_monad () () (Obj.magic get)
                (fun uu___ ->
                   (fun ctxt1 ->
                      let ctxt1 = Obj.magic ctxt1 in
                      let uu___ =
                        remove_trigger_for_assumption ctxt1.p trig
                          a.FStar_SMTEncoding_Term.assumption_name in
                      match uu___ with
                      | (p, eligible) ->
                          let uu___1 = put { p; reached = (ctxt1.reached) } in
                          Obj.magic
                            (FStar_Class_Monad.op_let_Bang st_monad () ()
                               uu___1
                               (fun uu___2 ->
                                  (fun uu___2 ->
                                     let uu___2 = Obj.magic uu___2 in
                                     Obj.magic
                                       (FStar_Class_Monad.return st_monad ()
                                          (Obj.magic eligible))) uu___2)))
                     uu___))) uu___1 uu___
let (already_reached : Prims.string -> Prims.bool st) =
  fun uu___ ->
    (fun aname ->
       Obj.magic
         (FStar_Class_Monad.op_let_Bang st_monad () () (Obj.magic get)
            (fun uu___ ->
               (fun ctxt1 ->
                  let ctxt1 = Obj.magic ctxt1 in
                  let uu___ =
                    FStar_Class_Setlike.mem ()
                      (Obj.magic
                         (FStar_Compiler_RBSet.setlike_rbset
                            FStar_Class_Ord.ord_string)) aname
                      (Obj.magic ctxt1.reached) in
                  Obj.magic
                    (FStar_Class_Monad.return st_monad () (Obj.magic uu___)))
                 uu___))) uu___
let (trigger_pending_assumptions :
  sym Prims.list -> FStar_SMTEncoding_Term.assumption Prims.list st) =
  fun uu___ ->
    (fun lids ->
       Obj.magic
         (FStar_Class_Monad.foldM_left st_monad () ()
            (fun uu___1 ->
               fun uu___ ->
                 (fun acc ->
                    let acc = Obj.magic acc in
                    fun lid ->
                      let lid = Obj.magic lid in
                      let uu___ = find_assumptions_waiting_on_trigger lid in
                      Obj.magic
                        (FStar_Class_Monad.op_let_Bang st_monad () ()
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              (fun uu___1 ->
                                 let uu___1 = Obj.magic uu___1 in
                                 match uu___1 with
                                 | [] ->
                                     Obj.magic
                                       (FStar_Class_Monad.return st_monad ()
                                          (Obj.magic acc))
                                 | assumptions ->
                                     let uu___2 = mark_trigger_reached lid in
                                     Obj.magic
                                       (FStar_Class_Monad.op_let_Bang
                                          st_monad () () uu___2
                                          (fun uu___3 ->
                                             (fun uu___3 ->
                                                let uu___3 = Obj.magic uu___3 in
                                                Obj.magic
                                                  (FStar_Class_Monad.foldM_left
                                                     st_monad () ()
                                                     (fun uu___5 ->
                                                        fun uu___4 ->
                                                          (fun acc1 ->
                                                             let acc1 =
                                                               Obj.magic acc1 in
                                                             fun assumption
                                                               ->
                                                               let assumption
                                                                 =
                                                                 Obj.magic
                                                                   assumption in
                                                               let uu___4 =
                                                                 remove_trigger_for
                                                                   lid
                                                                   assumption in
                                                               Obj.magic
                                                                 (FStar_Class_Monad.op_let_Bang
                                                                    st_monad
                                                                    () ()
                                                                    (
                                                                    Obj.magic
                                                                    uu___4)
                                                                    (
                                                                    fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    let uu___5
                                                                    =
                                                                    Obj.magic
                                                                    uu___5 in
                                                                    if uu___5
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.return
                                                                    st_monad
                                                                    ()
                                                                    (Obj.magic
                                                                    (assumption
                                                                    :: acc1)))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.return
                                                                    st_monad
                                                                    ()
                                                                    (Obj.magic
                                                                    acc1)))
                                                                    uu___5)))
                                                            uu___5 uu___4)
                                                     (Obj.magic acc)
                                                     (Obj.magic assumptions)))
                                               uu___3))) uu___1))) uu___1
                   uu___) (Obj.magic []) (Obj.magic lids))) uu___
let rec (scan : FStar_SMTEncoding_Term.assumption Prims.list -> unit st) =
  fun ds ->
    FStar_Class_Monad.op_let_Bang st_monad () () (Obj.magic get)
      (fun uu___ ->
         (fun ctxt1 ->
            let ctxt1 = Obj.magic ctxt1 in
            let macro_expand s =
              let uu___ =
                FStar_Compiler_Util.psmap_try_find (ctxt1.p).macro_freenames
                  s in
              match uu___ with
              | FStar_Pervasives_Native.None -> [s]
              | FStar_Pervasives_Native.Some l -> s :: l in
            let new_syms =
              FStar_Compiler_List.collect
                (fun a ->
                   let uu___ =
                     let uu___1 = assumption_free_names a in
                     FStar_Class_Setlike.elems ()
                       (Obj.magic
                          (FStar_Compiler_RBSet.setlike_rbset
                             FStar_Class_Ord.ord_string)) (Obj.magic uu___1) in
                   FStar_Compiler_List.collect macro_expand uu___) ds in
            let uu___ = trigger_pending_assumptions new_syms in
            Obj.magic
              (FStar_Class_Monad.op_let_Bang st_monad () () (Obj.magic uu___)
                 (fun uu___1 ->
                    (fun uu___1 ->
                       let uu___1 = Obj.magic uu___1 in
                       match uu___1 with
                       | [] ->
                           Obj.magic
                             (FStar_Class_Monad.return st_monad ()
                                (Obj.repr ()))
                       | triggered ->
                           let uu___2 =
                             Obj.magic
                               (FStar_Class_Monad.foldM_left st_monad () ()
                                  (fun uu___4 ->
                                     fun uu___3 ->
                                       (fun acc ->
                                          let acc = Obj.magic acc in
                                          fun assumption ->
                                            let assumption =
                                              Obj.magic assumption in
                                            let uu___3 =
                                              already_reached
                                                assumption.FStar_SMTEncoding_Term.assumption_name in
                                            Obj.magic
                                              (FStar_Class_Monad.op_let_Bang
                                                 st_monad () ()
                                                 (Obj.magic uu___3)
                                                 (fun uu___4 ->
                                                    (fun uu___4 ->
                                                       let uu___4 =
                                                         Obj.magic uu___4 in
                                                       if uu___4
                                                       then
                                                         Obj.magic
                                                           (FStar_Class_Monad.return
                                                              st_monad ()
                                                              (Obj.magic acc))
                                                       else
                                                         (let uu___6 =
                                                            reached_assumption
                                                              assumption.FStar_SMTEncoding_Term.assumption_name in
                                                          Obj.magic
                                                            (FStar_Class_Monad.op_let_Bang
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
                                                                    (FStar_Class_Monad.return
                                                                    st_monad
                                                                    ()
                                                                    (Obj.magic
                                                                    (assumption
                                                                    :: acc))))
                                                                    uu___7))))
                                                      uu___4))) uu___4 uu___3)
                                  (Obj.magic []) (Obj.magic triggered)) in
                           Obj.magic
                             (FStar_Class_Monad.op_let_Bang st_monad () ()
                                (Obj.magic uu___2)
                                (fun uu___3 ->
                                   (fun to_scan ->
                                      let to_scan = Obj.magic to_scan in
                                      Obj.magic (scan to_scan)) uu___3)))
                      uu___1))) uu___)
let (prune :
  pruning_state ->
    FStar_SMTEncoding_Term.decl Prims.list ->
      FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun p ->
    fun roots ->
      let roots1 = FStar_Compiler_List.collect assumptions_of_decl roots in
      let init1 =
        let uu___ =
          Obj.magic
            (FStar_Class_Setlike.empty ()
               (Obj.magic
                  (FStar_Compiler_RBSet.setlike_rbset
                     FStar_Class_Ord.ord_string)) ()) in
        { p; reached = uu___ } in
      let uu___ =
        let uu___1 = scan (FStar_List_Tot_Base.op_At roots1 p.extra_roots) in
        uu___1 init1 in
      match uu___ with
      | (uu___1, ctxt1) ->
          let reached_names =
            FStar_Class_Setlike.elems ()
              (Obj.magic
                 (FStar_Compiler_RBSet.setlike_rbset
                    FStar_Class_Ord.ord_string)) (Obj.magic ctxt1.reached) in
          let reached_assumptions =
            FStar_Compiler_List.collect
              (fun name ->
                 let uu___2 =
                   FStar_Compiler_Util.psmap_try_find
                     (ctxt1.p).assumption_name_map name in
                 match uu___2 with
                 | FStar_Pervasives_Native.None -> []
                 | FStar_Pervasives_Native.Some a -> [a])
              (FStar_List_Tot_Base.op_At reached_names p.ambients) in
          reached_assumptions