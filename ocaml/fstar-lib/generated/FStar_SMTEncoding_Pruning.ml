open Prims
type triggers = Prims.string Prims.list Prims.list
type pruning_state =
  {
  trigger_to_assumption:
    FStar_SMTEncoding_Term.assumption Prims.list FStar_Compiler_Util.psmap ;
  assumption_to_triggers: triggers FStar_Compiler_Util.psmap ;
  assumption_name_map: FStar_SMTEncoding_Term.decl FStar_Compiler_Util.psmap ;
  ambients: Prims.string Prims.list }
let (__proj__Mkpruning_state__item__trigger_to_assumption :
  pruning_state ->
    FStar_SMTEncoding_Term.assumption Prims.list FStar_Compiler_Util.psmap)
  =
  fun projectee ->
    match projectee with
    | { trigger_to_assumption; assumption_to_triggers; assumption_name_map;
        ambients;_} -> trigger_to_assumption
let (__proj__Mkpruning_state__item__assumption_to_triggers :
  pruning_state -> triggers FStar_Compiler_Util.psmap) =
  fun projectee ->
    match projectee with
    | { trigger_to_assumption; assumption_to_triggers; assumption_name_map;
        ambients;_} -> assumption_to_triggers
let (__proj__Mkpruning_state__item__assumption_name_map :
  pruning_state -> FStar_SMTEncoding_Term.decl FStar_Compiler_Util.psmap) =
  fun projectee ->
    match projectee with
    | { trigger_to_assumption; assumption_to_triggers; assumption_name_map;
        ambients;_} -> assumption_name_map
let (__proj__Mkpruning_state__item__ambients :
  pruning_state -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { trigger_to_assumption; assumption_to_triggers; assumption_name_map;
        ambients;_} -> ambients
let (init : pruning_state) =
  let uu___ = FStar_Compiler_Util.psmap_empty () in
  let uu___1 = FStar_Compiler_Util.psmap_empty () in
  let uu___2 = FStar_Compiler_Util.psmap_empty () in
  {
    trigger_to_assumption = uu___;
    assumption_to_triggers = uu___1;
    assumption_name_map = uu___2;
    ambients = []
  }
let (add_assumption_to_triggers :
  FStar_SMTEncoding_Term.assumption ->
    pruning_state -> triggers -> pruning_state)
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
            trigger_to_assumption = (p.trigger_to_assumption);
            assumption_to_triggers = (p.assumption_to_triggers);
            assumption_name_map = uu___;
            ambients = (p.ambients)
          } in
        match trigs with
        | [] ->
            {
              trigger_to_assumption = (p1.trigger_to_assumption);
              assumption_to_triggers = (p1.assumption_to_triggers);
              assumption_name_map = (p1.assumption_name_map);
              ambients = ((a.FStar_SMTEncoding_Term.assumption_name) ::
                (p1.ambients))
            }
        | uu___ ->
            let uu___1 =
              FStar_Compiler_Util.psmap_add p1.assumption_to_triggers
                a.FStar_SMTEncoding_Term.assumption_name trigs in
            {
              trigger_to_assumption = (p1.trigger_to_assumption);
              assumption_to_triggers = uu___1;
              assumption_name_map = (p1.assumption_name_map);
              ambients = (p1.ambients)
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
              trigger_to_assumption = uu___1;
              assumption_to_triggers = (p.assumption_to_triggers);
              assumption_name_map = (p.assumption_name_map);
              ambients = (p.ambients)
            }
        | FStar_Pervasives_Native.Some l ->
            let uu___1 =
              FStar_Compiler_Util.psmap_add p.trigger_to_assumption trig (a
                :: l) in
            {
              trigger_to_assumption = uu___1;
              assumption_to_triggers = (p.assumption_to_triggers);
              assumption_name_map = (p.assumption_name_map);
              ambients = (p.ambients)
            }
let (trigger_reached : pruning_state -> Prims.string -> pruning_state) =
  fun p ->
    fun trig ->
      let uu___ =
        FStar_Compiler_Util.psmap_remove p.trigger_to_assumption trig in
      {
        trigger_to_assumption = uu___;
        assumption_to_triggers = (p.assumption_to_triggers);
        assumption_name_map = (p.assumption_name_map);
        ambients = (p.ambients)
      }
let (remove_trigger_for_assumption :
  pruning_state ->
    Prims.string -> Prims.string -> (pruning_state * Prims.bool))
  =
  fun p ->
    fun aname ->
      fun trig ->
        let uu___ =
          FStar_Compiler_Util.psmap_try_find p.assumption_to_triggers aname in
        match uu___ with
        | FStar_Pervasives_Native.None -> (p, false)
        | FStar_Pervasives_Native.Some l ->
            let remaining_triggers =
              FStar_Compiler_List.map
                (fun disjunct ->
                   FStar_Compiler_List.filter (fun x -> x <> trig) disjunct)
                l in
            let eligible =
              FStar_Compiler_Util.for_some Prims.uu___is_Nil
                remaining_triggers in
            let uu___1 =
              let uu___2 =
                FStar_Compiler_Util.psmap_add p.assumption_to_triggers aname
                  remaining_triggers in
              {
                trigger_to_assumption = (p.trigger_to_assumption);
                assumption_to_triggers = uu___2;
                assumption_name_map = (p.assumption_name_map);
                ambients = (p.ambients)
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
let (triggers_of_assumption : FStar_SMTEncoding_Term.assumption -> triggers)
  =
  fun a ->
    let rec aux t =
      match t.FStar_SMTEncoding_Term.tm with
      | FStar_SMTEncoding_Term.Quant
          (FStar_SMTEncoding_Term.Forall, triggers1, uu___, uu___1, uu___2)
          ->
          FStar_Compiler_List.map
            (fun disjunct ->
               FStar_Compiler_List.collect
                 (fun t1 ->
                    let uu___3 =
                      FStar_SMTEncoding_Term.free_top_level_names t1 in
                    FStar_Class_Setlike.elems ()
                      (Obj.magic
                         (FStar_Compiler_RBSet.setlike_rbset
                            FStar_Class_Ord.ord_string)) (Obj.magic uu___3))
                 disjunct) triggers1
      | FStar_SMTEncoding_Term.Labeled (t1, uu___, uu___1) -> aux t1
      | FStar_SMTEncoding_Term.LblPos (t1, uu___) -> aux t1
      | uu___ -> [] in
    aux a.FStar_SMTEncoding_Term.assumption_term
let (add_assumptions :
  FStar_SMTEncoding_Term.decl Prims.list -> pruning_state -> pruning_state) =
  fun ds ->
    fun p ->
      let assumptions = FStar_Compiler_List.collect assumptions_of_decl ds in
      let p1 =
        FStar_Compiler_List.fold_left
          (fun p2 ->
             fun a ->
               let triggers1 = triggers_of_assumption a in
               let p3 =
                 FStar_Compiler_List.fold_left
                   (FStar_Compiler_List.fold_left
                      (add_trigger_to_assumption a)) p2 triggers1 in
               add_assumption_to_triggers a p3 triggers1) p assumptions in
      p1
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
  sym Prims.list ->
    (FStar_SMTEncoding_Term.assumption Prims.list, Prims.bool)
      FStar_Pervasives.either st)
  =
  fun uu___ ->
    (fun lids ->
       let join_acc acc next =
         match (acc, next) with
         | (FStar_Pervasives.Inl l, FStar_Pervasives.Inl m) ->
             FStar_Pervasives.Inl (FStar_List_Tot_Base.op_At l m)
         | (FStar_Pervasives.Inl l, FStar_Pervasives.Inr uu___) ->
             FStar_Pervasives.Inl l
         | (FStar_Pervasives.Inr uu___, FStar_Pervasives.Inl m) ->
             FStar_Pervasives.Inl m
         | (FStar_Pervasives.Inr l, FStar_Pervasives.Inr m) ->
             FStar_Pervasives.Inr (l || m) in
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
                                                let uu___4 =
                                                  Obj.magic
                                                    (FStar_Class_Monad.foldM_left
                                                       st_monad () ()
                                                       (fun uu___6 ->
                                                          fun uu___5 ->
                                                            (fun acc1 ->
                                                               let acc1 =
                                                                 Obj.magic
                                                                   acc1 in
                                                               fun assumption
                                                                 ->
                                                                 let assumption
                                                                   =
                                                                   Obj.magic
                                                                    assumption in
                                                                 let uu___5 =
                                                                   remove_trigger_for
                                                                    lid
                                                                    assumption in
                                                                 Obj.magic
                                                                   (FStar_Class_Monad.op_let_Bang
                                                                    st_monad
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___5)
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    let uu___6
                                                                    =
                                                                    Obj.magic
                                                                    uu___6 in
                                                                    if uu___6
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
                                                                    uu___6)))
                                                              uu___6 uu___5)
                                                       (Obj.magic [])
                                                       (Obj.magic assumptions)) in
                                                Obj.magic
                                                  (FStar_Class_Monad.op_let_Bang
                                                     st_monad () ()
                                                     (Obj.magic uu___4)
                                                     (fun uu___5 ->
                                                        (fun
                                                           eligible_assumptions
                                                           ->
                                                           let eligible_assumptions
                                                             =
                                                             Obj.magic
                                                               eligible_assumptions in
                                                           match eligible_assumptions
                                                           with
                                                           | [] ->
                                                               Obj.magic
                                                                 (FStar_Class_Monad.return
                                                                    st_monad
                                                                    ()
                                                                    (
                                                                    Obj.magic
                                                                    (join_acc
                                                                    acc
                                                                    (FStar_Pervasives.Inr
                                                                    true))))
                                                           | uu___5 ->
                                                               Obj.magic
                                                                 (FStar_Class_Monad.return
                                                                    st_monad
                                                                    ()
                                                                    (
                                                                    Obj.magic
                                                                    (join_acc
                                                                    acc
                                                                    (FStar_Pervasives.Inl
                                                                    eligible_assumptions)))))
                                                          uu___5))) uu___3)))
                                uu___1))) uu___1 uu___)
            (Obj.magic (FStar_Pervasives.Inr false)) (Obj.magic lids))) uu___
let rec (scan : FStar_SMTEncoding_Term.assumption Prims.list -> unit st) =
  fun ds ->
    let new_syms =
      FStar_Compiler_List.collect
        (fun a -> a.FStar_SMTEncoding_Term.assumption_free_names) ds in
    let uu___ = trigger_pending_assumptions new_syms in
    FStar_Class_Monad.op_let_Bang st_monad () () (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            let uu___1 = Obj.magic uu___1 in
            match uu___1 with
            | FStar_Pervasives.Inl triggered ->
                let uu___2 =
                  Obj.magic
                    (FStar_Class_Monad.foldM_left st_monad () ()
                       (fun uu___4 ->
                          fun uu___3 ->
                            (fun acc ->
                               let acc = Obj.magic acc in
                               fun assumption ->
                                 let assumption = Obj.magic assumption in
                                 let uu___3 =
                                   already_reached
                                     assumption.FStar_SMTEncoding_Term.assumption_name in
                                 Obj.magic
                                   (FStar_Class_Monad.op_let_Bang st_monad ()
                                      () (Obj.magic uu___3)
                                      (fun uu___4 ->
                                         (fun uu___4 ->
                                            let uu___4 = Obj.magic uu___4 in
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
                                                    st_monad () () uu___6
                                                    (fun uu___7 ->
                                                       (fun uu___7 ->
                                                          let uu___7 =
                                                            Obj.magic uu___7 in
                                                          Obj.magic
                                                            (FStar_Class_Monad.return
                                                               st_monad ()
                                                               (Obj.magic
                                                                  (assumption
                                                                  :: acc))))
                                                         uu___7)))) uu___4)))
                              uu___4 uu___3) (Obj.magic [])
                       (Obj.magic triggered)) in
                Obj.magic
                  (FStar_Class_Monad.op_let_Bang st_monad () ()
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun to_scan ->
                           let to_scan = Obj.magic to_scan in
                           Obj.magic (scan to_scan)) uu___3))
            | FStar_Pervasives.Inr uu___2 ->
                Obj.magic
                  (FStar_Class_Monad.return st_monad () (Obj.repr ())))
           uu___1)
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
      let uu___ = let uu___1 = scan roots1 in uu___1 init1 in
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