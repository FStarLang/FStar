open Prims
type lid_set = FStar_Ident.lident FStar_Compiler_RBSet.rbset
type ctxt =
  {
  env: FStar_TypeChecker_Env.env ;
  reached: lid_set ;
  pending_lemmas: FStar_TypeChecker_Env.pending_lemma_patterns }
let (__proj__Mkctxt__item__env : ctxt -> FStar_TypeChecker_Env.env) =
  fun projectee ->
    match projectee with | { env; reached; pending_lemmas;_} -> env
let (__proj__Mkctxt__item__reached : ctxt -> lid_set) =
  fun projectee ->
    match projectee with | { env; reached; pending_lemmas;_} -> reached
let (__proj__Mkctxt__item__pending_lemmas :
  ctxt -> FStar_TypeChecker_Env.pending_lemma_patterns) =
  fun projectee ->
    match projectee with
    | { env; reached; pending_lemmas;_} -> pending_lemmas
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
let (remove_trigger : FStar_Ident.lident -> unit st) =
  fun lid ->
    FStar_Class_Monad.op_let_Bang st_monad () () (Obj.magic get)
      (fun uu___ ->
         (fun ctxt1 ->
            let ctxt1 = Obj.magic ctxt1 in
            let uu___ =
              let uu___1 =
                FStar_TypeChecker_Env.remove_pending_lemma lid
                  ctxt1.pending_lemmas in
              {
                env = (ctxt1.env);
                reached = (ctxt1.reached);
                pending_lemmas = uu___1
              } in
            Obj.magic (put uu___)) uu___)
let (find_lemmas_waiting_on_trigger :
  FStar_Ident.lident -> FStar_Ident.lident Prims.list st) =
  fun uu___ ->
    (fun lid ->
       Obj.magic
         (FStar_Class_Monad.op_let_Bang st_monad () () (Obj.magic get)
            (fun uu___ ->
               (fun ctxt1 ->
                  let ctxt1 = Obj.magic ctxt1 in
                  let lems =
                    FStar_TypeChecker_Env.find_lemmas_waiting_on_trigger lid
                      ctxt1.pending_lemmas in
                  Obj.magic
                    (FStar_Class_Monad.return st_monad () (Obj.magic lems)))
                 uu___))) uu___
let (add_lident : FStar_Ident.lident -> unit st) =
  fun x ->
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
                           FStar_Syntax_Syntax.ord_fv)) x
                     (Obj.magic ctxt1.reached)) in
              {
                env = (ctxt1.env);
                reached = uu___1;
                pending_lemmas = (ctxt1.pending_lemmas)
              } in
            Obj.magic (put uu___)) uu___)
let (remove_trigger_for_lemma :
  FStar_Ident.lident -> FStar_Ident.lident -> Prims.bool st) =
  fun uu___1 ->
    fun uu___ ->
      (fun pat ->
         fun lem ->
           Obj.magic
             (FStar_Class_Monad.op_let_Bang st_monad () () (Obj.magic get)
                (fun uu___ ->
                   (fun ctxt1 ->
                      let ctxt1 = Obj.magic ctxt1 in
                      let uu___ =
                        FStar_TypeChecker_Env.remove_trigger_for_lemma pat
                          lem ctxt1.pending_lemmas in
                      match uu___ with
                      | (pp, eligible) ->
                          let uu___1 =
                            put
                              {
                                env = (ctxt1.env);
                                reached = (ctxt1.reached);
                                pending_lemmas = pp
                              } in
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
let (ctx_contains : FStar_Ident.lident -> Prims.bool st) =
  fun uu___ ->
    (fun x ->
       Obj.magic
         (FStar_Class_Monad.op_let_Bang st_monad () () (Obj.magic get)
            (fun uu___ ->
               (fun ctxt1 ->
                  let ctxt1 = Obj.magic ctxt1 in
                  let uu___ =
                    FStar_Class_Setlike.mem ()
                      (Obj.magic
                         (FStar_Compiler_RBSet.setlike_rbset
                            FStar_Syntax_Syntax.ord_fv)) x
                      (Obj.magic ctxt1.reached) in
                  Obj.magic
                    (FStar_Class_Monad.return st_monad () (Obj.magic uu___)))
                 uu___))) uu___
let (reachable_of_inductive :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.typ Prims.list))
  =
  fun env ->
    fun ty ->
      let aux uu___ ty1 =
        match uu___ with
        | (a_lids, a_tys) ->
            let uu___1 = FStar_TypeChecker_Env.datacons_of_typ env ty1 in
            (match uu___1 with
             | (uu___2, dcs) ->
                 let tys =
                   FStar_Compiler_List.collect
                     (fun dc ->
                        let uu___3 =
                          FStar_TypeChecker_Env.try_lookup_lid env dc in
                        match uu___3 with
                        | FStar_Pervasives_Native.None -> []
                        | FStar_Pervasives_Native.Some ((uu___4, t), uu___5)
                            -> [t]) dcs in
                 let tys1 =
                   let uu___3 = FStar_TypeChecker_Env.try_lookup_lid env ty1 in
                   match uu___3 with
                   | FStar_Pervasives_Native.None -> tys
                   | FStar_Pervasives_Native.Some ((uu___4, t), uu___5) -> t
                       :: tys in
                 ((FStar_List_Tot_Base.op_At dcs a_lids),
                   (FStar_List_Tot_Base.op_At tys1 a_tys))) in
      let aux1 mutuals = FStar_Compiler_List.fold_left aux ([], []) mutuals in
      let uu___ = FStar_TypeChecker_Env.lookup_qname env ty in
      match uu___ with
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives.Inr (se, uu___1), uu___2) ->
          (match se.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ
               { FStar_Syntax_Syntax.lid = uu___3;
                 FStar_Syntax_Syntax.us = uu___4;
                 FStar_Syntax_Syntax.params = uu___5;
                 FStar_Syntax_Syntax.num_uniform_params = uu___6;
                 FStar_Syntax_Syntax.t = uu___7;
                 FStar_Syntax_Syntax.mutuals = mutuals;
                 FStar_Syntax_Syntax.ds = uu___8;
                 FStar_Syntax_Syntax.injective_type_params = uu___9;_}
               -> aux1 mutuals
           | uu___3 -> ([], []))
      | uu___1 -> ([], [])
let (lookup_lident_in_env :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.term Prims.list))
  =
  fun env ->
    fun x ->
      let uu___ = FStar_TypeChecker_Env.lookup_qname env x in
      match uu___ with
      | FStar_Pervasives_Native.None -> ([], [])
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives.Inl (uu___1, t), uu___2) -> ([], [t])
      | FStar_Pervasives_Native.Some
          (FStar_Pervasives.Inr (se, uu___1), uu___2) ->
          (match se.FStar_Syntax_Syntax.sigel with
           | FStar_Syntax_Syntax.Sig_inductive_typ
               { FStar_Syntax_Syntax.lid = lid;
                 FStar_Syntax_Syntax.us = uu___3;
                 FStar_Syntax_Syntax.params = uu___4;
                 FStar_Syntax_Syntax.num_uniform_params = uu___5;
                 FStar_Syntax_Syntax.t = uu___6;
                 FStar_Syntax_Syntax.mutuals = uu___7;
                 FStar_Syntax_Syntax.ds = uu___8;
                 FStar_Syntax_Syntax.injective_type_params = uu___9;_}
               -> reachable_of_inductive env lid
           | FStar_Syntax_Syntax.Sig_datacon
               { FStar_Syntax_Syntax.lid1 = uu___3;
                 FStar_Syntax_Syntax.us1 = uu___4;
                 FStar_Syntax_Syntax.t1 = uu___5;
                 FStar_Syntax_Syntax.ty_lid = ty_lid;
                 FStar_Syntax_Syntax.num_ty_params = uu___6;
                 FStar_Syntax_Syntax.mutuals1 = uu___7;
                 FStar_Syntax_Syntax.injective_type_params1 = uu___8;_}
               -> reachable_of_inductive env ty_lid
           | FStar_Syntax_Syntax.Sig_declare_typ
               { FStar_Syntax_Syntax.lid2 = uu___3;
                 FStar_Syntax_Syntax.us2 = uu___4;
                 FStar_Syntax_Syntax.t2 = t;_}
               -> ([], [t])
           | FStar_Syntax_Syntax.Sig_let
               { FStar_Syntax_Syntax.lbs1 = lbs;
                 FStar_Syntax_Syntax.lids1 = mutuals;_}
               ->
               let uu___3 =
                 FStar_Compiler_List.collect
                   (fun lb ->
                      [lb.FStar_Syntax_Syntax.lbtyp;
                      lb.FStar_Syntax_Syntax.lbdef])
                   (FStar_Pervasives_Native.snd lbs) in
               (mutuals, uu___3)
           | FStar_Syntax_Syntax.Sig_assume
               { FStar_Syntax_Syntax.lid3 = uu___3;
                 FStar_Syntax_Syntax.us3 = uu___4;
                 FStar_Syntax_Syntax.phi1 = phi;_}
               -> ([], [phi])
           | uu___3 -> ([], []))
let (lookup_definition_and_type :
  FStar_Ident.lident ->
    (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.term Prims.list) st)
  =
  fun uu___ ->
    (fun x ->
       Obj.magic
         (FStar_Class_Monad.op_let_Bang st_monad () () (Obj.magic get)
            (fun uu___ ->
               (fun ctxt1 ->
                  let ctxt1 = Obj.magic ctxt1 in
                  let res = lookup_lident_in_env ctxt1.env x in
                  Obj.magic
                    (FStar_Class_Monad.return st_monad () (Obj.magic res)))
                 uu___))) uu___
let (lookup_type :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option st)
  =
  fun uu___ ->
    (fun x ->
       Obj.magic
         (FStar_Class_Monad.op_let_Bang st_monad () () (Obj.magic get)
            (fun uu___ ->
               (fun ctxt1 ->
                  let ctxt1 = Obj.magic ctxt1 in
                  let uu___ =
                    FStar_TypeChecker_Env.try_lookup_lid ctxt1.env x in
                  match uu___ with
                  | FStar_Pervasives_Native.None ->
                      Obj.magic
                        (FStar_Class_Monad.return st_monad ()
                           (Obj.magic FStar_Pervasives_Native.None))
                  | FStar_Pervasives_Native.Some ((uu___1, t), uu___2) ->
                      Obj.magic
                        (FStar_Class_Monad.return st_monad ()
                           (Obj.magic (FStar_Pervasives_Native.Some t))))
                 uu___))) uu___
let rec (context_of_term :
  FStar_Syntax_Syntax.term -> FStar_Ident.lident Prims.list st) =
  fun uu___ ->
    (fun t ->
       let fvs = FStar_Syntax_Free.fvars t in
       let uu___ =
         FStar_Class_Setlike.elems ()
           (Obj.magic
              (FStar_Compiler_RBSet.setlike_rbset FStar_Syntax_Syntax.ord_fv))
           (Obj.magic fvs) in
       Obj.magic
         (FStar_Class_Monad.foldM_left st_monad () ()
            (fun uu___2 ->
               fun uu___1 ->
                 (fun acc ->
                    let acc = Obj.magic acc in
                    fun fv ->
                      let fv = Obj.magic fv in
                      let uu___1 = ctx_contains fv in
                      Obj.magic
                        (FStar_Class_Monad.op_let_Bang st_monad () ()
                           (Obj.magic uu___1)
                           (fun uu___2 ->
                              (fun uu___2 ->
                                 let uu___2 = Obj.magic uu___2 in
                                 if uu___2
                                 then
                                   Obj.magic
                                     (FStar_Class_Monad.return st_monad ()
                                        (Obj.magic acc))
                                 else
                                   (let uu___4 = add_lident fv in
                                    Obj.magic
                                      (FStar_Class_Monad.op_let_Bang st_monad
                                         () () uu___4
                                         (fun uu___5 ->
                                            (fun uu___5 ->
                                               let uu___5 = Obj.magic uu___5 in
                                               let uu___6 =
                                                 lookup_definition_and_type
                                                   fv in
                                               Obj.magic
                                                 (FStar_Class_Monad.op_let_Bang
                                                    st_monad () ()
                                                    (Obj.magic uu___6)
                                                    (fun uu___7 ->
                                                       (fun uu___7 ->
                                                          let uu___7 =
                                                            Obj.magic uu___7 in
                                                          match uu___7 with
                                                          | (lids, terms) ->
                                                              let uu___8 =
                                                                FStar_Class_Monad.iterM
                                                                  st_monad ()
                                                                  (fun uu___9
                                                                    ->
                                                                    (fun lid
                                                                    ->
                                                                    let lid =
                                                                    Obj.magic
                                                                    lid in
                                                                    Obj.magic
                                                                    (add_lident
                                                                    lid))
                                                                    uu___9)
                                                                  (Obj.magic
                                                                    lids) in
                                                              Obj.magic
                                                                (FStar_Class_Monad.op_let_Bang
                                                                   st_monad
                                                                   () ()
                                                                   uu___8
                                                                   (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    uu___9 in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.foldM_left
                                                                    st_monad
                                                                    () ()
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    fun
                                                                    uu___10
                                                                    ->
                                                                    (fun acc1
                                                                    ->
                                                                    let acc1
                                                                    =
                                                                    Obj.magic
                                                                    acc1 in
                                                                    fun t1 ->
                                                                    let t1 =
                                                                    Obj.magic
                                                                    t1 in
                                                                    let uu___10
                                                                    =
                                                                    context_of_term
                                                                    t1 in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    st_monad
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun fvs1
                                                                    ->
                                                                    let fvs1
                                                                    =
                                                                    Obj.magic
                                                                    fvs1 in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.return
                                                                    st_monad
                                                                    ()
                                                                    (Obj.magic
                                                                    (FStar_List_Tot_Base.op_At
                                                                    fvs1 acc1))))
                                                                    uu___11)))
                                                                    uu___11
                                                                    uu___10)
                                                                    (Obj.magic
                                                                    (FStar_List_Tot_Base.op_At
                                                                    (fv ::
                                                                    lids) acc))
                                                                    (Obj.magic
                                                                    terms)))
                                                                    uu___9)))
                                                         uu___7))) uu___5))))
                                uu___2))) uu___2 uu___1) (Obj.magic [])
            (Obj.magic uu___))) uu___
let (trigger_pending_lemmas :
  FStar_Ident.lident Prims.list ->
    (FStar_Ident.lident Prims.list, Prims.bool) FStar_Pervasives.either st)
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
                      let uu___ = find_lemmas_waiting_on_trigger lid in
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
                                 | lemmas ->
                                     let uu___2 = remove_trigger lid in
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
                                                               fun lem ->
                                                                 let lem =
                                                                   Obj.magic
                                                                    lem in
                                                                 let uu___5 =
                                                                   remove_trigger_for_lemma
                                                                    lid lem in
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
                                                                    (lem ::
                                                                    acc1)))
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
                                                       (Obj.magic lemmas)) in
                                                Obj.magic
                                                  (FStar_Class_Monad.op_let_Bang
                                                     st_monad () ()
                                                     (Obj.magic uu___4)
                                                     (fun uu___5 ->
                                                        (fun eligible_lemmas
                                                           ->
                                                           let eligible_lemmas
                                                             =
                                                             Obj.magic
                                                               eligible_lemmas in
                                                           match eligible_lemmas
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
                                                                    eligible_lemmas)))))
                                                          uu___5))) uu___3)))
                                uu___1))) uu___1 uu___)
            (Obj.magic (FStar_Pervasives.Inr false)) (Obj.magic lids))) uu___
let rec (scan : FStar_Syntax_Syntax.term Prims.list -> unit st) =
  fun ts ->
    let uu___ =
      Obj.magic
        (FStar_Class_Monad.foldM_left st_monad () ()
           (fun uu___2 ->
              fun uu___1 ->
                (fun acc ->
                   let acc = Obj.magic acc in
                   fun t ->
                     let t = Obj.magic t in
                     let uu___1 = context_of_term t in
                     Obj.magic
                       (FStar_Class_Monad.op_let_Bang st_monad () ()
                          (Obj.magic uu___1)
                          (fun uu___2 ->
                             (fun new_fvs ->
                                let new_fvs = Obj.magic new_fvs in
                                Obj.magic
                                  (FStar_Class_Monad.return st_monad ()
                                     (Obj.magic
                                        (FStar_List_Tot_Base.op_At new_fvs
                                           acc)))) uu___2))) uu___2 uu___1)
           (Obj.magic []) (Obj.magic ts)) in
    FStar_Class_Monad.op_let_Bang st_monad () () (Obj.magic uu___)
      (fun uu___1 ->
         (fun new_fvs ->
            let new_fvs = Obj.magic new_fvs in
            let uu___1 = trigger_pending_lemmas new_fvs in
            Obj.magic
              (FStar_Class_Monad.op_let_Bang st_monad () ()
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    (fun uu___2 ->
                       let uu___2 = Obj.magic uu___2 in
                       match uu___2 with
                       | FStar_Pervasives.Inl triggered ->
                           let uu___3 =
                             Obj.magic
                               (FStar_Class_Monad.foldM_left st_monad () ()
                                  (fun uu___5 ->
                                     fun uu___4 ->
                                       (fun acc ->
                                          let acc = Obj.magic acc in
                                          fun lem ->
                                            let lem = Obj.magic lem in
                                            let uu___4 = ctx_contains lem in
                                            Obj.magic
                                              (FStar_Class_Monad.op_let_Bang
                                                 st_monad () ()
                                                 (Obj.magic uu___4)
                                                 (fun uu___5 ->
                                                    (fun uu___5 ->
                                                       let uu___5 =
                                                         Obj.magic uu___5 in
                                                       if uu___5
                                                       then
                                                         Obj.magic
                                                           (FStar_Class_Monad.return
                                                              st_monad ()
                                                              (Obj.magic acc))
                                                       else
                                                         (let uu___7 =
                                                            add_lident lem in
                                                          Obj.magic
                                                            (FStar_Class_Monad.op_let_Bang
                                                               st_monad () ()
                                                               uu___7
                                                               (fun uu___8 ->
                                                                  (fun uu___8
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    uu___8 in
                                                                    let uu___9
                                                                    =
                                                                    lookup_type
                                                                    lem in
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.op_let_Bang
                                                                    st_monad
                                                                    () ()
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    uu___10 in
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.return
                                                                    st_monad
                                                                    ()
                                                                    (Obj.magic
                                                                    acc))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    t ->
                                                                    Obj.magic
                                                                    (FStar_Class_Monad.return
                                                                    st_monad
                                                                    ()
                                                                    (Obj.magic
                                                                    (t ::
                                                                    acc))))
                                                                    uu___10)))
                                                                    uu___8))))
                                                      uu___5))) uu___5 uu___4)
                                  (Obj.magic []) (Obj.magic triggered)) in
                           Obj.magic
                             (FStar_Class_Monad.op_let_Bang st_monad () ()
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   (fun lemma_types ->
                                      let lemma_types = Obj.magic lemma_types in
                                      Obj.magic (scan lemma_types)) uu___4))
                       | FStar_Pervasives.Inr uu___3 ->
                           Obj.magic
                             (FStar_Class_Monad.return st_monad ()
                                (Obj.repr ()))) uu___2))) uu___1)
let (context_of :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term Prims.list -> FStar_Ident.lident Prims.list)
  =
  fun env ->
    fun ts ->
      let init =
        let uu___ =
          Obj.magic
            (FStar_Class_Setlike.empty ()
               (Obj.magic
                  (FStar_Compiler_RBSet.setlike_rbset
                     FStar_Syntax_Syntax.ord_fv)) ()) in
        {
          env;
          reached = uu___;
          pending_lemmas = (env.FStar_TypeChecker_Env.pending_lemmas)
        } in
      let uu___ = let uu___1 = scan ts in uu___1 init in
      match uu___ with
      | (uu___1, ctxt1) ->
          FStar_Class_Setlike.elems ()
            (Obj.magic
               (FStar_Compiler_RBSet.setlike_rbset FStar_Syntax_Syntax.ord_fv))
            (Obj.magic ctxt1.reached)