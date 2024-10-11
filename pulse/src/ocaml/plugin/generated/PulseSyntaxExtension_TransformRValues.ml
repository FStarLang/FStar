open Prims
type mutvar_entry =
  (FStarC_Ident.ident * FStarC_Syntax_Syntax.bv * FStarC_Ident.ident
    FStar_Pervasives_Native.option)
type menv =
  {
  map: mutvar_entry Prims.list ;
  env: PulseSyntaxExtension_Env.env_t }
let (__proj__Mkmenv__item__map : menv -> mutvar_entry Prims.list) =
  fun projectee -> match projectee with | { map; env;_} -> map
let (__proj__Mkmenv__item__env : menv -> PulseSyntaxExtension_Env.env_t) =
  fun projectee -> match projectee with | { map; env;_} -> env
let (menv_push_ns : menv -> FStarC_Ident.lid -> menv) =
  fun m ->
    fun ns ->
      let uu___ = PulseSyntaxExtension_Env.push_namespace m.env ns in
      { map = (m.map); env = uu___ }
let (menv_push_bv :
  menv ->
    FStarC_Ident.ident ->
      PulseSyntaxExtension_Sugar.mut_or_ref FStar_Pervasives_Native.option ->
        Prims.bool -> menv)
  =
  fun m ->
    fun x ->
      fun q ->
        fun auto_deref_applicable ->
          let uu___ = PulseSyntaxExtension_Env.push_bv m.env x in
          match uu___ with
          | (env, bv) ->
              let m1 = { map = (m.map); env } in
              if
                (q =
                   (FStar_Pervasives_Native.Some
                      PulseSyntaxExtension_Sugar.MUT))
                  && auto_deref_applicable
              then
                {
                  map = ((x, bv, FStar_Pervasives_Native.None) :: (m1.map));
                  env = (m1.env)
                }
              else m1
let (menv_push_bvs : menv -> FStarC_Ident.ident Prims.list -> menv) =
  fun m ->
    fun xs ->
      let uu___ =
        let uu___1 = PulseSyntaxExtension_Env.push_bvs m.env xs in
        FStar_Pervasives_Native.fst uu___1 in
      { map = (m.map); env = uu___ }
let (is_mut :
  menv ->
    FStarC_Syntax_Syntax.bv ->
      FStarC_Ident.ident FStar_Pervasives_Native.option
        FStar_Pervasives_Native.option)
  =
  fun m ->
    fun x ->
      let uu___ =
        FStarC_Compiler_List.tryFind
          (fun uu___1 ->
             match uu___1 with
             | (uu___2, y, uu___3) -> FStarC_Syntax_Syntax.bv_eq x y) 
          m.map in
      match uu___ with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (uu___1, uu___2, curval) ->
          FStar_Pervasives_Native.Some curval
type needs_derefs = (FStarC_Ident.ident * FStarC_Ident.ident) Prims.list
let (fresh_var :
  FStarC_Ident.ident -> FStarC_Ident.ident PulseSyntaxExtension_Err.err) =
  fun uu___ ->
    (fun nm ->
       Obj.magic
         (FStarC_Class_Monad.op_let_Bang PulseSyntaxExtension_Err.err_monad
            () () (Obj.magic PulseSyntaxExtension_Err.next_ctr)
            (fun uu___ ->
               (fun ctr ->
                  let ctr = Obj.magic ctr in
                  let s =
                    let uu___ =
                      FStarC_Class_Show.show FStarC_Ident.showable_ident nm in
                    let uu___1 =
                      let uu___2 =
                        FStarC_Class_Show.show
                          (FStarC_Class_Show.printableshow
                             FStar_Class_Printable.printable_nat) ctr in
                      Prims.strcat "@" uu___2 in
                    Prims.strcat uu___ uu___1 in
                  let uu___ =
                    let uu___1 =
                      let uu___2 = FStarC_Ident.range_of_id nm in (s, uu___2) in
                    FStarC_Ident.mk_ident uu___1 in
                  Obj.magic (PulseSyntaxExtension_Err.return uu___)) uu___)))
      uu___
let (bind_curval : menv -> FStarC_Ident.ident -> FStarC_Ident.ident -> menv)
  =
  fun m ->
    fun x ->
      fun curval ->
        let uu___ =
          FStarC_Compiler_List.tryFind
            (fun uu___1 ->
               match uu___1 with
               | (y, uu___2, uu___3) -> FStarC_Ident.ident_equals x y) 
            m.map in
        match uu___ with
        | FStar_Pervasives_Native.None -> failwith "Impossible 1"
        | FStar_Pervasives_Native.Some (x1, bv, uu___1) ->
            {
              map = ((x1, bv, (FStar_Pervasives_Native.Some curval)) ::
                (m.map));
              env = (m.env)
            }
let (clear_curval : menv -> FStarC_Ident.ident -> menv) =
  fun m ->
    fun x ->
      let uu___ =
        FStarC_Compiler_List.tryFind
          (fun uu___1 ->
             match uu___1 with
             | (y, uu___2, uu___3) -> FStarC_Ident.ident_equals x y) 
          m.map in
      match uu___ with
      | FStar_Pervasives_Native.None -> failwith "Impossible 2"
      | FStar_Pervasives_Native.Some (x1, bv, uu___1) ->
          {
            map = ((x1, bv, FStar_Pervasives_Native.None) :: (m.map));
            env = (m.env)
          }
let (bind_curvals : menv -> needs_derefs -> menv) =
  fun m ->
    fun l ->
      FStarC_Compiler_List.fold_left
        (fun m1 ->
           fun uu___ -> match uu___ with | (x, y) -> bind_curval m1 x y) m l
let (resolve_mut :
  menv ->
    FStarC_Parser_AST.term -> mutvar_entry FStar_Pervasives_Native.option)
  =
  fun m ->
    fun e ->
      match e.FStarC_Parser_AST.tm with
      | FStarC_Parser_AST.Var l ->
          let topt =
            FStarC_Syntax_DsEnv.try_lookup_lid
              (m.env).PulseSyntaxExtension_Env.dsenv l in
          (match topt with
           | FStar_Pervasives_Native.Some
               { FStarC_Syntax_Syntax.n = FStarC_Syntax_Syntax.Tm_name x;
                 FStarC_Syntax_Syntax.pos = uu___;
                 FStarC_Syntax_Syntax.vars = uu___1;
                 FStarC_Syntax_Syntax.hash_code = uu___2;_}
               ->
               FStarC_Compiler_List.tryFind
                 (fun uu___3 ->
                    match uu___3 with
                    | (uu___4, y, uu___5) -> FStarC_Syntax_Syntax.bv_eq x y)
                 m.map
           | uu___ -> FStar_Pervasives_Native.None)
      | uu___ -> FStar_Pervasives_Native.None
let (maybe_clear_curval : menv -> FStarC_Parser_AST.term -> menv) =
  fun m ->
    fun x ->
      let uu___ = resolve_mut m x in
      match uu___ with
      | FStar_Pervasives_Native.None -> m
      | FStar_Pervasives_Native.Some (x1, y, uu___1) ->
          {
            map = ((x1, y, FStar_Pervasives_Native.None) :: (m.map));
            env = (m.env)
          }
let (read : FStarC_Ident.ident -> FStarC_Parser_AST.term) =
  fun x ->
    let range = FStarC_Ident.range_of_id x in
    let level = FStarC_Parser_AST.Un in
    let head =
      {
        FStarC_Parser_AST.tm =
          (FStarC_Parser_AST.Var PulseSyntaxExtension_Env.op_bang_lid);
        FStarC_Parser_AST.range = range;
        FStarC_Parser_AST.level = level
      } in
    let arg =
      let uu___ =
        let uu___1 = FStarC_Ident.lid_of_ids [x] in
        FStarC_Parser_AST.Var uu___1 in
      {
        FStarC_Parser_AST.tm = uu___;
        FStarC_Parser_AST.range = range;
        FStarC_Parser_AST.level = level
      } in
    {
      FStarC_Parser_AST.tm =
        (FStarC_Parser_AST.App (head, arg, FStarC_Parser_AST.Nothing));
      FStarC_Parser_AST.range = range;
      FStarC_Parser_AST.level = level
    }
let (add_derefs_in_scope :
  needs_derefs ->
    PulseSyntaxExtension_Sugar.stmt -> PulseSyntaxExtension_Sugar.stmt)
  =
  fun n ->
    fun p ->
      FStarC_Compiler_List.fold_right
        (fun uu___ ->
           fun p1 ->
             match uu___ with
             | (x, y) ->
                 let lb =
                   let pat =
                     let uu___1 = FStarC_Ident.range_of_id y in
                     FStarC_Parser_AST.mk_pattern
                       (FStarC_Parser_AST.PatVar
                          (y, FStar_Pervasives_Native.None, [])) uu___1 in
                   let uu___1 =
                     let uu___2 =
                       let uu___3 =
                         let uu___4 =
                           let uu___5 = read x in
                           PulseSyntaxExtension_Sugar.Default_initializer
                             uu___5 in
                         FStar_Pervasives_Native.Some uu___4 in
                       {
                         PulseSyntaxExtension_Sugar.qualifier =
                           FStar_Pervasives_Native.None;
                         PulseSyntaxExtension_Sugar.pat = pat;
                         PulseSyntaxExtension_Sugar.typ =
                           FStar_Pervasives_Native.None;
                         PulseSyntaxExtension_Sugar.init1 = uu___3
                       } in
                     PulseSyntaxExtension_Sugar.LetBinding uu___2 in
                   {
                     PulseSyntaxExtension_Sugar.s = uu___1;
                     PulseSyntaxExtension_Sugar.range1 =
                       (p1.PulseSyntaxExtension_Sugar.range1)
                   } in
                 {
                   PulseSyntaxExtension_Sugar.s =
                     (PulseSyntaxExtension_Sugar.Sequence
                        {
                          PulseSyntaxExtension_Sugar.s1 = lb;
                          PulseSyntaxExtension_Sugar.s2 = p1
                        });
                   PulseSyntaxExtension_Sugar.range1 =
                     (p1.PulseSyntaxExtension_Sugar.range1)
                 }) n p
let (term'_of_id : FStarC_Ident.ident -> FStarC_Parser_AST.term') =
  fun y ->
    let uu___ = FStarC_Ident.lid_of_ids [y] in FStarC_Parser_AST.Var uu___
let rec (transform_term :
  menv ->
    FStarC_Parser_AST.term ->
      (FStarC_Parser_AST.term * needs_derefs * menv)
        PulseSyntaxExtension_Err.err)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun m ->
         fun e ->
           match e.FStarC_Parser_AST.tm with
           | FStarC_Parser_AST.Var uu___ ->
               Obj.magic
                 (Obj.repr
                    (let uu___1 = resolve_mut m e in
                     match uu___1 with
                     | FStar_Pervasives_Native.None ->
                         Obj.repr
                           (PulseSyntaxExtension_Err.return (e, [], m))
                     | FStar_Pervasives_Native.Some
                         (x, uu___2, FStar_Pervasives_Native.None) ->
                         Obj.repr
                           (let uu___3 = fresh_var x in
                            FStarC_Class_Monad.op_let_Bang
                              PulseSyntaxExtension_Err.err_monad () ()
                              (Obj.magic uu___3)
                              (fun uu___4 ->
                                 (fun y ->
                                    let y = Obj.magic y in
                                    let uu___4 =
                                      let uu___5 =
                                        let uu___6 =
                                          let uu___7 =
                                            FStarC_Ident.lid_of_ids [y] in
                                          FStarC_Parser_AST.Var uu___7 in
                                        {
                                          FStarC_Parser_AST.tm = uu___6;
                                          FStarC_Parser_AST.range =
                                            (e.FStarC_Parser_AST.range);
                                          FStarC_Parser_AST.level =
                                            (e.FStarC_Parser_AST.level)
                                        } in
                                      let uu___6 = bind_curval m x y in
                                      (uu___5, [(x, y)], uu___6) in
                                    Obj.magic
                                      (PulseSyntaxExtension_Err.return uu___4))
                                   uu___4))
                     | FStar_Pervasives_Native.Some
                         (uu___2, uu___3, FStar_Pervasives_Native.Some y) ->
                         Obj.repr
                           (let uu___4 =
                              let uu___5 =
                                let uu___6 =
                                  let uu___7 = FStarC_Ident.lid_of_ids [y] in
                                  FStarC_Parser_AST.Var uu___7 in
                                {
                                  FStarC_Parser_AST.tm = uu___6;
                                  FStarC_Parser_AST.range =
                                    (e.FStarC_Parser_AST.range);
                                  FStarC_Parser_AST.level =
                                    (e.FStarC_Parser_AST.level)
                                } in
                              (uu___5, [], m) in
                            PulseSyntaxExtension_Err.return uu___4)))
           | FStarC_Parser_AST.Op (id, tms) ->
               Obj.magic
                 (Obj.repr
                    (let uu___ =
                       Obj.magic
                         (FStarC_Class_Monad.foldM_left
                            PulseSyntaxExtension_Err.err_monad () ()
                            (fun uu___2 ->
                               fun uu___1 ->
                                 (fun uu___1 ->
                                    let uu___1 = Obj.magic uu___1 in
                                    fun tm ->
                                      let tm = Obj.magic tm in
                                      match uu___1 with
                                      | (tms1, needs, m1) ->
                                          let uu___2 = transform_term m1 tm in
                                          Obj.magic
                                            (FStarC_Class_Monad.op_let_Bang
                                               PulseSyntaxExtension_Err.err_monad
                                               () () (Obj.magic uu___2)
                                               (fun uu___3 ->
                                                  (fun uu___3 ->
                                                     let uu___3 =
                                                       Obj.magic uu___3 in
                                                     match uu___3 with
                                                     | (tm1, needs', m') ->
                                                         Obj.magic
                                                           (PulseSyntaxExtension_Err.return
                                                              ((tm1 :: tms1),
                                                                (FStar_List_Tot_Base.op_At
                                                                   needs
                                                                   needs'),
                                                                m'))) uu___3)))
                                   uu___2 uu___1) (Obj.magic ([], [], m))
                            (Obj.magic tms)) in
                     FStarC_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             let uu___1 = Obj.magic uu___1 in
                             match uu___1 with
                             | (tms1, needs, m1) ->
                                 let e1 =
                                   {
                                     FStarC_Parser_AST.tm =
                                       (FStarC_Parser_AST.Op
                                          (id,
                                            (FStarC_Compiler_List.rev tms1)));
                                     FStarC_Parser_AST.range =
                                       (e.FStarC_Parser_AST.range);
                                     FStarC_Parser_AST.level =
                                       (e.FStarC_Parser_AST.level)
                                   } in
                                 Obj.magic
                                   (PulseSyntaxExtension_Err.return
                                      (e1, needs, m1))) uu___1)))
           | FStarC_Parser_AST.App (head, arg, imp) ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = transform_term m head in
                     FStarC_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             let uu___1 = Obj.magic uu___1 in
                             match uu___1 with
                             | (head1, needs, m1) ->
                                 let uu___2 = transform_term m1 arg in
                                 Obj.magic
                                   (FStarC_Class_Monad.op_let_Bang
                                      PulseSyntaxExtension_Err.err_monad ()
                                      () (Obj.magic uu___2)
                                      (fun uu___3 ->
                                         (fun uu___3 ->
                                            let uu___3 = Obj.magic uu___3 in
                                            match uu___3 with
                                            | (arg1, needs', m2) ->
                                                let e1 =
                                                  {
                                                    FStarC_Parser_AST.tm =
                                                      (FStarC_Parser_AST.App
                                                         (head1, arg1, imp));
                                                    FStarC_Parser_AST.range =
                                                      (e.FStarC_Parser_AST.range);
                                                    FStarC_Parser_AST.level =
                                                      (e.FStarC_Parser_AST.level)
                                                  } in
                                                Obj.magic
                                                  (PulseSyntaxExtension_Err.return
                                                     (e1,
                                                       (FStar_List_Tot_Base.op_At
                                                          needs needs'), m2)))
                                           uu___3))) uu___1)))
           | FStarC_Parser_AST.Ascribed (e1, t, topt, b) ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = transform_term m e1 in
                     FStarC_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             let uu___1 = Obj.magic uu___1 in
                             match uu___1 with
                             | (e2, needs, m1) ->
                                 let e3 =
                                   {
                                     FStarC_Parser_AST.tm =
                                       (FStarC_Parser_AST.Ascribed
                                          (e2, t, topt, b));
                                     FStarC_Parser_AST.range =
                                       (e2.FStarC_Parser_AST.range);
                                     FStarC_Parser_AST.level =
                                       (e2.FStarC_Parser_AST.level)
                                   } in
                                 Obj.magic
                                   (PulseSyntaxExtension_Err.return
                                      (e3, needs, m1))) uu___1)))
           | FStarC_Parser_AST.Paren e1 ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = transform_term m e1 in
                     FStarC_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             let uu___1 = Obj.magic uu___1 in
                             match uu___1 with
                             | (e2, needs, m1) ->
                                 let e3 =
                                   {
                                     FStarC_Parser_AST.tm =
                                       (FStarC_Parser_AST.Paren e2);
                                     FStarC_Parser_AST.range =
                                       (e2.FStarC_Parser_AST.range);
                                     FStarC_Parser_AST.level =
                                       (e2.FStarC_Parser_AST.level)
                                   } in
                                 Obj.magic
                                   (PulseSyntaxExtension_Err.return
                                      (e3, needs, m1))) uu___1)))
           | FStarC_Parser_AST.Construct (lid, tms) ->
               Obj.magic
                 (Obj.repr
                    (let uu___ =
                       Obj.magic
                         (FStarC_Class_Monad.foldM_left
                            PulseSyntaxExtension_Err.err_monad () ()
                            (fun uu___2 ->
                               fun uu___1 ->
                                 (fun uu___1 ->
                                    let uu___1 = Obj.magic uu___1 in
                                    fun uu___2 ->
                                      let uu___2 = Obj.magic uu___2 in
                                      match (uu___1, uu___2) with
                                      | ((tms1, needs, m1), (tm, imp)) ->
                                          let uu___3 = transform_term m1 tm in
                                          Obj.magic
                                            (FStarC_Class_Monad.op_let_Bang
                                               PulseSyntaxExtension_Err.err_monad
                                               () () (Obj.magic uu___3)
                                               (fun uu___4 ->
                                                  (fun uu___4 ->
                                                     let uu___4 =
                                                       Obj.magic uu___4 in
                                                     match uu___4 with
                                                     | (tm1, needs', m') ->
                                                         Obj.magic
                                                           (PulseSyntaxExtension_Err.return
                                                              (((tm1, imp) ::
                                                                tms1),
                                                                (FStar_List_Tot_Base.op_At
                                                                   needs
                                                                   needs'),
                                                                m'))) uu___4)))
                                   uu___2 uu___1) (Obj.magic ([], [], m))
                            (Obj.magic tms)) in
                     FStarC_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             let uu___1 = Obj.magic uu___1 in
                             match uu___1 with
                             | (tms1, needs, m1) ->
                                 let e1 =
                                   {
                                     FStarC_Parser_AST.tm =
                                       (FStarC_Parser_AST.Construct
                                          (lid,
                                            (FStarC_Compiler_List.rev tms1)));
                                     FStarC_Parser_AST.range =
                                       (e.FStarC_Parser_AST.range);
                                     FStarC_Parser_AST.level =
                                       (e.FStarC_Parser_AST.level)
                                   } in
                                 Obj.magic
                                   (PulseSyntaxExtension_Err.return
                                      (e1, needs, m1))) uu___1)))
           | FStarC_Parser_AST.LetOpen (l, t) ->
               Obj.magic
                 (Obj.repr
                    (let m1 = menv_push_ns m l in
                     let uu___ = transform_term m1 t in
                     FStarC_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             let uu___1 = Obj.magic uu___1 in
                             match uu___1 with
                             | (p, needs, uu___2) ->
                                 let uu___3 =
                                   let uu___4 = bind_curvals m1 needs in
                                   (p, needs, uu___4) in
                                 Obj.magic
                                   (PulseSyntaxExtension_Err.return uu___3))
                            uu___1)))
           | uu___ ->
               Obj.magic
                 (Obj.repr (PulseSyntaxExtension_Err.return (e, [], m))))
        uu___1 uu___
let rec (transform_stmt_with_reads :
  menv ->
    PulseSyntaxExtension_Sugar.stmt ->
      (PulseSyntaxExtension_Sugar.stmt * needs_derefs * menv)
        PulseSyntaxExtension_Err.err)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun m ->
         fun p ->
           match p.PulseSyntaxExtension_Sugar.s with
           | PulseSyntaxExtension_Sugar.Sequence
               { PulseSyntaxExtension_Sugar.s1 = s1;
                 PulseSyntaxExtension_Sugar.s2 = s2;_}
               ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = transform_stmt_with_reads m s1 in
                     FStarC_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             let uu___1 = Obj.magic uu___1 in
                             match uu___1 with
                             | (s11, needs, m1) ->
                                 let uu___2 = transform_stmt m1 s2 in
                                 Obj.magic
                                   (FStarC_Class_Monad.op_let_Bang
                                      PulseSyntaxExtension_Err.err_monad ()
                                      () (Obj.magic uu___2)
                                      (fun uu___3 ->
                                         (fun s21 ->
                                            let s21 = Obj.magic s21 in
                                            let p1 =
                                              {
                                                PulseSyntaxExtension_Sugar.s
                                                  =
                                                  (PulseSyntaxExtension_Sugar.Sequence
                                                     {
                                                       PulseSyntaxExtension_Sugar.s1
                                                         = s11;
                                                       PulseSyntaxExtension_Sugar.s2
                                                         = s21
                                                     });
                                                PulseSyntaxExtension_Sugar.range1
                                                  =
                                                  (p.PulseSyntaxExtension_Sugar.range1)
                                              } in
                                            Obj.magic
                                              (PulseSyntaxExtension_Err.return
                                                 (p1, needs, m1))) uu___3)))
                            uu___1)))
           | PulseSyntaxExtension_Sugar.Open l ->
               Obj.magic
                 (Obj.repr
                    (let uu___ =
                       let uu___1 = menv_push_ns m l in (p, [], uu___1) in
                     PulseSyntaxExtension_Err.return uu___))
           | PulseSyntaxExtension_Sugar.Expr
               { PulseSyntaxExtension_Sugar.e = e;_} ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = transform_term m e in
                     FStarC_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             let uu___1 = Obj.magic uu___1 in
                             match uu___1 with
                             | (e1, needs, uu___2) ->
                                 let p1 =
                                   {
                                     PulseSyntaxExtension_Sugar.s =
                                       (PulseSyntaxExtension_Sugar.Expr
                                          { PulseSyntaxExtension_Sugar.e = e1
                                          });
                                     PulseSyntaxExtension_Sugar.range1 =
                                       (p.PulseSyntaxExtension_Sugar.range1)
                                   } in
                                 Obj.magic
                                   (PulseSyntaxExtension_Err.return
                                      (p1, needs, m))) uu___1)))
           | PulseSyntaxExtension_Sugar.Assignment
               { PulseSyntaxExtension_Sugar.lhs = lhs;
                 PulseSyntaxExtension_Sugar.value = value;_}
               ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = transform_term m value in
                     FStarC_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             let uu___1 = Obj.magic uu___1 in
                             match uu___1 with
                             | (value1, needs, m1) ->
                                 let m2 = maybe_clear_curval m1 lhs in
                                 let s1 =
                                   {
                                     PulseSyntaxExtension_Sugar.s =
                                       (PulseSyntaxExtension_Sugar.Assignment
                                          {
                                            PulseSyntaxExtension_Sugar.lhs =
                                              lhs;
                                            PulseSyntaxExtension_Sugar.value
                                              = value1
                                          });
                                     PulseSyntaxExtension_Sugar.range1 =
                                       (p.PulseSyntaxExtension_Sugar.range1)
                                   } in
                                 Obj.magic
                                   (PulseSyntaxExtension_Err.return
                                      (s1, needs, m2))) uu___1)))
           | PulseSyntaxExtension_Sugar.ArrayAssignment
               { PulseSyntaxExtension_Sugar.arr = arr;
                 PulseSyntaxExtension_Sugar.index = index;
                 PulseSyntaxExtension_Sugar.value1 = value;_}
               ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = transform_term m arr in
                     FStarC_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             let uu___1 = Obj.magic uu___1 in
                             match uu___1 with
                             | (arr1, arr_needs, m1) ->
                                 let uu___2 = transform_term m1 index in
                                 Obj.magic
                                   (FStarC_Class_Monad.op_let_Bang
                                      PulseSyntaxExtension_Err.err_monad ()
                                      () (Obj.magic uu___2)
                                      (fun uu___3 ->
                                         (fun uu___3 ->
                                            let uu___3 = Obj.magic uu___3 in
                                            match uu___3 with
                                            | (index1, index_needs, m2) ->
                                                let uu___4 =
                                                  transform_term m2 value in
                                                Obj.magic
                                                  (FStarC_Class_Monad.op_let_Bang
                                                     PulseSyntaxExtension_Err.err_monad
                                                     () () (Obj.magic uu___4)
                                                     (fun uu___5 ->
                                                        (fun uu___5 ->
                                                           let uu___5 =
                                                             Obj.magic uu___5 in
                                                           match uu___5 with
                                                           | (value1,
                                                              value_needs,
                                                              m3) ->
                                                               let p1 =
                                                                 {
                                                                   PulseSyntaxExtension_Sugar.s
                                                                    =
                                                                    (PulseSyntaxExtension_Sugar.ArrayAssignment
                                                                    {
                                                                    PulseSyntaxExtension_Sugar.arr
                                                                    = arr1;
                                                                    PulseSyntaxExtension_Sugar.index
                                                                    = index1;
                                                                    PulseSyntaxExtension_Sugar.value1
                                                                    = value1
                                                                    });
                                                                   PulseSyntaxExtension_Sugar.range1
                                                                    =
                                                                    (p.PulseSyntaxExtension_Sugar.range1)
                                                                 } in
                                                               Obj.magic
                                                                 (PulseSyntaxExtension_Err.return
                                                                    (p1,
                                                                    (FStar_List_Tot_Base.op_At
                                                                    arr_needs
                                                                    (FStar_List_Tot_Base.op_At
                                                                    index_needs
                                                                    value_needs)),
                                                                    m3)))
                                                          uu___5))) uu___3)))
                            uu___1)))
           | PulseSyntaxExtension_Sugar.LetBinding
               { PulseSyntaxExtension_Sugar.qualifier = qualifier;
                 PulseSyntaxExtension_Sugar.pat = pat;
                 PulseSyntaxExtension_Sugar.typ = typ;
                 PulseSyntaxExtension_Sugar.init1 = init;_}
               ->
               Obj.magic
                 (Obj.repr
                    (let uu___ =
                       match init with
                       | FStar_Pervasives_Native.None ->
                           Obj.magic
                             (Obj.repr
                                (PulseSyntaxExtension_Err.return
                                   (FStar_Pervasives_Native.None, [], m)))
                       | FStar_Pervasives_Native.Some
                           (PulseSyntaxExtension_Sugar.Default_initializer e)
                           ->
                           Obj.magic
                             (Obj.repr
                                (let mk_init e1 =
                                   FStar_Pervasives_Native.Some
                                     (PulseSyntaxExtension_Sugar.Default_initializer
                                        e1) in
                                 match e.FStarC_Parser_AST.tm with
                                 | FStarC_Parser_AST.Var zlid ->
                                     Obj.repr
                                       (let uu___1 =
                                          let uu___2 =
                                            FStarC_Ident.ids_of_lid zlid in
                                          (qualifier, uu___2) in
                                        match uu___1 with
                                        | (FStar_Pervasives_Native.None,
                                           z::[]) ->
                                            Obj.repr
                                              (let uu___2 = resolve_mut m e in
                                               match uu___2 with
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   PulseSyntaxExtension_Err.return
                                                     ((mk_init e), [], m)
                                               | FStar_Pervasives_Native.Some
                                                   (uu___3, uu___4,
                                                    FStar_Pervasives_Native.Some
                                                    y)
                                                   ->
                                                   let uu___5 =
                                                     let uu___6 =
                                                       let uu___7 =
                                                         let uu___8 =
                                                           term'_of_id y in
                                                         {
                                                           FStarC_Parser_AST.tm
                                                             = uu___8;
                                                           FStarC_Parser_AST.range
                                                             =
                                                             (e.FStarC_Parser_AST.range);
                                                           FStarC_Parser_AST.level
                                                             =
                                                             (e.FStarC_Parser_AST.level)
                                                         } in
                                                       mk_init uu___7 in
                                                     (uu___6, [], m) in
                                                   PulseSyntaxExtension_Err.return
                                                     uu___5
                                               | FStar_Pervasives_Native.Some
                                                   (x, uu___3,
                                                    FStar_Pervasives_Native.None)
                                                   ->
                                                   let uu___4 =
                                                     let uu___5 =
                                                       let uu___6 = read x in
                                                       mk_init uu___6 in
                                                     let uu___6 =
                                                       bind_curval m x z in
                                                     (uu___5, [], uu___6) in
                                                   PulseSyntaxExtension_Err.return
                                                     uu___4)
                                        | uu___2 ->
                                            Obj.repr
                                              (let uu___3 =
                                                 transform_term m e in
                                               FStarC_Class_Monad.op_let_Bang
                                                 PulseSyntaxExtension_Err.err_monad
                                                 () () (Obj.magic uu___3)
                                                 (fun uu___4 ->
                                                    (fun uu___4 ->
                                                       let uu___4 =
                                                         Obj.magic uu___4 in
                                                       match uu___4 with
                                                       | (init1, needs, m1)
                                                           ->
                                                           Obj.magic
                                                             (PulseSyntaxExtension_Err.return
                                                                ((mk_init
                                                                    init1),
                                                                  needs, m1)))
                                                      uu___4)))
                                 | uu___1 ->
                                     Obj.repr
                                       (let uu___2 = transform_term m e in
                                        FStarC_Class_Monad.op_let_Bang
                                          PulseSyntaxExtension_Err.err_monad
                                          () () (Obj.magic uu___2)
                                          (fun uu___3 ->
                                             (fun uu___3 ->
                                                let uu___3 = Obj.magic uu___3 in
                                                match uu___3 with
                                                | (init1, needs, m1) ->
                                                    Obj.magic
                                                      (PulseSyntaxExtension_Err.return
                                                         ((mk_init init1),
                                                           needs, m1)))
                                               uu___3))))
                       | FStar_Pervasives_Native.Some
                           (PulseSyntaxExtension_Sugar.Array_initializer
                           { PulseSyntaxExtension_Sugar.init = init1;
                             PulseSyntaxExtension_Sugar.len = len;_})
                           ->
                           Obj.magic
                             (Obj.repr
                                (let uu___1 = transform_term m init1 in
                                 FStarC_Class_Monad.op_let_Bang
                                   PulseSyntaxExtension_Err.err_monad () ()
                                   (Obj.magic uu___1)
                                   (fun uu___2 ->
                                      (fun uu___2 ->
                                         let uu___2 = Obj.magic uu___2 in
                                         match uu___2 with
                                         | (init2, needs, m1) ->
                                             let uu___3 =
                                               transform_term m1 len in
                                             Obj.magic
                                               (FStarC_Class_Monad.op_let_Bang
                                                  PulseSyntaxExtension_Err.err_monad
                                                  () () (Obj.magic uu___3)
                                                  (fun uu___4 ->
                                                     (fun uu___4 ->
                                                        let uu___4 =
                                                          Obj.magic uu___4 in
                                                        match uu___4 with
                                                        | (len1, len_needs,
                                                           m2) ->
                                                            Obj.magic
                                                              (PulseSyntaxExtension_Err.return
                                                                 ((FStar_Pervasives_Native.Some
                                                                    (PulseSyntaxExtension_Sugar.Array_initializer
                                                                    {
                                                                    PulseSyntaxExtension_Sugar.init
                                                                    = init2;
                                                                    PulseSyntaxExtension_Sugar.len
                                                                    = len1
                                                                    })),
                                                                   (FStar_List_Tot_Base.op_At
                                                                    needs
                                                                    len_needs),
                                                                   m2)))
                                                       uu___4))) uu___2)))
                       | FStar_Pervasives_Native.Some
                           (PulseSyntaxExtension_Sugar.Lambda_initializer
                           { PulseSyntaxExtension_Sugar.id1 = uu___1;
                             PulseSyntaxExtension_Sugar.is_rec = uu___2;
                             PulseSyntaxExtension_Sugar.binders2 = uu___3;
                             PulseSyntaxExtension_Sugar.ascription1 = uu___4;
                             PulseSyntaxExtension_Sugar.measure = uu___5;
                             PulseSyntaxExtension_Sugar.body3 = uu___6;
                             PulseSyntaxExtension_Sugar.decorations = uu___7;
                             PulseSyntaxExtension_Sugar.range3 = range;_})
                           ->
                           Obj.magic
                             (Obj.repr
                                (PulseSyntaxExtension_Err.fail
                                   "Lambdas are not yet supported" range)) in
                     FStarC_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             let uu___1 = Obj.magic uu___1 in
                             match uu___1 with
                             | (init1, needs, m1) ->
                                 let auto_deref_applicable =
                                   match init1 with
                                   | FStar_Pervasives_Native.Some
                                       (PulseSyntaxExtension_Sugar.Array_initializer
                                       uu___2) -> false
                                   | uu___2 -> true in
                                 let uu___2 =
                                   PulseSyntaxExtension_Env.pat_vars pat in
                                 Obj.magic
                                   (FStarC_Class_Monad.op_let_Bang
                                      PulseSyntaxExtension_Err.err_monad ()
                                      () (Obj.magic uu___2)
                                      (fun uu___3 ->
                                         (fun vs ->
                                            let vs = Obj.magic vs in
                                            let m2 =
                                              FStarC_Compiler_List.fold_left
                                                (fun m3 ->
                                                   fun v ->
                                                     menv_push_bv m3 v
                                                       qualifier
                                                       auto_deref_applicable)
                                                m1 vs in
                                            let p1 =
                                              {
                                                PulseSyntaxExtension_Sugar.s
                                                  =
                                                  (PulseSyntaxExtension_Sugar.LetBinding
                                                     {
                                                       PulseSyntaxExtension_Sugar.qualifier
                                                         = qualifier;
                                                       PulseSyntaxExtension_Sugar.pat
                                                         = pat;
                                                       PulseSyntaxExtension_Sugar.typ
                                                         = typ;
                                                       PulseSyntaxExtension_Sugar.init1
                                                         = init1
                                                     });
                                                PulseSyntaxExtension_Sugar.range1
                                                  =
                                                  (p.PulseSyntaxExtension_Sugar.range1)
                                              } in
                                            Obj.magic
                                              (PulseSyntaxExtension_Err.return
                                                 (p1, needs, m2))) uu___3)))
                            uu___1)))
           | PulseSyntaxExtension_Sugar.Block
               { PulseSyntaxExtension_Sugar.stmt = stmt;_} ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = transform_stmt m stmt in
                     FStarC_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun stmt1 ->
                             let stmt1 = Obj.magic stmt1 in
                             let p1 =
                               {
                                 PulseSyntaxExtension_Sugar.s =
                                   (PulseSyntaxExtension_Sugar.Block
                                      {
                                        PulseSyntaxExtension_Sugar.stmt =
                                          stmt1
                                      });
                                 PulseSyntaxExtension_Sugar.range1 =
                                   (p.PulseSyntaxExtension_Sugar.range1)
                               } in
                             Obj.magic
                               (PulseSyntaxExtension_Err.return (p1, [], m)))
                            uu___1)))
           | PulseSyntaxExtension_Sugar.If
               { PulseSyntaxExtension_Sugar.head = head;
                 PulseSyntaxExtension_Sugar.join_slprop = join_slprop;
                 PulseSyntaxExtension_Sugar.then_ = then_;
                 PulseSyntaxExtension_Sugar.else_opt = else_opt;_}
               ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = transform_term m head in
                     FStarC_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             let uu___1 = Obj.magic uu___1 in
                             match uu___1 with
                             | (head1, needs, m1) ->
                                 let uu___2 = transform_stmt m1 then_ in
                                 Obj.magic
                                   (FStarC_Class_Monad.op_let_Bang
                                      PulseSyntaxExtension_Err.err_monad ()
                                      () (Obj.magic uu___2)
                                      (fun uu___3 ->
                                         (fun then_1 ->
                                            let then_1 = Obj.magic then_1 in
                                            let uu___3 =
                                              match else_opt with
                                              | FStar_Pervasives_Native.None
                                                  ->
                                                  Obj.magic
                                                    (Obj.repr
                                                       (PulseSyntaxExtension_Err.return
                                                          FStar_Pervasives_Native.None))
                                              | FStar_Pervasives_Native.Some
                                                  else_ ->
                                                  Obj.magic
                                                    (Obj.repr
                                                       (let uu___4 =
                                                          transform_stmt m1
                                                            else_ in
                                                        FStarC_Class_Monad.op_let_Bang
                                                          PulseSyntaxExtension_Err.err_monad
                                                          () ()
                                                          (Obj.magic uu___4)
                                                          (fun uu___5 ->
                                                             (fun else_1 ->
                                                                let else_1 =
                                                                  Obj.magic
                                                                    else_1 in
                                                                Obj.magic
                                                                  (PulseSyntaxExtension_Err.return
                                                                    (FStar_Pervasives_Native.Some
                                                                    else_1)))
                                                               uu___5))) in
                                            Obj.magic
                                              (FStarC_Class_Monad.op_let_Bang
                                                 PulseSyntaxExtension_Err.err_monad
                                                 () () (Obj.magic uu___3)
                                                 (fun uu___4 ->
                                                    (fun else_opt1 ->
                                                       let else_opt1 =
                                                         Obj.magic else_opt1 in
                                                       let p1 =
                                                         {
                                                           PulseSyntaxExtension_Sugar.s
                                                             =
                                                             (PulseSyntaxExtension_Sugar.If
                                                                {
                                                                  PulseSyntaxExtension_Sugar.head
                                                                    = head1;
                                                                  PulseSyntaxExtension_Sugar.join_slprop
                                                                    =
                                                                    join_slprop;
                                                                  PulseSyntaxExtension_Sugar.then_
                                                                    = then_1;
                                                                  PulseSyntaxExtension_Sugar.else_opt
                                                                    =
                                                                    else_opt1
                                                                });
                                                           PulseSyntaxExtension_Sugar.range1
                                                             =
                                                             (p.PulseSyntaxExtension_Sugar.range1)
                                                         } in
                                                       Obj.magic
                                                         (PulseSyntaxExtension_Err.return
                                                            (p1, needs, m1)))
                                                      uu___4))) uu___3)))
                            uu___1)))
           | PulseSyntaxExtension_Sugar.Match
               { PulseSyntaxExtension_Sugar.head1 = head;
                 PulseSyntaxExtension_Sugar.returns_annot = returns_annot;
                 PulseSyntaxExtension_Sugar.branches = branches;_}
               ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = transform_term m head in
                     FStarC_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             let uu___1 = Obj.magic uu___1 in
                             match uu___1 with
                             | (head1, needs, m1) ->
                                 let uu___2 =
                                   Obj.magic
                                     (FStarC_Class_Monad.mapM
                                        PulseSyntaxExtension_Err.err_monad ()
                                        ()
                                        (fun uu___3 ->
                                           (fun uu___3 ->
                                              let uu___3 = Obj.magic uu___3 in
                                              match uu___3 with
                                              | (p1, s) ->
                                                  let uu___4 =
                                                    PulseSyntaxExtension_Env.pat_vars
                                                      p1 in
                                                  Obj.magic
                                                    (FStarC_Class_Monad.op_let_Bang
                                                       PulseSyntaxExtension_Err.err_monad
                                                       () ()
                                                       (Obj.magic uu___4)
                                                       (fun uu___5 ->
                                                          (fun vs ->
                                                             let vs =
                                                               Obj.magic vs in
                                                             let m2 =
                                                               menv_push_bvs
                                                                 m1 vs in
                                                             let uu___5 =
                                                               transform_stmt
                                                                 m2 s in
                                                             Obj.magic
                                                               (FStarC_Class_Monad.op_let_Bang
                                                                  PulseSyntaxExtension_Err.err_monad
                                                                  () ()
                                                                  (Obj.magic
                                                                    uu___5)
                                                                  (fun uu___6
                                                                    ->
                                                                    (fun s1
                                                                    ->
                                                                    let s1 =
                                                                    Obj.magic
                                                                    s1 in
                                                                    Obj.magic
                                                                    (PulseSyntaxExtension_Err.return
                                                                    (p1, s1)))
                                                                    uu___6)))
                                                            uu___5))) uu___3)
                                        (Obj.magic branches)) in
                                 Obj.magic
                                   (FStarC_Class_Monad.op_let_Bang
                                      PulseSyntaxExtension_Err.err_monad ()
                                      () (Obj.magic uu___2)
                                      (fun uu___3 ->
                                         (fun branches1 ->
                                            let branches1 =
                                              Obj.magic branches1 in
                                            let p1 =
                                              {
                                                PulseSyntaxExtension_Sugar.s
                                                  =
                                                  (PulseSyntaxExtension_Sugar.Match
                                                     {
                                                       PulseSyntaxExtension_Sugar.head1
                                                         = head1;
                                                       PulseSyntaxExtension_Sugar.returns_annot
                                                         = returns_annot;
                                                       PulseSyntaxExtension_Sugar.branches
                                                         = branches1
                                                     });
                                                PulseSyntaxExtension_Sugar.range1
                                                  =
                                                  (p.PulseSyntaxExtension_Sugar.range1)
                                              } in
                                            Obj.magic
                                              (PulseSyntaxExtension_Err.return
                                                 (p1, needs, m1))) uu___3)))
                            uu___1)))
           | PulseSyntaxExtension_Sugar.While
               { PulseSyntaxExtension_Sugar.guard = guard;
                 PulseSyntaxExtension_Sugar.id = id;
                 PulseSyntaxExtension_Sugar.invariant = invariant;
                 PulseSyntaxExtension_Sugar.body = body;_}
               ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = transform_stmt m guard in
                     FStarC_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun guard1 ->
                             let guard1 = Obj.magic guard1 in
                             let uu___1 = transform_stmt m body in
                             Obj.magic
                               (FStarC_Class_Monad.op_let_Bang
                                  PulseSyntaxExtension_Err.err_monad () ()
                                  (Obj.magic uu___1)
                                  (fun uu___2 ->
                                     (fun body1 ->
                                        let body1 = Obj.magic body1 in
                                        let p1 =
                                          {
                                            PulseSyntaxExtension_Sugar.s =
                                              (PulseSyntaxExtension_Sugar.While
                                                 {
                                                   PulseSyntaxExtension_Sugar.guard
                                                     = guard1;
                                                   PulseSyntaxExtension_Sugar.id
                                                     = id;
                                                   PulseSyntaxExtension_Sugar.invariant
                                                     = invariant;
                                                   PulseSyntaxExtension_Sugar.body
                                                     = body1
                                                 });
                                            PulseSyntaxExtension_Sugar.range1
                                              =
                                              (p.PulseSyntaxExtension_Sugar.range1)
                                          } in
                                        Obj.magic
                                          (PulseSyntaxExtension_Err.return
                                             (p1, [], m))) uu___2))) uu___1)))
           | PulseSyntaxExtension_Sugar.Parallel
               { PulseSyntaxExtension_Sugar.p1 = p1;
                 PulseSyntaxExtension_Sugar.p2 = p2;
                 PulseSyntaxExtension_Sugar.q1 = q1;
                 PulseSyntaxExtension_Sugar.q2 = q2;
                 PulseSyntaxExtension_Sugar.b1 = b1;
                 PulseSyntaxExtension_Sugar.b2 = b2;_}
               ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = transform_stmt m b1 in
                     FStarC_Class_Monad.op_let_Bang
                       PulseSyntaxExtension_Err.err_monad () ()
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun b11 ->
                             let b11 = Obj.magic b11 in
                             let uu___1 = transform_stmt m b2 in
                             Obj.magic
                               (FStarC_Class_Monad.op_let_Bang
                                  PulseSyntaxExtension_Err.err_monad () ()
                                  (Obj.magic uu___1)
                                  (fun uu___2 ->
                                     (fun b21 ->
                                        let b21 = Obj.magic b21 in
                                        let p3 =
                                          {
                                            PulseSyntaxExtension_Sugar.s =
                                              (PulseSyntaxExtension_Sugar.Parallel
                                                 {
                                                   PulseSyntaxExtension_Sugar.p1
                                                     = p1;
                                                   PulseSyntaxExtension_Sugar.p2
                                                     = p2;
                                                   PulseSyntaxExtension_Sugar.q1
                                                     = q1;
                                                   PulseSyntaxExtension_Sugar.q2
                                                     = q2;
                                                   PulseSyntaxExtension_Sugar.b1
                                                     = b11;
                                                   PulseSyntaxExtension_Sugar.b2
                                                     = b21
                                                 });
                                            PulseSyntaxExtension_Sugar.range1
                                              =
                                              (p.PulseSyntaxExtension_Sugar.range1)
                                          } in
                                        Obj.magic
                                          (PulseSyntaxExtension_Err.return
                                             (p3, [], m))) uu___2))) uu___1)))
           | PulseSyntaxExtension_Sugar.Introduce uu___ ->
               Obj.magic
                 (Obj.repr (PulseSyntaxExtension_Err.return (p, [], m)))
           | PulseSyntaxExtension_Sugar.ProofHintWithBinders uu___ ->
               Obj.magic
                 (Obj.repr (PulseSyntaxExtension_Err.return (p, [], m))))
        uu___1 uu___
and (transform_stmt :
  menv ->
    PulseSyntaxExtension_Sugar.stmt ->
      PulseSyntaxExtension_Sugar.stmt PulseSyntaxExtension_Err.err)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun m ->
         fun p ->
           let uu___ = transform_stmt_with_reads m p in
           Obj.magic
             (FStarC_Class_Monad.op_let_Bang
                PulseSyntaxExtension_Err.err_monad () () (Obj.magic uu___)
                (fun uu___1 ->
                   (fun uu___1 ->
                      let uu___1 = Obj.magic uu___1 in
                      match uu___1 with
                      | (p1, needs, m1) ->
                          let uu___2 = add_derefs_in_scope needs p1 in
                          Obj.magic (PulseSyntaxExtension_Err.return uu___2))
                     uu___1))) uu___1 uu___
let (transform :
  PulseSyntaxExtension_Env.env_t ->
    PulseSyntaxExtension_Sugar.stmt ->
      PulseSyntaxExtension_Sugar.stmt PulseSyntaxExtension_Err.err)
  = fun e -> fun p -> transform_stmt { map = []; env = e } p