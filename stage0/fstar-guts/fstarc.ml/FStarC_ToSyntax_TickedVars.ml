open Prims
let ident_is_ticked (id : FStarC_Ident.ident) : Prims.bool=
  let nm = FStarC_Ident.string_of_id id in
  ((FStarC_String.length nm) > Prims.int_zero) &&
    (let uu___ = FStarC_String.get nm Prims.int_zero in uu___ = 39)
let lident_is_ticked (id : FStarC_Ident.lident) : Prims.bool=
  let ns = FStarC_Ident.ns_of_lid id in
  let id1 = FStarC_Ident.ident_of_lid id in
  (Prims.uu___is_Nil ns) && (ident_is_ticked id1)
let uu___0 : FStarC_Ident.ident FStarC_RBSet.t FStarC_Class_Monoid.monoid=
  let uu___ =
    Obj.magic
      (FStarC_Class_Setlike.empty ()
         (Obj.magic
            (FStarC_RBSet.setlike_rbset FStarC_Syntax_Syntax.ord_ident)) ()) in
  {
    FStarC_Class_Monoid.mzero = uu___;
    FStarC_Class_Monoid.mplus =
      (fun uu___2 uu___1 ->
         (Obj.magic
            (FStarC_Class_Setlike.union ()
               (Obj.magic
                  (FStarC_RBSet.setlike_rbset FStarC_Syntax_Syntax.ord_ident))))
           uu___2 uu___1)
  }
type 'a m =
  (FStarC_Ident.ident FStarC_RBSet.t, Obj.t, 'a) FStarC_Writer.writer
let emit1 (x : FStarC_Ident.ident) : unit m=
  let uu___ =
    Obj.magic
      (FStarC_Class_Setlike.singleton ()
         (Obj.magic
            (FStarC_RBSet.setlike_rbset FStarC_Syntax_Syntax.ord_ident)) x) in
  FStarC_Writer.emit uu___0 uu___
let rec go_term (env : FStarC_Syntax_DsEnv.env) (t : FStarC_Parser_AST.term)
  : unit m=
  match t.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.Paren t1 -> go_term env t1
  | FStarC_Parser_AST.Labeled uu___ ->
      failwith "Impossible --- labeled source term"
  | FStarC_Parser_AST.Var a ->
      let uu___ =
        (lident_is_ticked a) &&
          (let uu___1 =
             let uu___2 = FStarC_Ident.ident_of_lid a in
             FStarC_Syntax_DsEnv.try_lookup_id env uu___2 in
           FStar_Pervasives_Native.uu___is_None uu___1) in
      if uu___
      then let uu___1 = FStarC_Ident.ident_of_lid a in emit1 uu___1
      else
        FStarC_Class_Monad.return (FStarC_Writer.monad_writer uu___0) ()
          (Obj.repr ())
  | FStarC_Parser_AST.Var x ->
      FStarC_Class_Monad.return (FStarC_Writer.monad_writer uu___0) ()
        (Obj.repr ())
  | FStarC_Parser_AST.Wild ->
      FStarC_Class_Monad.return (FStarC_Writer.monad_writer uu___0) ()
        (Obj.repr ())
  | FStarC_Parser_AST.Const uu___ ->
      FStarC_Class_Monad.return (FStarC_Writer.monad_writer uu___0) ()
        (Obj.repr ())
  | FStarC_Parser_AST.Uvar uu___ ->
      FStarC_Class_Monad.return (FStarC_Writer.monad_writer uu___0) ()
        (Obj.repr ())
  | FStarC_Parser_AST.Projector uu___ ->
      FStarC_Class_Monad.return (FStarC_Writer.monad_writer uu___0) ()
        (Obj.repr ())
  | FStarC_Parser_AST.Discrim uu___ ->
      FStarC_Class_Monad.return (FStarC_Writer.monad_writer uu___0) ()
        (Obj.repr ())
  | FStarC_Parser_AST.Name uu___ ->
      FStarC_Class_Monad.return (FStarC_Writer.monad_writer uu___0) ()
        (Obj.repr ())
  | FStarC_Parser_AST.Requires t1 -> go_term env t1
  | FStarC_Parser_AST.Ensures t1 -> go_term env t1
  | FStarC_Parser_AST.Decreases t1 -> go_term env t1
  | FStarC_Parser_AST.NamedTyp (uu___, t1) -> go_term env t1
  | FStarC_Parser_AST.LexList l ->
      FStarC_Class_Monad.iterM (FStarC_Writer.monad_writer uu___0) ()
        (fun uu___ -> (Obj.magic (go_term env)) uu___) (Obj.magic l)
  | FStarC_Parser_AST.WFOrder (rel, e) ->
      let uu___ = go_term env rel in
      FStarC_Class_Monad.op_let_Bang (FStarC_Writer.monad_writer uu___0) ()
        () uu___
        (fun uu___1 ->
           (fun uu___1 ->
              let uu___1 = Obj.magic uu___1 in Obj.magic (go_term env e))
             uu___1)
  | FStarC_Parser_AST.Paren t1 -> failwith "impossible"
  | FStarC_Parser_AST.Ascribed (t1, t', tacopt, uu___) ->
      let uu___1 = go_term env t1 in
      FStarC_Class_Monad.op_let_Bang (FStarC_Writer.monad_writer uu___0) ()
        () uu___1
        (fun uu___2 ->
           (fun uu___2 ->
              let uu___2 = Obj.magic uu___2 in
              let uu___3 = go_term env t' in
              Obj.magic
                (FStarC_Class_Monad.op_let_Bang
                   (FStarC_Writer.monad_writer uu___0) () () uu___3
                   (fun uu___4 ->
                      (fun uu___4 ->
                         let uu___4 = Obj.magic uu___4 in
                         match tacopt with
                         | FStar_Pervasives_Native.None ->
                             Obj.magic
                               (FStarC_Class_Monad.return
                                  (FStarC_Writer.monad_writer uu___0) ()
                                  (Obj.repr ()))
                         | FStar_Pervasives_Native.Some tac ->
                             Obj.magic (go_term env tac)) uu___4))) uu___2)
  | FStarC_Parser_AST.Construct (uu___, ts) ->
      FStarC_Class_Monad.iterM (FStarC_Writer.monad_writer uu___0) ()
        (fun uu___1 ->
           (fun uu___1 ->
              let uu___1 = Obj.magic uu___1 in
              match uu___1 with | (a, uu___2) -> Obj.magic (go_term env a))
             uu___1) (Obj.magic ts)
  | FStarC_Parser_AST.Op (uu___, ts) ->
      FStarC_Class_Monad.iterM (FStarC_Writer.monad_writer uu___0) ()
        (fun uu___1 -> (Obj.magic (go_term env)) uu___1) (Obj.magic ts)
  | FStarC_Parser_AST.App (t1, t2, uu___) ->
      let uu___1 = go_term env t1 in
      FStarC_Class_Monad.op_let_Bang (FStarC_Writer.monad_writer uu___0) ()
        () uu___1
        (fun uu___2 ->
           (fun uu___2 ->
              let uu___2 = Obj.magic uu___2 in Obj.magic (go_term env t2))
             uu___2)
  | FStarC_Parser_AST.Refine (b, t1) ->
      let uu___ = go_binder env b in
      FStarC_Class_Monad.op_let_Bang (FStarC_Writer.monad_writer uu___0) ()
        () (Obj.magic uu___)
        (fun uu___1 ->
           (fun env' ->
              let env' = Obj.magic env' in Obj.magic (go_term env' t1))
             uu___1)
  | FStarC_Parser_AST.Sum (binders, body) ->
      let uu___ =
        Obj.magic
          (FStarC_Class_Monad.foldM_left (FStarC_Writer.monad_writer uu___0)
             () ()
             (fun uu___2 uu___1 ->
                (fun env1 ->
                   let env1 = Obj.magic env1 in
                   fun bt ->
                     let bt = Obj.magic bt in
                     match bt with
                     | FStar_Pervasives.Inl binder ->
                         Obj.magic (Obj.repr (go_binder env1 binder))
                     | FStar_Pervasives.Inr t1 ->
                         Obj.magic
                           (Obj.repr
                              (let uu___1 = go_term env1 t1 in
                               FStarC_Class_Monad.op_let_Bang
                                 (FStarC_Writer.monad_writer uu___0) () ()
                                 uu___1
                                 (fun uu___2 ->
                                    (fun uu___2 ->
                                       let uu___2 = Obj.magic uu___2 in
                                       Obj.magic
                                         (FStarC_Class_Monad.return
                                            (FStarC_Writer.monad_writer
                                               uu___0) () (Obj.magic env1)))
                                      uu___2)))) uu___2 uu___1)
             (Obj.magic env) (Obj.magic binders)) in
      FStarC_Class_Monad.op_let_Bang (FStarC_Writer.monad_writer uu___0) ()
        () (Obj.magic uu___)
        (fun uu___1 ->
           (fun env' ->
              let env' = Obj.magic env' in Obj.magic (go_term env' body))
             uu___1)
  | FStarC_Parser_AST.Product (binders, body) ->
      let uu___ =
        Obj.magic
          (FStarC_Class_Monad.foldM_left (FStarC_Writer.monad_writer uu___0)
             () () (fun uu___2 uu___1 -> (Obj.magic go_binder) uu___2 uu___1)
             (Obj.magic env) (Obj.magic binders)) in
      FStarC_Class_Monad.op_let_Bang (FStarC_Writer.monad_writer uu___0) ()
        () (Obj.magic uu___)
        (fun uu___1 ->
           (fun env' ->
              let env' = Obj.magic env' in Obj.magic (go_term env' body))
             uu___1)
  | FStarC_Parser_AST.Project (t1, uu___) -> go_term env t1
  | FStarC_Parser_AST.Attributes cattributes ->
      FStarC_Class_Monad.iterM (FStarC_Writer.monad_writer uu___0) ()
        (fun uu___ -> (Obj.magic (go_term env)) uu___)
        (Obj.magic cattributes)
  | FStarC_Parser_AST.CalcProof (rel, init, steps) ->
      let uu___ = go_term env rel in
      FStarC_Class_Monad.op_let_Bang (FStarC_Writer.monad_writer uu___0) ()
        () uu___
        (fun uu___1 ->
           (fun uu___1 ->
              let uu___1 = Obj.magic uu___1 in
              let uu___2 = go_term env init in
              Obj.magic
                (FStarC_Class_Monad.op_let_Bang
                   (FStarC_Writer.monad_writer uu___0) () () uu___2
                   (fun uu___3 ->
                      (fun uu___3 ->
                         let uu___3 = Obj.magic uu___3 in
                         Obj.magic
                           (FStarC_Class_Monad.iterM
                              (FStarC_Writer.monad_writer uu___0) ()
                              (fun uu___4 ->
                                 (fun uu___4 ->
                                    let uu___4 = Obj.magic uu___4 in
                                    match uu___4 with
                                    | FStarC_Parser_AST.CalcStep
                                        (rel1, just, next) ->
                                        let uu___5 = go_term env rel1 in
                                        Obj.magic
                                          (FStarC_Class_Monad.op_let_Bang
                                             (FStarC_Writer.monad_writer
                                                uu___0) () () uu___5
                                             (fun uu___6 ->
                                                (fun uu___6 ->
                                                   let uu___6 =
                                                     Obj.magic uu___6 in
                                                   let uu___7 =
                                                     go_term env just in
                                                   Obj.magic
                                                     (FStarC_Class_Monad.op_let_Bang
                                                        (FStarC_Writer.monad_writer
                                                           uu___0) () ()
                                                        uu___7
                                                        (fun uu___8 ->
                                                           (fun uu___8 ->
                                                              let uu___8 =
                                                                Obj.magic
                                                                  uu___8 in
                                                              Obj.magic
                                                                (go_term env
                                                                   next))
                                                             uu___8))) uu___6)))
                                   uu___4) (Obj.magic steps))) uu___3)))
             uu___1)
  | FStarC_Parser_AST.ElimForall (bs, t1, ts) ->
      let uu___ = go_binders env bs in
      FStarC_Class_Monad.op_let_Bang (FStarC_Writer.monad_writer uu___0) ()
        () (Obj.magic uu___)
        (fun uu___1 ->
           (fun env' ->
              let env' = Obj.magic env' in
              let uu___1 = go_term env' t1 in
              Obj.magic
                (FStarC_Class_Monad.op_let_Bang
                   (FStarC_Writer.monad_writer uu___0) () () uu___1
                   (fun uu___2 ->
                      (fun uu___2 ->
                         let uu___2 = Obj.magic uu___2 in
                         Obj.magic
                           (FStarC_Class_Monad.iterM
                              (FStarC_Writer.monad_writer uu___0) ()
                              (fun uu___3 ->
                                 (Obj.magic (go_term env')) uu___3)
                              (Obj.magic ts))) uu___2))) uu___1)
  | FStarC_Parser_AST.ElimExists (binders, p, q, y, e) ->
      let uu___ = go_term env q in
      FStarC_Class_Monad.op_let_Bang (FStarC_Writer.monad_writer uu___0) ()
        () uu___
        (fun uu___1 ->
           (fun uu___1 ->
              let uu___1 = Obj.magic uu___1 in
              let uu___2 = go_binders env binders in
              Obj.magic
                (FStarC_Class_Monad.op_let_Bang
                   (FStarC_Writer.monad_writer uu___0) () ()
                   (Obj.magic uu___2)
                   (fun uu___3 ->
                      (fun env' ->
                         let env' = Obj.magic env' in
                         let uu___3 = go_term env' p in
                         Obj.magic
                           (FStarC_Class_Monad.op_let_Bang
                              (FStarC_Writer.monad_writer uu___0) () ()
                              uu___3
                              (fun uu___4 ->
                                 (fun uu___4 ->
                                    let uu___4 = Obj.magic uu___4 in
                                    let uu___5 = go_binder env' y in
                                    Obj.magic
                                      (FStarC_Class_Monad.op_let_Bang
                                         (FStarC_Writer.monad_writer uu___0)
                                         () () (Obj.magic uu___5)
                                         (fun uu___6 ->
                                            (fun env'' ->
                                               let env'' = Obj.magic env'' in
                                               Obj.magic (go_term env'' e))
                                              uu___6))) uu___4))) uu___3)))
             uu___1)
  | FStarC_Parser_AST.ElimImplies (p, q, e) ->
      let uu___ = go_term env p in
      FStarC_Class_Monad.op_let_Bang (FStarC_Writer.monad_writer uu___0) ()
        () uu___
        (fun uu___1 ->
           (fun uu___1 ->
              let uu___1 = Obj.magic uu___1 in
              let uu___2 = go_term env q in
              Obj.magic
                (FStarC_Class_Monad.op_let_Bang
                   (FStarC_Writer.monad_writer uu___0) () () uu___2
                   (fun uu___3 ->
                      (fun uu___3 ->
                         let uu___3 = Obj.magic uu___3 in
                         Obj.magic (go_term env e)) uu___3))) uu___1)
  | FStarC_Parser_AST.ElimOr (p, q, r, x, e, x', e') ->
      let uu___ = go_term env p in
      FStarC_Class_Monad.op_let_Bang (FStarC_Writer.monad_writer uu___0) ()
        () uu___
        (fun uu___1 ->
           (fun uu___1 ->
              let uu___1 = Obj.magic uu___1 in
              let uu___2 = go_term env q in
              Obj.magic
                (FStarC_Class_Monad.op_let_Bang
                   (FStarC_Writer.monad_writer uu___0) () () uu___2
                   (fun uu___3 ->
                      (fun uu___3 ->
                         let uu___3 = Obj.magic uu___3 in
                         let uu___4 = go_term env r in
                         Obj.magic
                           (FStarC_Class_Monad.op_let_Bang
                              (FStarC_Writer.monad_writer uu___0) () ()
                              uu___4
                              (fun uu___5 ->
                                 (fun uu___5 ->
                                    let uu___5 = Obj.magic uu___5 in
                                    let uu___6 = go_binder env x in
                                    Obj.magic
                                      (FStarC_Class_Monad.op_let_Bang
                                         (FStarC_Writer.monad_writer uu___0)
                                         () () (Obj.magic uu___6)
                                         (fun uu___7 ->
                                            (fun env_x ->
                                               let env_x = Obj.magic env_x in
                                               let uu___7 = go_term env_x e in
                                               Obj.magic
                                                 (FStarC_Class_Monad.op_let_Bang
                                                    (FStarC_Writer.monad_writer
                                                       uu___0) () () uu___7
                                                    (fun uu___8 ->
                                                       (fun uu___8 ->
                                                          let uu___8 =
                                                            Obj.magic uu___8 in
                                                          let uu___9 =
                                                            go_binder env x' in
                                                          Obj.magic
                                                            (FStarC_Class_Monad.op_let_Bang
                                                               (FStarC_Writer.monad_writer
                                                                  uu___0) ()
                                                               ()
                                                               (Obj.magic
                                                                  uu___9)
                                                               (fun uu___10
                                                                  ->
                                                                  (fun env_x'
                                                                    ->
                                                                    let env_x'
                                                                    =
                                                                    Obj.magic
                                                                    env_x' in
                                                                    Obj.magic
                                                                    (go_term
                                                                    env_x' e'))
                                                                    uu___10)))
                                                         uu___8))) uu___7)))
                                   uu___5))) uu___3))) uu___1)
  | FStarC_Parser_AST.ElimAnd (p, q, r, x, y, e) ->
      let uu___ = go_term env p in
      FStarC_Class_Monad.op_let_Bang (FStarC_Writer.monad_writer uu___0) ()
        () uu___
        (fun uu___1 ->
           (fun uu___1 ->
              let uu___1 = Obj.magic uu___1 in
              let uu___2 = go_term env q in
              Obj.magic
                (FStarC_Class_Monad.op_let_Bang
                   (FStarC_Writer.monad_writer uu___0) () () uu___2
                   (fun uu___3 ->
                      (fun uu___3 ->
                         let uu___3 = Obj.magic uu___3 in
                         let uu___4 = go_term env r in
                         Obj.magic
                           (FStarC_Class_Monad.op_let_Bang
                              (FStarC_Writer.monad_writer uu___0) () ()
                              uu___4
                              (fun uu___5 ->
                                 (fun uu___5 ->
                                    let uu___5 = Obj.magic uu___5 in
                                    let uu___6 = go_binders env [x; y] in
                                    Obj.magic
                                      (FStarC_Class_Monad.op_let_Bang
                                         (FStarC_Writer.monad_writer uu___0)
                                         () () (Obj.magic uu___6)
                                         (fun uu___7 ->
                                            (fun env' ->
                                               let env' = Obj.magic env' in
                                               Obj.magic (go_term env' e))
                                              uu___7))) uu___5))) uu___3)))
             uu___1)
  | FStarC_Parser_AST.ListLiteral ts ->
      FStarC_Class_Monad.iterM (FStarC_Writer.monad_writer uu___0) ()
        (fun uu___ -> (Obj.magic (go_term env)) uu___) (Obj.magic ts)
  | FStarC_Parser_AST.SeqLiteral ts ->
      FStarC_Class_Monad.iterM (FStarC_Writer.monad_writer uu___0) ()
        (fun uu___ -> (Obj.magic (go_term env)) uu___) (Obj.magic ts)
  | FStarC_Parser_AST.Abs uu___ ->
      FStarC_Class_Monad.return (FStarC_Writer.monad_writer uu___0) ()
        (Obj.repr ())
  | FStarC_Parser_AST.Function uu___ ->
      FStarC_Class_Monad.return (FStarC_Writer.monad_writer uu___0) ()
        (Obj.repr ())
  | FStarC_Parser_AST.Let uu___ ->
      FStarC_Class_Monad.return (FStarC_Writer.monad_writer uu___0) ()
        (Obj.repr ())
  | FStarC_Parser_AST.LetOpen uu___ ->
      FStarC_Class_Monad.return (FStarC_Writer.monad_writer uu___0) ()
        (Obj.repr ())
  | FStarC_Parser_AST.If uu___ ->
      FStarC_Class_Monad.return (FStarC_Writer.monad_writer uu___0) ()
        (Obj.repr ())
  | FStarC_Parser_AST.QForall uu___ ->
      FStarC_Class_Monad.return (FStarC_Writer.monad_writer uu___0) ()
        (Obj.repr ())
  | FStarC_Parser_AST.QExists uu___ ->
      FStarC_Class_Monad.return (FStarC_Writer.monad_writer uu___0) ()
        (Obj.repr ())
  | FStarC_Parser_AST.QuantOp uu___ ->
      FStarC_Class_Monad.return (FStarC_Writer.monad_writer uu___0) ()
        (Obj.repr ())
  | FStarC_Parser_AST.Record uu___ ->
      FStarC_Class_Monad.return (FStarC_Writer.monad_writer uu___0) ()
        (Obj.repr ())
  | FStarC_Parser_AST.Match uu___ ->
      FStarC_Class_Monad.return (FStarC_Writer.monad_writer uu___0) ()
        (Obj.repr ())
  | FStarC_Parser_AST.TryWith uu___ ->
      FStarC_Class_Monad.return (FStarC_Writer.monad_writer uu___0) ()
        (Obj.repr ())
  | FStarC_Parser_AST.Bind uu___ ->
      FStarC_Class_Monad.return (FStarC_Writer.monad_writer uu___0) ()
        (Obj.repr ())
  | FStarC_Parser_AST.Quote uu___ ->
      FStarC_Class_Monad.return (FStarC_Writer.monad_writer uu___0) ()
        (Obj.repr ())
  | FStarC_Parser_AST.VQuote uu___ ->
      FStarC_Class_Monad.return (FStarC_Writer.monad_writer uu___0) ()
        (Obj.repr ())
  | FStarC_Parser_AST.Antiquote uu___ ->
      FStarC_Class_Monad.return (FStarC_Writer.monad_writer uu___0) ()
        (Obj.repr ())
  | FStarC_Parser_AST.Seq uu___ ->
      FStarC_Class_Monad.return (FStarC_Writer.monad_writer uu___0) ()
        (Obj.repr ())
and go_binder (uu___1 : FStarC_Syntax_DsEnv.env)
  (uu___ : FStarC_Parser_AST.binder) : FStarC_Syntax_DsEnv.env m=
  (fun env b ->
     match b.FStarC_Parser_AST.b with
     | FStarC_Parser_AST.Variable x ->
         let uu___ =
           let uu___1 =
             (ident_is_ticked x) &&
               (let uu___2 = FStarC_Syntax_DsEnv.try_lookup_id env x in
                FStar_Pervasives_Native.uu___is_None uu___2) in
           if uu___1
           then emit1 x
           else
             FStarC_Class_Monad.return (FStarC_Writer.monad_writer uu___0) ()
               (Obj.repr ()) in
         Obj.magic
           (FStarC_Class_Monad.op_let_Bang
              (FStarC_Writer.monad_writer uu___0) () () uu___
              (fun uu___1 ->
                 (fun uu___1 ->
                    let uu___1 = Obj.magic uu___1 in
                    let uu___2 = FStarC_Syntax_DsEnv.push_bv env x in
                    match uu___2 with
                    | (env', uu___3) ->
                        Obj.magic
                          (FStarC_Class_Monad.return
                             (FStarC_Writer.monad_writer uu___0) ()
                             (Obj.magic env'))) uu___1))
     | FStarC_Parser_AST.Annotated (x, t) ->
         let uu___ =
           let uu___1 =
             (ident_is_ticked x) &&
               (let uu___2 = FStarC_Syntax_DsEnv.try_lookup_id env x in
                FStar_Pervasives_Native.uu___is_None uu___2) in
           if uu___1
           then emit1 x
           else
             FStarC_Class_Monad.return (FStarC_Writer.monad_writer uu___0) ()
               (Obj.repr ()) in
         Obj.magic
           (FStarC_Class_Monad.op_let_Bang
              (FStarC_Writer.monad_writer uu___0) () () uu___
              (fun uu___1 ->
                 (fun uu___1 ->
                    let uu___1 = Obj.magic uu___1 in
                    let uu___2 = go_term env t in
                    Obj.magic
                      (FStarC_Class_Monad.op_let_Bang
                         (FStarC_Writer.monad_writer uu___0) () () uu___2
                         (fun uu___3 ->
                            (fun uu___3 ->
                               let uu___3 = Obj.magic uu___3 in
                               let uu___4 = FStarC_Syntax_DsEnv.push_bv env x in
                               match uu___4 with
                               | (env', uu___5) ->
                                   Obj.magic
                                     (FStarC_Class_Monad.return
                                        (FStarC_Writer.monad_writer uu___0)
                                        () (Obj.magic env'))) uu___3)))
                   uu___1))
     | FStarC_Parser_AST.NoName t ->
         let uu___ = go_term env t in
         Obj.magic
           (FStarC_Class_Monad.op_let_Bang
              (FStarC_Writer.monad_writer uu___0) () () uu___
              (fun uu___1 ->
                 (fun uu___1 ->
                    let uu___1 = Obj.magic uu___1 in
                    Obj.magic
                      (FStarC_Class_Monad.return
                         (FStarC_Writer.monad_writer uu___0) ()
                         (Obj.magic env))) uu___1))) uu___1 uu___
and go_binders (uu___1 : FStarC_Syntax_DsEnv.env)
  (uu___ : FStarC_Parser_AST.binder Prims.list) : FStarC_Syntax_DsEnv.env m=
  (fun env bs ->
     Obj.magic
       (FStarC_Class_Monad.foldM_left (FStarC_Writer.monad_writer uu___0) ()
          () (fun uu___1 uu___ -> (Obj.magic go_binder) uu___1 uu___)
          (Obj.magic env) (Obj.magic bs))) uu___1 uu___
let free_ticked_vars (env : FStarC_Syntax_DsEnv.env)
  (t : FStarC_Parser_AST.term) : FStarC_Ident.ident Prims.list=
  let uu___ =
    let uu___1 = go_term env t in
    Obj.magic (FStarC_Writer.run_writer uu___0 () (Obj.magic uu___1)) in
  match uu___ with
  | (fvs, ()) ->
      FStarC_Class_Setlike.elems ()
        (Obj.magic
           (FStarC_RBSet.setlike_rbset FStarC_Syntax_Syntax.ord_ident))
        (Obj.magic fvs)
let rec unparen (t : FStarC_Parser_AST.term) : FStarC_Parser_AST.term=
  match t.FStarC_Parser_AST.tm with
  | FStarC_Parser_AST.Paren t1 -> unparen t1
  | uu___ -> t
let tm_type (r : FStarC_Range_Type.range) : FStarC_Parser_AST.term=
  let uu___ =
    let uu___1 = FStarC_Ident.lid_of_path ["Type"] r in
    FStarC_Parser_AST.Name uu___1 in
  FStarC_Parser_AST.mk_term uu___ r FStarC_Parser_AST.Kind
let close (env : FStarC_Syntax_DsEnv.env) (t : FStarC_Parser_AST.term) :
  FStarC_Parser_AST.term=
  let ftv = free_ticked_vars env t in
  if Prims.uu___is_Nil ftv
  then t
  else
    (let binders =
       FStarC_List.map
         (fun x ->
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 =
                    FStarC_Class_HasRange.pos FStarC_Ident.hasrange_ident x in
                  tm_type uu___4 in
                (x, uu___3) in
              FStarC_Parser_AST.Annotated uu___2 in
            let uu___2 =
              FStarC_Class_HasRange.pos FStarC_Ident.hasrange_ident x in
            FStarC_Parser_AST.mk_binder uu___1 uu___2
              FStarC_Parser_AST.Type_level
              (FStar_Pervasives_Native.Some FStarC_Parser_AST.Implicit)) ftv in
     let result =
       FStarC_Parser_AST.mk_term (FStarC_Parser_AST.Product (binders, t))
         t.FStarC_Parser_AST.range t.FStarC_Parser_AST.level in
     result)
let close_fun (env : FStarC_Syntax_DsEnv.env) (t : FStarC_Parser_AST.term) :
  FStarC_Parser_AST.term=
  let ftv = free_ticked_vars env t in
  if Prims.uu___is_Nil ftv
  then t
  else
    (let binders =
       FStarC_List.map
         (fun x ->
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 =
                    FStarC_Class_HasRange.pos FStarC_Ident.hasrange_ident x in
                  tm_type uu___4 in
                (x, uu___3) in
              FStarC_Parser_AST.Annotated uu___2 in
            let uu___2 =
              FStarC_Class_HasRange.pos FStarC_Ident.hasrange_ident x in
            FStarC_Parser_AST.mk_binder uu___1 uu___2
              FStarC_Parser_AST.Type_level
              (FStar_Pervasives_Native.Some FStarC_Parser_AST.Implicit)) ftv in
     let t1 =
       let uu___1 = let uu___2 = unparen t in uu___2.FStarC_Parser_AST.tm in
       match uu___1 with
       | FStarC_Parser_AST.Product uu___2 -> t
       | uu___2 ->
           let uu___3 =
             let uu___4 =
               let uu___5 =
                 FStarC_Parser_AST.mk_term
                   (FStarC_Parser_AST.Name FStarC_Parser_Const.effect_Tot_lid)
                   t.FStarC_Parser_AST.range t.FStarC_Parser_AST.level in
               (uu___5, t, FStarC_Parser_AST.Nothing) in
             FStarC_Parser_AST.App uu___4 in
           FStarC_Parser_AST.mk_term uu___3 t.FStarC_Parser_AST.range
             t.FStarC_Parser_AST.level in
     let result =
       FStarC_Parser_AST.mk_term (FStarC_Parser_AST.Product (binders, t1))
         t1.FStarC_Parser_AST.range t1.FStarC_Parser_AST.level in
     result)
